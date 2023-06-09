theory Multirelations

imports Power_Allegories_Multirelations

begin

lemma nonempty_set_card:
  assumes "finite S"
  shows "S \<noteq> {} \<longleftrightarrow> card S \<ge> 1"
  using assms card_0_eq by fastforce

no_notation one_class.one ("1")
no_notation times_class.times (infixl "*" 70)

no_notation rel_fdia ("(|_\<rangle>_)" [61,81] 82)
no_notation rel_bdia ("(\<langle>_|_)" [61,81] 82)
no_notation rel_fbox ("(|_]_)" [61,81] 82)
no_notation rel_bbox ("([_|_)" [61,81] 82)

declare s_prod_pa_def [mr_simp]

notation s_prod (infixl "*" 70)
notation s_id ("1")

lemma sp_oi_subdist:
  "(P \<inter> Q) * (R \<inter> S) \<subseteq> P * R"
  unfolding s_prod_def by blast

lemma sp_oi_subdist_2:
  "(P \<inter> Q) * (R \<inter> S) \<subseteq> (P * R) \<inter> (Q * S)"
  unfolding s_prod_def by blast

section \<open>Inner Structure\<close>

subsection \<open>Inner union, inner intersection and inner complement\<close>

abbreviation "inner_union" (infixl "\<union>\<union>" 65)
  where "inner_union \<equiv> p_prod"

definition inner_intersection :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> ('a,'b) mrel" (infixl "\<inter>\<inter>" 65) where
  "R \<inter>\<inter> S \<equiv> { (a,B) . \<exists>C D . B = C \<inter> D \<and> (a,C) \<in> R \<and> (a,D) \<in> S }"

definition inner_complement :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("\<sim> _" [80] 80) where
  "\<sim>R \<equiv> { (a,B) . (a,-B) \<in> R }"

abbreviation "iu_unit" ("1\<^sub>\<union>\<^sub>\<union>")
  where "1\<^sub>\<union>\<^sub>\<union> \<equiv> p_id"

definition ii_unit :: "('a,'a) mrel" ("1\<^sub>\<inter>\<^sub>\<inter>")
  where "1\<^sub>\<inter>\<^sub>\<inter> \<equiv> { (a,UNIV) | a . True }"

declare inner_intersection_def [mr_simp] inner_complement_def [mr_simp] ii_unit_def [mr_simp]

lemma iu_assoc:
  "(R \<union>\<union> S) \<union>\<union> T = R \<union>\<union> (S \<union>\<union> T)"
  by (simp add: p_prod_assoc)

lemma iu_commute:
  "R \<union>\<union> S = S \<union>\<union> R"
  by (simp add: p_prod_comm)

lemma iu_unit:
  "R \<union>\<union> 1\<^sub>\<union>\<^sub>\<union> = R"
  by simp

lemma ii_assoc:
  "(R \<inter>\<inter> S) \<inter>\<inter> T = R \<inter>\<inter> (S \<inter>\<inter> T)"
  apply (clarsimp simp: mr_simp)
  by (metis (no_types, opaque_lifting) semilattice_inf_class.inf_assoc)

lemma ii_commute:
  "R \<inter>\<inter> S = S \<inter>\<inter> R"
  by (auto simp: mr_simp)

lemma ii_unit [simp]:
  "R \<inter>\<inter> 1\<^sub>\<inter>\<^sub>\<inter> = R"
  by (simp add: mr_simp)

lemma pa_ic:
  "\<sim>(R \<otimes> \<sim>S) = R \<otimes> S"
  by (clarsimp simp: mr_simp)

lemma ic_involutive [simp]:
  "\<sim>\<sim>R = R"
  by (simp add: mr_simp)

lemma ic_injective:
  "\<sim>R = \<sim>S \<Longrightarrow> R = S"
  by (metis ic_involutive)

lemma ic_antidist_iu:
  "\<sim>(R \<union>\<union> S) = \<sim>R \<inter>\<inter> \<sim>S"
  apply (clarsimp simp: mr_simp)
  by (metis (no_types, opaque_lifting) compl_sup double_compl)

lemma ic_antidist_ii:
  "\<sim>(R \<inter>\<inter> S) = \<sim>R \<union>\<union> \<sim>S"
  by (metis ic_antidist_iu ic_involutive)

lemma ic_iu_unit [simp]:
  "\<sim>1\<^sub>\<union>\<^sub>\<union> = 1\<^sub>\<inter>\<^sub>\<inter>"
  unfolding ii_unit_def p_id_def inner_complement_def by force

lemma ic_ii_unit [simp]:
  "\<sim>1\<^sub>\<inter>\<^sub>\<inter> = 1\<^sub>\<union>\<^sub>\<union>"
  by (metis ic_involutive ic_iu_unit)

lemma ii_unit_split_iu [simp]:
  "1 \<union>\<union> \<sim>1 = 1\<^sub>\<inter>\<^sub>\<inter>"
  by (force simp: mr_simp)

lemma aux_1:
  "B = {a} \<inter> D \<Longrightarrow> -D = {a} \<Longrightarrow> B = {}"
  by auto

lemma iu_unit_split_ii [simp]:
  "1 \<inter>\<inter> \<sim>1 = 1\<^sub>\<union>\<^sub>\<union>"
  by (metis ic_antidist_iu ic_ii_unit ic_involutive ii_commute ii_unit_split_iu)

lemma iu_right_dist_ou:
  "(R \<union> S) \<union>\<union> T = (R \<union>\<union> T) \<union> (S \<union>\<union> T)"
  unfolding p_prod_def by auto

lemma ii_right_dist_ou:
  "(R \<union> S) \<inter>\<inter> T = (R \<inter>\<inter> T) \<union> (S \<inter>\<inter> T)"
  by (auto simp: mr_simp)

lemma iu_left_isotone:
  "R \<subseteq> S \<Longrightarrow> R \<union>\<union> T \<subseteq> S \<union>\<union> T"
  by (metis iu_right_dist_ou subset_Un_eq)

lemma iu_right_isotone:
  "R \<subseteq> S \<Longrightarrow> T \<union>\<union> R \<subseteq> T \<union>\<union> S"
  by (simp add: iu_commute iu_left_isotone)

lemma iu_isotone:
  "R \<subseteq> S \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> R \<union>\<union> P \<subseteq> S \<union>\<union> Q"
  by (meson dual_order.trans iu_left_isotone iu_right_isotone)

lemma ii_left_isotone:
  "R \<subseteq> S \<Longrightarrow> R \<inter>\<inter> T \<subseteq> S \<inter>\<inter> T"
  by (metis ii_right_dist_ou subset_Un_eq)

lemma ii_right_isotone:
  "R \<subseteq> S \<Longrightarrow> T \<inter>\<inter> R \<subseteq> T \<inter>\<inter> S"
  by (simp add: ii_commute ii_left_isotone)

lemma ii_isotone:
  "R \<subseteq> S \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> R \<inter>\<inter> P \<subseteq> S \<inter>\<inter> Q"
  by (meson ii_left_isotone ii_right_isotone order_trans)

lemma iu_right_subdist_ii:
  "(R \<inter>\<inter> S) \<union>\<union> T \<subseteq> (R \<union>\<union> T) \<inter>\<inter> (S \<union>\<union> T)"
  apply (clarsimp simp: mr_simp)
  by (metis sup_inf_distrib2)

lemma ii_right_subdist_iu:
  "(R \<union>\<union> S) \<inter>\<inter> T \<subseteq> (R \<inter>\<inter> T) \<union>\<union> (S \<inter>\<inter> T)"
  apply (clarsimp simp: mr_simp)
  by (metis inf_sup_distrib2)

lemma ic_isotone:
  "R \<subseteq> S \<Longrightarrow> \<sim>R \<subseteq> \<sim>S"
  by (simp add: inner_complement_def subset_eq)

lemma ic_bot [simp]:
  "\<sim>{} = {}"
  by (simp add: mr_simp)

lemma ic_top [simp]:
  "\<sim>U = U"
  by (auto simp: mr_simp)

lemma ic_dist_ou:
  "\<sim>(R \<union> S) = \<sim>R \<union> \<sim>S"
  by (auto simp: mr_simp)

lemma ic_dist_oi:
  "\<sim>(R \<inter> S) = \<sim>R \<inter> \<sim>S"
  by (auto simp: mr_simp)

lemma ic_dist_oc:
  "\<sim>-R = -(\<sim>R)"
  by (auto simp: mr_simp)

lemma ii_sub_idempotent:
  "R \<subseteq> R \<inter>\<inter> R"
  unfolding inner_intersection_def by force

definition inner_Union :: "('i \<Rightarrow> ('a,'b) mrel) \<Rightarrow> 'i set \<Rightarrow> ('a,'b) mrel" ("\<Union>\<Union>_|_" [80,80] 80) where
  "\<Union>\<Union>X|I \<equiv> { (a,B) . \<exists>f . B = (\<Union>i\<in>I . f i) \<and> (\<forall>i\<in>I . (a,f i) \<in> X i) }"

definition inner_Intersection :: "('i \<Rightarrow> ('a,'b) mrel) \<Rightarrow> 'i set \<Rightarrow> ('a,'b) mrel" ("\<Inter>\<Inter>_|_" [80,80] 80) where
  "\<Inter>\<Inter>X|I \<equiv> { (a,B) . \<exists>f . B = (\<Inter>i\<in>I . f i) \<and> (\<forall>i\<in>I . (a,f i) \<in> X i) }"

declare inner_Union_def [mr_simp] inner_Intersection_def [mr_simp]

lemma iU_empty:
  "\<Union>\<Union>X|{} = 1\<^sub>\<union>\<^sub>\<union>"
  by (auto simp: mr_simp)

lemma iI_empty:
  "\<Inter>\<Inter>X|{} = 1\<^sub>\<inter>\<^sub>\<inter>"
  by (auto simp: mr_simp)

lemma ic_antidist_iU:
  "\<sim>\<Union>\<Union>X|I = \<Inter>\<Inter>(inner_complement o X)|I"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (metis (mono_tags, lifting) Compl_UN double_compl)
  by (clarsimp simp: mr_simp) blast

lemma ic_antidist_iI:
  "\<sim>\<Inter>\<Inter>X|I = \<Union>\<Union>(inner_complement o X)|I"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (metis Compl_INT double_complement)
  by (clarsimp simp: mr_simp) blast

lemma iu_right_dist_oU:
  "\<Union>X \<union>\<union> T = (\<Union>R\<in>X . R \<union>\<union> T)"
  by (clarsimp simp: mr_simp) blast

lemma ii_right_dist_oU:
  "\<Union>X \<inter>\<inter> T = (\<Union>R\<in>X . R \<inter>\<inter> T)"
  by (clarsimp simp: mr_simp) blast

lemma iu_right_subdist_iI:
  "\<Inter>\<Inter>X|I \<union>\<union> T \<subseteq> \<Inter>\<Inter>(\<lambda>i . X i \<union>\<union> T)|I"
  apply (clarsimp simp: mr_simp)
  by (metis INT_simps(6))

lemma ii_right_subdist_iU:
  "\<Union>\<Union>X|I \<inter>\<inter> T \<subseteq> \<Union>\<Union>(\<lambda>i . X i \<inter>\<inter> T)|I"
  by (clarsimp simp: mr_simp, metis UN_extend_simps(4))

lemma ic_dist_oU:
  "\<sim>\<Union>X = \<Union>(inner_complement ` X)"
  by (auto simp: mr_simp)

lemma ic_dist_oI:
  "\<sim>\<Inter>X = \<Inter>(inner_complement ` X)"
  by (auto simp: mr_simp)

lemma sp_left_subdist_iU:
  "R * (\<Union>\<Union>X|I) \<subseteq> \<Union>\<Union>(\<lambda>i . R * X i)|I"
  apply (clarsimp simp: mr_simp)
  subgoal for a B f proof -
    assume 1: "(a,B) \<in> R"
    assume "\<forall>b\<in>B . \<exists>g . f b = \<Union>(g ` I) \<and> (\<forall>i\<in>I . (b,g i) \<in> X i)"
    from this obtain g where 2: "\<forall>b\<in>B . f b = \<Union>(g b ` I) \<and> (\<forall>i\<in>I . (b,g b i) \<in> X i)"
      by metis
    hence 3: "\<Union>(f ` B) = (\<Union>b\<in>B . \<Union>(g b ` I))"
      by (meson SUP_cong)
    let ?h = "\<lambda>i . \<Union>b\<in>B . g b i"
    have "\<Union>(f ` B) = \<Union>(?h ` I) \<and> (\<forall>i\<in>I . \<exists>B . (a,B) \<in> R \<and> (\<exists>f . (\<forall>b\<in>B . (b,f b) \<in> X i) \<and> ?h i = \<Union>(f ` B)))"
      using 1 2 3 by (metis SUP_commute)
    thus ?thesis
      by auto
  qed
  done

lemma sp_right_subdist_iU:
  "(\<Union>\<Union>X|I) * R \<subseteq> \<Union>\<Union>(\<lambda>i . X i * R)|I"
  by (clarsimp simp: mr_simp, blast)

lemma sp_right_dist_iU:
  assumes "\<forall>J::'a set . J \<noteq> {} \<longrightarrow> (\<Union>\<Union>(\<lambda>j . R)|J) \<subseteq> R"
  shows "(\<Union>\<Union>X|I) * R = \<Union>\<Union>(\<lambda>i . X i * R)|(I::'a set)"
  apply (rule antisym)
  using sp_right_subdist_iU apply blast
  apply (clarsimp simp: mr_simp)
  subgoal for a f proof -
    assume "\<forall>i\<in>I . \<exists>B . (a,B) \<in> X i \<and> (\<exists>g . (\<forall>b\<in>B . (b,g b) \<in> R) \<and> f i = \<Union>(g ` B))"
    from this obtain B g where 1: "\<forall>i\<in>I . (a,B i) \<in> X i \<and> (\<forall>b\<in>B i . (b,g i b) \<in> R) \<and> f i = \<Union>(g i ` B i)"
      by metis
    let ?B = "\<Union>(B ` I)"
    let ?g = "\<lambda>b . \<Union>{ g i b | i . i\<in>I \<and> b \<in> B i }"
    have "\<forall>b\<in>?B . (b,?g b) \<in> R"
    proof (rule ballI)
      fix b
      let ?I = "{ i | i . i\<in>I \<and> b \<in> B i }"
      assume 2: "b \<in> \<Union>(B ` I)"
      have "(b,?g b) \<in> \<Union>\<Union>(\<lambda>j . R)|?I"
        apply (clarsimp simp: mr_simp)
        apply (rule exI[of _ "\<lambda>i . g i b"])
        using 1 by blast
      thus "(b,?g b) \<in> R"
        using 2 by (smt (verit) assms UN_E empty_Collect_eq subset_iff)
    qed
    hence "?B = \<Union>(B ` I) \<and> (\<forall>i\<in>I . (a,B i) \<in> X i) \<and> (\<forall>b\<in>?B . (b,?g b) \<in> R) \<and> \<Union>(f ` I) = \<Union>(?g ` ?B)"
      using 1 by auto
    thus "\<exists>B . (\<exists>f . B = \<Union>(f ` I) \<and> (\<forall>i\<in>I . (a,f i) \<in> X i)) \<and> (\<exists>g . (\<forall>b\<in>B . (b,g b) \<in> R) \<and> \<Union>(f ` I) = \<Union>(g ` B))"
      by (metis (no_types, lifting))
  qed
  done

subsection \<open>Dual\<close>

abbreviation dual :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("_\<^sup>d" [100] 100)
  where "R\<^sup>d \<equiv> \<sim>-R"

lemma dual:
  "R\<^sup>d = { (a,B) . (a,-B) \<notin> R }"
  by (simp add: inner_complement_def)

declare dual [mr_simp]

lemma dual_antitone:
  "R \<subseteq> S \<Longrightarrow> S\<^sup>d \<subseteq> R\<^sup>d"
  by (simp add: ic_isotone)

lemma ic_oc_dual:
  "\<sim>R = -R\<^sup>d"
  by (simp add: ic_dist_oc)

lemma dual_involutive [simp]:
  "R\<^sup>d\<^sup>d = R"
  by (simp add: ic_dist_oc)

lemma dual_antidist_ou:
  "(R \<union> S)\<^sup>d = R\<^sup>d \<inter> S\<^sup>d"
  by (simp add: ic_dist_oi)

lemma dual_antidist_oi:
  "(R \<inter> S)\<^sup>d = R\<^sup>d \<union> S\<^sup>d"
  by (simp add: ic_dist_ou)

lemma dual_dist_oc:
  "(-R)\<^sup>d = -R\<^sup>d"
  by (fact ic_dist_oc)

lemma dual_dist_ic:
  "(\<sim>R)\<^sup>d = \<sim>R\<^sup>d"
  by (simp add: ic_dist_oc)

lemma dual_antidist_oU:
  "(\<Union>X)\<^sup>d = \<Inter>(dual ` X)"
  by (simp add: ic_dist_oI uminus_Sup)

lemma dual_antidist_oI:
  "(\<Inter>X)\<^sup>d = \<Union>(dual ` X)"
  by (simp add: ic_dist_oU uminus_Inf)

subsection \<open>Co-composition\<close>

definition co_prod :: "('a,'b) mrel \<Rightarrow> ('b,'c) mrel \<Rightarrow> ('a,'c) mrel" (infixl "\<odot>" 70) where
  "R \<odot> S \<equiv> { (a,C) . \<exists>B . (a,B) \<in> R \<and> (\<exists>f . (\<forall>b \<in> B . (b,f b) \<in> S) \<and> C = \<Inter>{ f b | b . b \<in> B }) }"

lemma co_prod_im:
  "R \<odot> S = { (a,C) . \<exists>B . (a,B) \<in> R \<and> (\<exists>f . (\<forall>b \<in> B . (b,f b) \<in> S) \<and> C = \<Inter>((\<lambda>x . f x) ` B)) }"
  by (auto simp: co_prod_def)

lemma co_prod_iff:
  "(a,C) \<in> (R \<odot> S) \<longleftrightarrow> (\<exists>B . (a,B) \<in> R \<and> (\<exists>f . (\<forall>b \<in> B . (b,f b) \<in> S) \<and> C = \<Inter>{ f b | b . b \<in> B }))"
  by (unfold co_prod_im, auto)

declare co_prod_im [mr_simp]

lemma co_prod:
  "R \<odot> S = \<sim>(R * \<sim>S)"
  apply (clarsimp simp: mr_simp)
  by (smt (verit) Collect_cong Compl_INT Compl_UN case_prodI2 double_complement old.prod.case)

lemma cp_left_isotone:
  "R \<subseteq> S \<Longrightarrow> R \<odot> T \<subseteq> S \<odot> T"
  by (simp add: co_prod ic_isotone s_prod_isol)

lemma cp_right_isotone:
  "R \<subseteq> S \<Longrightarrow> T \<odot> R \<subseteq> T \<odot> S"
  by (smt (verit) co_prod_iff in_mono subrelI)

lemma cp_isotone:
  "R \<subseteq> S \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> R \<odot> P \<subseteq> S \<odot> Q"
  by (meson cp_left_isotone cp_right_isotone order_trans)

lemma ic_dist_cp:
  "\<sim>(R \<odot> S) = R * \<sim>S"
  by (simp add: co_prod)

lemma ic_dist_sp:
  "\<sim>(R * S) = R \<odot> \<sim>S"
  by (simp add: co_prod)

lemma ic_cp_ic_unit:
  "\<sim>R = R \<odot> \<sim>1"
  by (simp add: co_prod)

lemma cp_left_zero [simp]:
  "{} \<odot> R = {}"
  by (simp add: co_prod_im)

lemma cp_left_unit [simp]:
  "1 \<odot> R = R"
  by (simp add: co_prod)

lemma cp_ic_unit [simp]:
  "\<sim>1 \<odot> \<sim>1 = 1"
  using ic_cp_ic_unit ic_involutive by blast

lemma cp_right_dist_ou:
  "(R \<union> S) \<odot> T = (R \<odot> T) \<union> (S \<odot> T)"
  by (simp add: co_prod ic_dist_ou s_prod_distr)

lemma cp_left_iu_unit [simp]:
  "1\<^sub>\<union>\<^sub>\<union> \<odot> R = 1\<^sub>\<inter>\<^sub>\<inter>"
  by (simp add: co_prod)

lemma cp_right_ii_unit:
  "R \<odot> 1\<^sub>\<inter>\<^sub>\<inter> \<subseteq> R \<union>\<union> \<sim>R"
  apply (clarsimp simp: mr_simp)
  by (metis double_compl sup_compl_top)

lemma sp_right_iu_unit:
  "R * 1\<^sub>\<union>\<^sub>\<union> \<subseteq> R \<inter>\<inter> \<sim>R"
  apply (clarsimp simp: mr_simp)
  by (metis Compl_disjoint double_complement)

lemma cp_left_subdist_ii:
  "R \<odot> (S \<inter>\<inter> T) \<subseteq> (R \<odot> S) \<inter>\<inter> (R \<odot> T)"
  by (metis cl3 co_prod ic_antidist_ii ic_antidist_iu ic_isotone)

lemma cp_right_subantidist_iu:
  "(R \<union>\<union> S) \<odot> T \<subseteq> (R \<odot> T) \<inter>\<inter> (S \<odot> T)"
  by (metis co_prod ic_antidist_iu ic_isotone seq_conc_subdistr)

lemma cp_right_antidist_iu:
  assumes "T \<inter>\<inter> T \<subseteq> T"
  shows "(R \<union>\<union> S) \<odot> T = (R \<odot> T) \<inter>\<inter> (S \<odot> T)"
  by (smt (verit) assms cl4 co_prod cp_right_subantidist_iu ic_antidist_ii ic_involutive ic_isotone subset_antisym)

lemma cp_right_dist_oU:
  "\<Union>X \<odot> T = (\<Union>R\<in>X . R \<odot> T)"
  by (auto simp: mr_simp)

lemma cp_left_subdist_iI:
  "R \<odot> (\<Inter>\<Inter>X|I) \<subseteq> \<Inter>\<Inter>(\<lambda>i . R \<odot> X i)|I"
proof -
  have "R \<odot> (\<Inter>\<Inter>X|I) = \<sim>(R * (\<Union>\<Union>(inner_complement o X)|I))"
    by (simp add: co_prod ic_antidist_iI)
  also have "... \<subseteq> \<sim>(\<Union>\<Union>(\<lambda>i . R * \<sim>(X i))|I)"
    apply (rule ic_isotone)
    using sp_left_subdist_iU by force
  also have "... = \<Inter>\<Inter>(\<lambda>i . R \<odot> X i)|I"
    apply (subst ic_antidist_iU)
    by (metis co_prod comp_apply)
  finally show ?thesis
    .
qed

lemma cp_right_subantidist_iU:
  "(\<Union>\<Union>X|I) \<odot> R \<subseteq> \<Inter>\<Inter>(\<lambda>i . X i \<odot> R)|I"
proof -
  have "(\<Union>\<Union>X|I) \<odot> R = \<sim>((\<Union>\<Union>X|I) * \<sim>R)"
    by (simp add: co_prod)
  also have "... \<subseteq> \<sim>((\<Union>\<Union>(\<lambda>i . X i * \<sim>R)|I))"
    by (simp add: ic_isotone sp_right_subdist_iU)
  also have "... = \<Inter>\<Inter>(\<lambda>i . X i \<odot> R)|I"
    apply (subst ic_antidist_iU)
    by (metis co_prod comp_apply)
  finally show ?thesis
    .
qed

lemma cp_right_antidist_iU:
  assumes "\<forall>J::'a set . J \<noteq> {} \<longrightarrow> (\<Inter>\<Inter>(\<lambda>j . R)|J) \<subseteq> R"
  shows "(\<Union>\<Union>X|I) \<odot> R = \<Inter>\<Inter>(\<lambda>i . X i \<odot> R)|(I::'a set)"
proof -
  have 1: "\<And>J . \<Union>\<Union>(\<lambda>j. \<sim> R)|J = \<sim>\<Inter>\<Inter>(\<lambda>j . R)|J"
    apply (subst ic_antidist_iI)
    by (metis comp_apply)
  have "(\<Union>\<Union>X|I) \<odot> R = \<sim>((\<Union>\<Union>X|I) * \<sim>R)"
    by (simp add: co_prod)
  also have "... = \<sim>((\<Union>\<Union>(\<lambda>i . X i * \<sim>R)|I))"
    by (simp add: 1 assms sp_right_dist_iU ic_isotone)
  also have "... = \<Inter>\<Inter>(\<lambda>i . X i \<odot> R)|I"
    apply (subst ic_antidist_iU)
    by (metis co_prod comp_apply)
  finally show ?thesis
    .
qed

subsection \<open>Inner order\<close>

definition inner_order_iu :: "'a \<times> 'b set \<Rightarrow> 'a \<times> 'b set \<Rightarrow> bool" (infix "\<preceq>\<^sub>\<union>\<^sub>\<union>" 50) where
  "x \<preceq>\<^sub>\<union>\<^sub>\<union> y \<equiv> fst x = fst y \<and> snd x \<subseteq> snd y"

definition inner_order_ii :: "'a \<times> 'b set \<Rightarrow> 'a \<times> 'b set \<Rightarrow> bool" (infix "\<preceq>\<^sub>\<inter>\<^sub>\<inter>" 50) where
  "x \<preceq>\<^sub>\<inter>\<^sub>\<inter> y \<equiv> fst x = fst y \<and> snd x \<supseteq> snd y"

lemma inner_order_dual:
  "x \<preceq>\<^sub>\<union>\<^sub>\<union> y \<longleftrightarrow> y \<preceq>\<^sub>\<inter>\<^sub>\<inter> x"
  by (metis inner_order_ii_def inner_order_iu_def)

interpretation inner_order_iu: order "(\<preceq>\<^sub>\<union>\<^sub>\<union>)" "\<lambda>x y . x \<preceq>\<^sub>\<union>\<^sub>\<union> y \<and> x \<noteq> y"
  by (unfold_locales, auto simp add: inner_order_iu_def)

subsection \<open>Up-closure, down-closure and convex-closure\<close>

abbreviation up :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("_\<up>" [100] 100)
  where "R\<up> \<equiv> R \<union>\<union> U"

abbreviation down :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("_\<down>" [100] 100)
  where "R\<down> \<equiv> R \<inter>\<inter> U"

abbreviation convex :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("_\<updown>" [100] 100)
  where "R\<updown> \<equiv> R\<up> \<inter> R\<down>"

lemma up:
  "R\<up> = { (a,B) . \<exists>C . (a,C) \<in> R \<and> C \<subseteq> B }"
  by (simp add: p_id_U)

lemma down:
  "R\<down> = { (a,B) . \<exists>C . (a,C) \<in> R \<and> B \<subseteq> C }"
  by (auto simp: mr_simp)

lemma convex:
  "R\<updown> = { (a,B) . \<exists>C D . (a,C) \<in> R \<and> (a,D) \<in> R \<and> C \<subseteq> B \<and> B \<subseteq> D }"
  by (auto simp: mr_simp)

declare up [mr_simp] down [mr_simp] convex [mr_simp]

lemma ic_up:
  "\<sim>(R\<up>) = (\<sim>R)\<down>"
  by (simp add: ic_antidist_iu)

lemma ic_down:
  "\<sim>(R\<down>) = (\<sim>R)\<up>"
  by (simp add: ic_antidist_ii)

lemma ic_convex:
  "\<sim>(R\<updown>) = (\<sim>R)\<updown>"
  by (simp add: ic_dist_oi ic_down ic_up inf_commute)

lemma up_isotone:
  "R \<subseteq> S \<Longrightarrow> R\<up> \<subseteq> S\<up>"
  by (fact iu_left_isotone)

lemma up_increasing:
  "R \<subseteq> R\<up>"
  by (simp add: upclosed_ext)

lemma up_idempotent [simp]:
  "R\<up>\<up> = R\<up>"
  by (simp add: iu_assoc)

lemma up_dist_ou:
  "(R \<union> S)\<up> = R\<up> \<union> S\<up>"
  by (simp add: iu_right_dist_ou)

lemma up_dist_iu:
  "(R \<union>\<union> S)\<up> = R\<up> \<union>\<union> S\<up>"
  using cv_hom_par p_prod_assoc by blast

lemma up_dist_ii:
  "(R \<inter>\<inter> S)\<up> = R\<up> \<inter>\<inter> S\<up>"
proof (rule antisym)
  show "(R \<inter>\<inter> S)\<up> \<subseteq> R\<up> \<inter>\<inter> S\<up>"
    by (simp add: iu_right_subdist_ii)
next
  have "\<And>a B C D E . (a,B) \<in> R \<Longrightarrow> (a,C) \<in> S \<Longrightarrow> \<exists>F . (\<exists>G . (B \<union> D) \<inter> (C \<union> E) = F \<union> G) \<and> (\<exists>H I . F = H \<inter> I \<and> (a,H) \<in> R \<and> (a,I) \<in> S)"
  proof -
    fix a B C D E
    assume 1: "(a,B) \<in> R"
    assume 2: "(a,C) \<in> S"
    let ?F = "B \<inter> C"
    let ?G = "(B \<inter> E) \<union> (D \<inter> C) \<union> (D \<inter> E)"
    have "(B \<union> D) \<inter> (C \<union> E) = ?F \<union> ?G"
      by auto
    thus "\<exists>F . (\<exists>G . (B \<union> D) \<inter> (C \<union> E) = F \<union> G) \<and> (\<exists>H I . F = H \<inter> I \<and> (a,H) \<in> R \<and> (a,I) \<in> S)"
      using 1 2 by auto
  qed
  thus "R\<up> \<inter>\<inter> S\<up> \<subseteq> (R \<inter>\<inter> S)\<up>"
    by (clarsimp simp: mr_simp)
qed

lemma down_isotone:
  "R \<subseteq> S \<Longrightarrow> R\<down> \<subseteq> S\<down>"
  by (fact ii_left_isotone)

lemma down_increasing:
  "R \<subseteq> R\<down>"
  by (metis ic_involutive ic_isotone ic_up up_increasing)

lemma down_idempotent [simp]:
  "R\<down>\<down> = R\<down>"
  by (simp add: ic_down ic_injective)

lemma down_dist_ou:
  "(R \<union> S)\<down> = R\<down> \<union> S\<down>"
  by (fact ii_right_dist_ou)

lemma down_dist_iu:
  "(R \<union>\<union> S)\<down> = R\<down> \<union>\<union> S\<down>"
  by (simp add: ic_antidist_ii ic_antidist_iu ic_injective up_dist_ii)

lemma down_dist_ii:
  "(R \<inter>\<inter> S)\<down> = R\<down> \<inter>\<inter> S\<down>"
  by (metis down_idempotent ii_assoc ii_commute)

lemma convex_isotone:
  "R \<subseteq> S \<Longrightarrow> R\<updown> \<subseteq> S\<updown>"
  by (meson Int_mono down_isotone up_isotone)

lemma convex_increasing:
  "R \<subseteq> R\<updown>"
  by (simp add: down_increasing up_increasing)

lemma convex_idempotent [simp]:
  "R\<updown>\<updown> = R\<updown>"
  by (smt (verit, ccfv_threshold) U_par_idem convex_increasing convex_isotone ic_top ic_up ii_assoc iu_assoc le_inf_iff subsetI subset_antisym)

lemma down_sp:
  "R\<down> = R * (1\<^sub>\<union>\<^sub>\<union> \<union> 1)"
proof -
  have "\<forall>a B . (\<exists>C . (\<exists>D . B = C \<inter> D) \<and> (a,C) \<in> R) \<longleftrightarrow> (\<exists>C . (a,C) \<in> R \<and> (\<exists>f . (\<forall>c\<in>C . f c = {} \<or> f c = {c}) \<and> B = (\<Union>c\<in>C . f c)))"
  proof (intro allI, rule iffI)
    fix a B
    assume "\<exists>C . (\<exists>D . B = C \<inter> D) \<and> (a,C) \<in> R"
    from this obtain C where 1: "\<exists>D . B = C \<inter> D" and 2: "(a,C) \<in> R"
      by auto
    let ?f = "\<lambda>c . if c \<in> B then {c} else {}"
    have "(\<Union>c\<in>C . ?f c) = (\<Union>c\<in>B . ?f c) \<union> (\<Union>c\<in>C\<inter>-B . ?f c)"
      using 1 by blast
    hence 3: "B = (\<Union>c\<in>C . ?f c)"
      by auto
    have "\<forall>c\<in>C . ?f c = {} \<or> ?f c = {c}"
      by auto
    thus "\<exists>C . (a,C) \<in> R \<and> (\<exists>f . (\<forall>c\<in>C . f c = {} \<or> f c = {c}) \<and> B = (\<Union>c\<in>C . f c))"
      using 2 3 by smt
  next
    fix a B
    assume "\<exists>C . (a,C) \<in> R \<and> (\<exists>f . (\<forall>c\<in>C . f c = {} \<or> f c = {c}) \<and> B = (\<Union>c\<in>C . f c))"
    from this obtain C where 4: "(a,C) \<in> R" and "\<exists>f . (\<forall>c\<in>C . f c = {} \<or> f c = {c}) \<and> B = (\<Union>c\<in>C . f c)"
      by auto
    hence "B \<subseteq> C"
      by auto
    thus "\<exists>C . (\<exists>D . B = C \<inter> D) \<and> (a,C) \<in> R"
      using 4 by auto
  qed
  thus ?thesis
    by (clarsimp simp: mr_simp)
qed

lemma up_cp:
  "R\<up> = \<sim>R \<odot> (1\<^sub>\<inter>\<^sub>\<inter> \<union> \<sim>1)"
  by (metis co_prod down_sp ic_dist_ou ic_ii_unit ic_involutive ic_up)

lemma down_dist_sp:
  "(R * S)\<down> = R * S\<down>"
proof (rule antisym)
  show "(R * S)\<down> \<subseteq> R * S\<down>"
    by (simp add: down_sp s_prod_assoc1)
next
  have "\<And>a B f . (a,B) \<in> R \<Longrightarrow> \<forall>b\<in>B . \<exists>C . (\<exists>D . f b = C \<inter> D) \<and> (b,C) \<in> S \<Longrightarrow> \<exists>E . (\<exists>F . (\<Union>b\<in>B . f b) = E \<inter> F) \<and> (\<exists>B . (a,B) \<in> R \<and> (\<exists>g . (\<forall>b\<in>B . (b,g b) \<in> S) \<and> E = (\<Union>b\<in>B . g b)))"
  proof -
    fix a B f
    assume 1: "(a,B) \<in> R"
    assume "\<forall>b\<in>B . \<exists>C . (\<exists>D . f b = C \<inter> D) \<and> (b,C) \<in> S"
    hence "\<exists>g . \<forall>b\<in>B . (\<exists>D . f b = g b \<inter> D) \<and> (b,g b) \<in> S"
      by metis
    from this obtain g where 2: "\<forall>b\<in>B . (\<exists>D . f b = g b \<inter> D) \<and> (b,g b) \<in> S"
      by auto
    hence "(\<Union>b\<in>B . f b) \<subseteq> (\<Union>b\<in>B . g b)"
      by blast
    thus "\<exists>E . (\<exists>F . (\<Union>b\<in>B . f b) = E \<inter> F) \<and> (\<exists>B . (a,B) \<in> R \<and> (\<exists>g . (\<forall>b\<in>B . (b,g b) \<in> S) \<and> E = (\<Union>b\<in>B . g b)))"
      using 1 2 by (metis semilattice_inf_class.inf.absorb_iff2)
  qed
  thus "R * S\<down> \<subseteq> (R * S)\<down>"
    by (clarsimp simp: mr_simp)
qed

lemma up_dist_cp:
  "(R \<odot> S)\<up> = R \<odot> S\<up>"
  by (metis co_prod down_dist_sp ic_down ic_up)

lemma iu_up_oi:
  "R\<up> \<union>\<union> S\<up> = R\<up> \<inter> S\<up>"
  by (fact up_closed_par_is_meet)

lemma ii_down_oi:
  "R\<down> \<inter>\<inter> S\<down> = R\<down> \<inter> S\<down>"
  by (metis ic_antidist_ii ic_dist_oi ic_down ic_involutive up_closed_par_is_meet)

lemma down_dist_ii_oi:
  "R\<down> \<inter> S\<down> = (R \<inter>\<inter> S)\<down>"
  by (simp add: down_dist_ii ii_down_oi)

lemma up_dist_iu_oi:
  "R\<up> \<inter> S\<up> = (R \<union>\<union> S)\<up>"
  by (simp add: up_closed_par_is_meet up_dist_iu)

lemma oi_down_sub_up:
  "R\<down> \<inter> S\<up> \<subseteq> (R\<down> \<inter> S)\<up>"
  by (auto simp: mr_simp)

lemma oi_down_up:
  "R\<down> \<inter> S = {} \<Longrightarrow> R \<inter> S\<up> = {}"
  by (metis (no_types, lifting) cp_left_zero down_increasing ic_bot inf.orderE inf_assoc inf_bot_right oi_down_sub_up up_cp)

lemma oi_down_up_iff:
  "R\<down> \<inter> S = {} \<longleftrightarrow> R \<inter> S\<up> = {}"
proof (rule iffI)
  show "R\<down> \<inter> S = {} \<Longrightarrow> R \<inter> S\<up> = {}"
    by (simp add: oi_down_up)
next
  assume 1: "R \<inter> S\<up> = {}"
  have "(\<sim>S)\<down> = \<sim>(S\<up>)"
    by (metis (no_types) ic_down ic_involutive)
  hence "\<sim>(R\<down> \<inter> S) = {}"
    using 1 by (metis Int_commute ic_bot ic_dist_oi ic_down oi_down_up)
  thus "R\<down> \<inter> S = {}"
    by (metis (no_types) ic_bot ic_involutive)
qed

lemma down_double_complement_up:
  "R\<down> \<subseteq> S \<longleftrightarrow> R \<subseteq> -((-S)\<up>)"
  by (metis disjoint_eq_subset_Compl double_compl oi_down_up_iff)

lemma up_double_complement_down:
  "R\<up> \<subseteq> S \<longleftrightarrow> R \<subseteq> -((-S)\<down>)"
  by (metis Compl_subset_Compl_iff double_compl down_double_complement_up)

lemma below_up_oi_down:
  "R \<subseteq> R\<up> \<inter> R\<down>"
  by (fact convex_increasing)

lemma cp_pa_sim:
  "(R \<odot> S)\<down> = R \<otimes> S\<down>"
  by (metis co_prod ic_involutive ic_up pa_ic pe_pa_sim)

lemma domain_up_down_conjugate:
  "(R\<up> \<inter> S) * 1\<^sub>\<union>\<^sub>\<union> = (R \<inter> S\<down>) * 1\<^sub>\<union>\<^sub>\<union>"
  apply (rule set_eqI, clarsimp simp: mr_simp)
  by (smt (verit, del_insts) Int_Un_eq(1) SUP_bot SUP_bot_conv(1) Un_Int_eq(1))

lemma down_below_sp_top:
  "R\<down> \<subseteq> R * U"
  apply (clarsimp simp: mr_simp)
  by (metis Int_Union UN_constant image_empty inf_commute)

lemma down_oi_up_closed:
  assumes "Q\<up> = Q"
  shows "R\<down> \<inter> Q \<subseteq> (R \<inter> Q)\<down>"
  using assms apply (clarsimp simp: mr_simp)
  by (metis (no_types, lifting) assms inf.cobounded1 ucl_iff)

lemma up_dist_oU:
  "(\<Union>X)\<up> = \<Union>(up ` X)"
  by (simp add: iu_right_dist_oU)

lemma up_dist_iU:
  assumes "I \<noteq> {}"
  shows "(\<Union>\<Union>X|I)\<up> = \<Union>\<Union>(up o X)|I"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (metis UN_simps(2) assms)
  apply (clarsimp simp: mr_simp)
  subgoal for a f
  proof -
    fix a f
    assume "\<forall>i\<in>I . \<exists>B . (\<exists>C . f i = B \<union> C) \<and> (a,B) \<in> X i"
    from this obtain g where "\<forall>i\<in>I . (\<exists>C . f i = g i \<union> C) \<and> (a,g i) \<in> X i"
      by metis
    hence "(\<exists>C . \<Union>(f ` I) = \<Union>(g ` I) \<union> C) \<and> (\<Union>(g ` I) = \<Union>(g ` I) \<and> (\<forall>i\<in>I . (a,g i) \<in> X i))"
      by auto
    thus "\<exists>B . (\<exists>C . \<Union>(f ` I) = B \<union> C) \<and> (\<exists>f . B = \<Union>(f ` I) \<and> (\<forall>i\<in>I . (a,f i) \<in> X i))"
      by auto
  qed
  done

lemma up_dist_iI:
  "(\<Inter>\<Inter>X|I)\<up> = \<Inter>\<Inter>(up o X)|I"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (smt (z3) INT_simps(10) sup_Inf sup_commute)
  apply (clarsimp simp: mr_simp)
  subgoal for a f
  proof -
    assume "\<forall>i\<in>I . \<exists>B . (\<exists>C . f i = B \<union> C) \<and> (a,B) \<in> X i"
    from this obtain g where "\<forall>i\<in>I . (\<exists>C . f i = g i \<union> C) \<and> (a,g i) \<in> X i"
      by metis
    hence "(\<exists>C . \<Inter>(f ` I) = \<Inter>(g ` I) \<union> C) \<and> (\<Inter>(g ` I) = \<Inter>(g ` I) \<and> (\<forall>i\<in>I . (a,g i) \<in> X i))"
      by auto
    thus "\<exists>B . (\<exists>C . \<Inter>(f ` I) = B \<union> C) \<and> (\<exists>f . B = \<Inter>(f ` I) \<and> (\<forall>i\<in>I . (a,f i) \<in> X i))"
      by auto
  qed
  done

lemma down_dist_oU:
  "(\<Union>X)\<down> = \<Union>(down ` X)"
  by (simp add: ii_right_dist_oU)

lemma down_dist_iU:
  "(\<Union>\<Union>X|I)\<down> = \<Union>\<Union>(down o X)|I"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (metis UN_extend_simps(4))
  apply (clarsimp simp: mr_simp)
  subgoal for a f
  proof -
    assume "\<forall>i\<in>I . \<exists>B . (\<exists>C . f i = B \<inter> C) \<and> (a,B) \<in> X i"
    from this obtain g where "\<forall>i\<in>I . (\<exists>C . f i = g i \<inter> C) \<and> (a,g i) \<in> X i"
      by metis
    hence "(\<exists>C . \<Union>(f ` I) = \<Union>(g ` I) \<inter> C) \<and> (\<Union>(g ` I) = \<Union>(g ` I) \<and> (\<forall>i\<in>I . (a,g i) \<in> X i))"
      by auto
    thus "\<exists>B . (\<exists>C . \<Union>(f ` I) = B \<inter> C) \<and> (\<exists>f . B = \<Union>(f ` I) \<and> (\<forall>i\<in>I . (a,f i) \<in> X i))"
      by auto
  qed
  done

lemma down_dist_iI:
  assumes "I \<noteq> {}"
  shows "(\<Inter>\<Inter>X|I)\<down> = \<Inter>\<Inter>(down o X)|I"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (smt (verit, del_insts) INF_const INT_absorb Int_commute assms semilattice_inf_class.inf_left_commute)
  apply (clarsimp simp: mr_simp)
  subgoal for a f
  proof -
    assume "\<forall>i\<in>I . \<exists>B . (\<exists>C . f i = B \<inter> C) \<and> (a,B) \<in> X i"
    from this obtain g where "\<forall>i\<in>I . (\<exists>C . f i = g i \<inter> C) \<and> (a,g i) \<in> X i"
      by metis
    hence "(\<exists>C . \<Inter>(f ` I) = \<Inter>(g ` I) \<inter> C) \<and> (\<Inter>(g ` I) = \<Inter>(g ` I) \<and> (\<forall>i\<in>I . (a,g i) \<in> X i))"
      by auto
    thus "\<exists>B . (\<exists>C . \<Inter>(f ` I) = B \<inter> C) \<and> (\<exists>f . B = \<Inter>(f ` I) \<and> (\<forall>i\<in>I . (a,f i) \<in> X i))"
      by auto
  qed
  done


lemma iU_up_oI:
  assumes "I \<noteq> {}"
  shows "\<Union>\<Union>(up o X)|I = \<Inter>(up ` X ` I)"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (metis UN_absorb sup_assoc)
  apply (clarsimp simp: mr_simp)
  by (metis UN_constant assms)

lemma iI_down_oI:
  assumes "I \<noteq> {}"
  shows "\<Inter>\<Inter>(down o X)|I = \<Inter>(down ` X ` I)"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (metis INF_absorb Int_assoc)
  apply (clarsimp simp: mr_simp)
  using INF_eq_const assms by auto

lemma down_dist_iI_oI:
  "\<Inter>(down ` X ` I) = (\<Inter>\<Inter>X|I)\<down>"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (metis INF_const INF_greatest INT_absorb empty_iff semilattice_inf_class.inf.absorb_iff2 semilattice_inf_class.le_inf_iff)
  apply (clarsimp simp: mr_simp)
  by blast

lemma up_dist_iU_oI:
  "\<Inter>(up ` X ` I) = (\<Union>\<Union>X|I)\<up>"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
  subgoal for a D proof -
    assume "\<forall>i\<in>I . \<exists>B . (\<exists>C . D = B \<union> C) \<and> (a,B) \<in> X i"
    from this obtain f where 1: "\<forall>i\<in>I . (\<exists>C . D = f i \<union> C) \<and> (a,f i) \<in> X i"
      by metis
    hence "\<exists>C . D = \<Union>(f ` I) \<union> C"
      by auto
    thus ?thesis
      using 1 by auto
  qed
  apply (clarsimp simp: mr_simp)
  by blast

lemma iu_up:
  "(R \<union>\<union> R)\<up> = R\<up>"
  using up_dist_iu_oi by auto

lemma ii_down:
  "(R \<inter>\<inter> R)\<down> = R\<down>"
  using down_dist_ii_oi by blast

lemma iU_up:
  assumes "I \<noteq> {}"
  shows "(\<Union>\<Union>(\<lambda>j . R)|I)\<up> = R\<up>"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
  using assms apply blast
  apply (clarsimp simp: mr_simp)
  by (metis UN_constant assms)

lemma iI_down:
  assumes "I \<noteq> {}"
  shows "(\<Inter>\<Inter>(\<lambda>j . R)|I)\<down> = R\<down>"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
  using assms apply blast
  apply (clarsimp simp: mr_simp)
  by (metis INF_const assms)

lemma iu_unit_up:
  "1\<^sub>\<union>\<^sub>\<union>\<up> = U"
  by (simp add: iu_commute)

lemma iu_unit_down:
  "1\<^sub>\<union>\<^sub>\<union>\<down> = 1\<^sub>\<union>\<^sub>\<union>"
  by (simp add: down_sp)

lemma iu_unit_convex:
  "1\<^sub>\<union>\<^sub>\<union>\<updown> = 1\<^sub>\<union>\<^sub>\<union>"
  by (simp add: iu_unit_down p_id_zero)

lemma ii_unit_up:
  "1\<^sub>\<inter>\<^sub>\<inter>\<up> = 1\<^sub>\<inter>\<^sub>\<inter>"
  by (simp add: up_cp)

lemma ii_unit_down:
  "1\<^sub>\<inter>\<^sub>\<inter>\<down> = U"
  using ii_commute ii_unit by blast

lemma ii_unit_convex:
  "1\<^sub>\<inter>\<^sub>\<inter>\<updown> = 1\<^sub>\<inter>\<^sub>\<inter>"
  using down_increasing ii_unit_up by blast

lemma sp_unit_down:
  "1\<down> = 1 \<union> 1\<^sub>\<union>\<^sub>\<union>"
  by (simp add: down_sp inf_sup_aci(5))

lemma sp_unit_convex:
  "1\<updown> = 1"
  unfolding convex s_id_def by force

lemma top_up:
  "U\<up> = U"
  by simp

lemma top_down:
  "U\<down> = U"
  by (metis U_par_idem ic_top ic_up)

lemma top_convex:
  "U\<updown> = U"
  by (simp add: top_down)

lemma bot_up:
  "{}\<up> = {}"
  by (simp add: p_prod_comm)

lemma bot_down:
  "{}\<down> = {}"
  using oi_down_up_iff by fastforce

lemma bot_convex:
  "{}\<updown> = {}"
  by (simp add: bot_down)

lemma down_oi_up_convex:
  "(R\<down> \<inter> S\<up>)\<updown> = R\<down> \<inter> S\<up>"
  unfolding up down convex by blast

lemma convex_iff_down_oi_up:
  "Q = Q\<updown> \<longleftrightarrow> (\<exists>R S . Q = R\<down> \<inter> S\<up>)"
  using down_oi_up_convex by blast

lemma convex_closed_oI:
  "(\<Inter>R\<in>X . R\<updown>)\<updown> = (\<Inter>R\<in>X . R\<updown>)"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (smt (verit, best) semilattice_inf_class.inf_commute semilattice_inf_class.inf_left_commute sup_commute sup_left_commute)
  by (meson convex_increasing)

lemma convex_closed_oi:
  "(R\<updown> \<inter> S\<updown>)\<updown> = R\<updown> \<inter> S\<updown>"
  using convex_closed_oI[of "{R,S}"] by simp

lemma
  "(R\<updown> \<union>\<union> S\<updown>)\<updown> = R\<updown> \<union>\<union> S\<updown>"
  nitpick[expect=genuine,card=1,3]
  oops

  section \<open>Powerdomain Preorders\<close>

abbreviation lower_less_eq :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> bool" (infixl "\<sqsubseteq>\<down>" 50) where
  "R \<sqsubseteq>\<down> S \<equiv> R \<subseteq> S\<down>"

abbreviation upper_less_eq :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> bool" (infixl "\<sqsubseteq>\<up>" 50) where
  "R \<sqsubseteq>\<up> S \<equiv> S \<subseteq> R\<up>"

abbreviation convex_less_eq :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> bool" (infixl "\<sqsubseteq>\<updown>" 50) where
  "R \<sqsubseteq>\<updown> S \<equiv> R \<sqsubseteq>\<down> S \<and> R \<sqsubseteq>\<up> S"

abbreviation Convex_less_eq :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> bool" (infixl "\<sqsubseteq>\<Updown>" 50) where
  "R \<sqsubseteq>\<Updown> S \<equiv> R \<subseteq> S\<updown>"

lemma lower_less_eq:
  "R \<sqsubseteq>\<down> S \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<longrightarrow> (\<exists>C . (a,C) \<in> S \<and> B \<subseteq> C))"
  apply (clarsimp simp: mr_simp)
  apply safe
   apply blast
  by (metis inf.absorb_iff2)

lemma upper_less_eq:
  "R \<sqsubseteq>\<up> S \<longleftrightarrow> (\<forall>a C . (a,C) \<in> S \<longrightarrow> (\<exists>B . (a,B) \<in> R \<and> B \<subseteq> C))"
  by (meson U_par_st subrelI subsetD)

lemma Convex_less_eq:
  "R \<sqsubseteq>\<Updown> S \<longleftrightarrow> (\<forall>a C . (a,C) \<in> R \<longrightarrow> (\<exists>B D . (a,B) \<in> S \<and> (a,D) \<in> S \<and> B \<subseteq> C \<and> C \<subseteq> D))"
  by (meson lower_less_eq semilattice_inf_class.le_inf_iff upper_less_eq)

lemma Convex_lower_upper:
  "R \<sqsubseteq>\<Updown> S \<longleftrightarrow> R \<sqsubseteq>\<down> S \<and> S \<sqsubseteq>\<up> R"
  by auto

lemma lower_reflexive:
  "R \<sqsubseteq>\<down> R"
  by (fact down_increasing)

lemma upper_reflexive:
  "R \<sqsubseteq>\<up> R"
  by (fact up_increasing)

lemma convex_reflexive:
  "R \<sqsubseteq>\<updown> R"
  by (simp add: lower_reflexive upper_reflexive)

lemma Convex_reflexive:
  "R \<sqsubseteq>\<Updown> R"
  by (fact convex_increasing)

lemma lower_transitive:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> S \<sqsubseteq>\<down> T \<Longrightarrow> R \<sqsubseteq>\<down> T"
  using down_idempotent down_isotone by blast

lemma upper_transitive:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> S \<sqsubseteq>\<up> T \<Longrightarrow> R \<sqsubseteq>\<up> T"
  using up_idempotent up_isotone by blast

lemma convex_transitive:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> S \<sqsubseteq>\<updown> T \<Longrightarrow> R \<sqsubseteq>\<updown> T"
  by (meson lower_transitive upper_transitive)

lemma Convex_transitive:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> S \<sqsubseteq>\<Updown> T \<Longrightarrow> R \<sqsubseteq>\<Updown> T"
  by (metis le_inf_iff lower_transitive upper_transitive)

lemma bot_lower_least:
  "{} \<sqsubseteq>\<down> R"
  by simp

lemma top_upper_least:
  "U \<sqsubseteq>\<up> R"
  by (metis U_par_idem iu_assoc le_inf_iff up_dist_iu_oi upper_reflexive)

lemma bot_Convex_least:
  "{} \<sqsubseteq>\<Updown> R"
  by simp

lemma top_lower_greatest:
  "R \<sqsubseteq>\<down> U"
  using U_par_idem top_down top_upper_least by blast

lemma bot_upper_greatest:
  "R \<sqsubseteq>\<up> {}"
  by simp

lemma top_Convex_greatest:
  "R \<sqsubseteq>\<Updown> U"
  using U_par_idem top_down top_upper_least by auto

lemma lower_iu_increasing:
  "R \<sqsubseteq>\<down> R \<union>\<union> R"
  by (meson dual_order.trans lower_reflexive subidem_par)

lemma upper_iu_increasing:
  "R \<sqsubseteq>\<up> R \<union>\<union> S"
  using p_prod_isor top_upper_least by auto

lemma convex_iu_increasing:
  "R \<sqsubseteq>\<updown> R \<union>\<union> R"
  by (simp add: lower_iu_increasing upper_iu_increasing)

lemma Convex_iu_increasing:
  "R \<sqsubseteq>\<Updown> R \<union>\<union> R"
  by (simp add: iu_up lower_iu_increasing upper_reflexive)

lemma lower_ii_decreasing:
  "R \<inter>\<inter> S \<sqsubseteq>\<down> R"
  by (metis ii_right_isotone top_down top_lower_greatest)

lemma upper_ii_decreasing:
  "R \<inter>\<inter> R \<sqsubseteq>\<up> R"
  using convex_reflexive ii_sub_idempotent by fastforce

lemma convex_ii_decreasing:
  "R \<inter>\<inter> R \<sqsubseteq>\<updown> R"
  by (simp add: lower_ii_decreasing upper_ii_decreasing)

lemma Convex_ii_increasing:
  "R \<sqsubseteq>\<Updown> R \<inter>\<inter> R"
  by (simp add: ii_down lower_reflexive upper_ii_decreasing)

lemma iu_lower_left_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> R \<union>\<union> T \<sqsubseteq>\<down> S \<union>\<union> T"
  by (simp add: down_dist_iu iu_isotone lower_reflexive)

lemma iu_upper_left_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> R \<union>\<union> T \<sqsubseteq>\<up> S \<union>\<union> T"
  by (metis (no_types, lifting) iu_assoc iu_commute iu_left_isotone)

lemma iu_convex_left_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> R \<union>\<union> T \<sqsubseteq>\<updown> S \<union>\<union> T"
  by (simp add: iu_lower_left_isotone iu_upper_left_isotone)

lemma iu_Convex_left_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> R \<union>\<union> T \<sqsubseteq>\<Updown> S \<union>\<union> T"
  by (simp add: iu_lower_left_isotone iu_upper_left_isotone)

lemma iu_lower_right_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> T \<union>\<union> R \<sqsubseteq>\<down> T \<union>\<union> S"
  by (simp add: iu_commute iu_lower_left_isotone)

lemma iu_upper_right_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> T \<union>\<union> R \<sqsubseteq>\<up> T \<union>\<union> S"
  by (simp add: iu_assoc iu_right_isotone)

lemma iu_convex_right_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> T \<union>\<union> R \<sqsubseteq>\<updown> T \<union>\<union> S"
  by (simp add: iu_lower_right_isotone iu_upper_right_isotone)

lemma iu_Convex_right_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> T \<union>\<union> R \<sqsubseteq>\<Updown> T \<union>\<union> S"
  by (simp add: iu_lower_right_isotone iu_upper_right_isotone)

lemma iu_lower_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> P \<sqsubseteq>\<down> Q \<Longrightarrow> R \<union>\<union> P \<sqsubseteq>\<down> S \<union>\<union> Q"
  by (simp add: down_dist_iu iu_isotone)

lemma iu_upper_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> P \<sqsubseteq>\<up> Q \<Longrightarrow> R \<union>\<union> P \<sqsubseteq>\<up> S \<union>\<union> Q"
  by (simp add: iu_isotone up_dist_iu)

lemma iu_convex_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> P \<sqsubseteq>\<updown> Q \<Longrightarrow> R \<union>\<union> P \<sqsubseteq>\<updown> S \<union>\<union> Q"
  by (simp add: iu_lower_isotone iu_upper_isotone)

lemma iu_Convex_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> P \<sqsubseteq>\<Updown> Q \<Longrightarrow> R \<union>\<union> P \<sqsubseteq>\<Updown> S \<union>\<union> Q"
  by (simp add: down_dist_iu iu_isotone up_dist_iu)

lemma ii_lower_left_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> R \<inter>\<inter> T \<sqsubseteq>\<down> S \<inter>\<inter> T"
  by (simp add: down_dist_ii ii_isotone lower_reflexive)

lemma ii_upper_left_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> R \<inter>\<inter> T \<sqsubseteq>\<up> S \<inter>\<inter> T"
  by (simp add: ii_isotone up_dist_ii upper_reflexive)

lemma ii_convex_left_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> R \<inter>\<inter> T \<sqsubseteq>\<updown> S \<inter>\<inter> T"
  by (simp add: ii_lower_left_isotone ii_upper_left_isotone)

lemma ii_Convex_left_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> R \<inter>\<inter> T \<sqsubseteq>\<Updown> S \<inter>\<inter> T"
  by (simp add: ii_lower_left_isotone ii_upper_left_isotone)

lemma ii_lower_right_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> T \<inter>\<inter> R \<sqsubseteq>\<down> T \<inter>\<inter> S"
  by (simp add: ii_assoc ii_right_isotone)

lemma ii_upper_right_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> T \<inter>\<inter> R \<sqsubseteq>\<up> T \<inter>\<inter> S"
  by (simp add: ii_commute ii_upper_left_isotone)

lemma ii_convex_right_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> T \<inter>\<inter> R \<sqsubseteq>\<updown> T \<inter>\<inter> S"
  by (simp add: ii_lower_right_isotone ii_upper_right_isotone)

lemma ii_Convex_right_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> T \<inter>\<inter> R \<sqsubseteq>\<Updown> T \<inter>\<inter> S"
  by (simp add: ii_lower_right_isotone ii_upper_right_isotone)

lemma ii_lower_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> P \<sqsubseteq>\<down> Q \<Longrightarrow> R \<inter>\<inter> P \<sqsubseteq>\<down> S \<inter>\<inter> Q"
  by (simp add: down_dist_ii ii_isotone)

lemma ii_upper_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> P \<sqsubseteq>\<up> Q \<Longrightarrow> R \<inter>\<inter> P \<sqsubseteq>\<up> S \<inter>\<inter> Q"
  by (simp add: ii_isotone up_dist_ii)

lemma ii_convex_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> P \<sqsubseteq>\<updown> Q \<Longrightarrow> R \<inter>\<inter> P \<sqsubseteq>\<updown> S \<inter>\<inter> Q"
  by (simp add: ii_lower_isotone ii_upper_isotone)

lemma ii_Convex_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> P \<sqsubseteq>\<Updown> Q \<Longrightarrow> R \<inter>\<inter> P \<sqsubseteq>\<Updown> S \<inter>\<inter> Q"
  by (simp add: ii_lower_isotone ii_upper_isotone)

lemma ou_lower_left_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> R \<union> T \<sqsubseteq>\<down> S \<union> T"
  by (meson le_sup_iff lower_reflexive lower_transitive)

lemma ou_upper_left_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> R \<union> T \<sqsubseteq>\<up> S \<union> T"
  by (metis Un_subset_iff sup.coboundedI1 up_dist_ou upclosed_ext)

lemma ou_convex_left_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> R \<union> T \<sqsubseteq>\<updown> S \<union> T"
  by (meson ou_lower_left_isotone ou_upper_left_isotone)

lemma ou_Convex_left_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> R \<union> T \<sqsubseteq>\<Updown> S \<union> T"
  by (meson le_inf_iff ou_lower_left_isotone ou_upper_left_isotone)

lemma ou_lower_right_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> T \<union> R \<sqsubseteq>\<down> T \<union> S"
  by (metis Un_commute ou_lower_left_isotone)

lemma ou_upper_right_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> T \<union> R \<sqsubseteq>\<up> T \<union> S"
  by (metis Un_commute ou_upper_left_isotone)

lemma ou_convex_right_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> T \<union> R \<sqsubseteq>\<updown> T \<union> S"
  by (meson ou_lower_right_isotone ou_upper_right_isotone)

lemma ou_Convex_right_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> T \<union> R \<sqsubseteq>\<Updown> T \<union> S"
  by (metis Un_commute ou_Convex_left_isotone)

lemma ou_lower_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> P \<sqsubseteq>\<down> Q \<Longrightarrow> R \<union> P \<sqsubseteq>\<down> S \<union> Q"
  using down_dist_ou by blast

lemma ou_upper_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> P \<sqsubseteq>\<up> Q \<Longrightarrow> R \<union> P \<sqsubseteq>\<up> S \<union> Q"
  by (simp add: iu_right_dist_ou sup.coboundedI1 sup.coboundedI2)

lemma ou_convex_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> P \<sqsubseteq>\<updown> Q \<Longrightarrow> R \<union> P \<sqsubseteq>\<updown> S \<union> Q"
  by (meson ou_lower_isotone ou_upper_isotone)

lemma ou_Convex_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> P \<sqsubseteq>\<Updown> Q \<Longrightarrow> R \<union> P \<sqsubseteq>\<Updown> S \<union> Q"
  by (metis le_inf_iff ou_lower_isotone ou_upper_isotone)

lemma sp_lower_left_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> T * R \<sqsubseteq>\<down> T * S"
  by (simp add: down_dist_sp s_prod_isor)

lemma sp_upper_left_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> T * R \<sqsubseteq>\<up> T * S"
  by (meson cl3 dual_order.trans s_prod_isor upper_iu_increasing)

lemma sp_convex_left_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> T * R \<sqsubseteq>\<updown> T * S"
  by (simp add: sp_lower_left_isotone sp_upper_left_isotone)

lemma sp_Convex_left_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> T * R \<sqsubseteq>\<Updown> T * S"
  by (simp add: sp_lower_left_isotone sp_upper_left_isotone)

lemma cp_lower_left_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> T \<odot> R \<sqsubseteq>\<down> T \<odot> S"
  by (smt (verit) co_prod ic_antidist_ii ic_antidist_iu ic_isotone ic_top sp_upper_left_isotone)

lemma cp_upper_left_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> T \<odot> R \<sqsubseteq>\<up> T \<odot> S"
  by (simp add: cp_right_isotone up_dist_cp)

lemma cp_convex_left_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> T \<odot> R \<sqsubseteq>\<updown> T \<odot> S"
  by (simp add: cp_lower_left_isotone cp_upper_left_isotone)

lemma cp_Convex_left_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> T \<odot> R \<sqsubseteq>\<Updown> T \<odot> S"
  by (simp add: cp_lower_left_isotone cp_upper_left_isotone)

lemma lower_ic_upper:
  "R \<sqsubseteq>\<down> S \<longleftrightarrow> \<sim>S \<sqsubseteq>\<up> \<sim>R"
  by (metis ic_down ic_involutive ic_isotone)

lemma upper_ic_lower:
  "R \<sqsubseteq>\<up> S \<longleftrightarrow> \<sim>S \<sqsubseteq>\<down> \<sim>R"
  by (simp add: lower_ic_upper)

lemma convex_ic:
  "R \<sqsubseteq>\<updown> S \<longleftrightarrow> \<sim>S \<sqsubseteq>\<updown> \<sim>R"
  by (meson lower_ic_upper upper_ic_lower)

lemma Convex_ic:
  "R \<sqsubseteq>\<Updown> S \<longleftrightarrow> \<sim>R \<sqsubseteq>\<Updown> \<sim>S"
  by (metis le_inf_iff lower_ic_upper upper_ic_lower)

lemma up_lower_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> R\<up> \<sqsubseteq>\<down> S\<up>"
  by (fact iu_lower_left_isotone)

lemma up_upper_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> R\<up> \<sqsubseteq>\<up> S\<up>"
  by (fact iu_left_isotone)

lemma up_convex_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> R\<up> \<sqsubseteq>\<updown> S\<up>"
  by (fact iu_convex_left_isotone)

lemma up_Convex_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> R\<up> \<sqsubseteq>\<Updown> S\<up>"
  by (fact iu_Convex_left_isotone)

lemma down_lower_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> R\<down> \<sqsubseteq>\<down> S\<down>"
  by (fact down_isotone)

lemma down_upper_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> R\<down> \<sqsubseteq>\<up> S\<down>"
  by (fact ii_upper_left_isotone)

lemma down_convex_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> R\<down> \<sqsubseteq>\<updown> S\<down>"
  by (fact ii_convex_left_isotone)

lemma down_Convex_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> R\<down> \<sqsubseteq>\<Updown> S\<down>"
  by (fact ii_Convex_left_isotone)

lemma convex_lower_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> R\<updown> \<sqsubseteq>\<down> S\<updown>"
  by (metis convex_idempotent convex_increasing le_inf_iff lower_transitive)

lemma convex_upper_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> R\<updown> \<sqsubseteq>\<up> S\<updown>"
  by (simp add: convex_lower_isotone ic_convex upper_ic_lower)

lemma convex_convex_isotone:
  "R \<sqsubseteq>\<updown> S \<Longrightarrow> R\<updown> \<sqsubseteq>\<updown> S\<updown>"
  by (simp add: convex_lower_isotone convex_upper_isotone)

lemma convex_Convex_isotone:
  "R \<sqsubseteq>\<Updown> S \<Longrightarrow> R\<updown> \<sqsubseteq>\<Updown> S\<updown>"
  by (fact convex_isotone)

lemma subset_lower:
  "R \<subseteq> S \<Longrightarrow> R \<sqsubseteq>\<down> S"
  using lower_reflexive by auto

lemma subset_upper:
  "R \<subseteq> S \<Longrightarrow> S \<sqsubseteq>\<up> R"
  using upper_reflexive by blast

lemma subset_Convex:
  "R \<subseteq> S \<Longrightarrow> R \<sqsubseteq>\<Updown> S"
  by (simp add: subset_lower subset_upper)

lemma oi_subset_lower_left_isotone:
  "R \<subseteq> S \<Longrightarrow> R \<inter> T \<sqsubseteq>\<down> S \<inter> T"
  using lower_reflexive by fastforce

lemma oi_subset_upper_left_antitone:
  "R \<subseteq> S \<Longrightarrow> S \<inter> T \<sqsubseteq>\<up> R \<inter> T"
  using upper_reflexive by force

lemma oi_subset_Convex_left_isotone:
  "R \<subseteq> S \<Longrightarrow> R \<inter> T \<sqsubseteq>\<Updown> S \<inter> T"
  by (simp add: oi_subset_lower_left_isotone oi_subset_upper_left_antitone)

lemma oi_subset_lower_right_isotone:
  "R \<subseteq> S \<Longrightarrow> T \<inter> R \<sqsubseteq>\<down> T \<inter> S"
  by (simp add: oi_subset_lower_left_isotone semilattice_inf_class.inf_commute)

lemma oi_subset_upper_right_antitone:
  "R \<subseteq> S \<Longrightarrow> T \<inter> S \<sqsubseteq>\<up> T \<inter> R"
  by (simp add: oi_subset_upper_left_antitone semilattice_inf_class.inf_commute)

lemma oi_subset_Convex_right_isotone:
  "R \<subseteq> S \<Longrightarrow> T \<inter> R \<sqsubseteq>\<Updown> T \<inter> S"
  using oi_subset_Convex_left_isotone by blast

lemma oi_subset_lower_isotone:
  "R \<subseteq> S \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> R \<inter> P \<sqsubseteq>\<down> S \<inter> Q"
  by (meson Int_mono subset_lower)

lemma oi_subset_upper_antitone:
  "R \<subseteq> S \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> S \<inter> Q \<sqsubseteq>\<up> R \<inter> P"
  by (meson Int_mono subset_upper)

lemma oi_subset_Convex_isotone:
  "R \<subseteq> S \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> R \<inter> P \<sqsubseteq>\<Updown> S \<inter> Q"
  by (simp add: oi_subset_lower_isotone oi_subset_upper_antitone)

lemma sp_iu_unit_lower:
  "R * 1\<^sub>\<union>\<^sub>\<union> \<sqsubseteq>\<down> R"
  using lower_ii_decreasing sp_right_iu_unit by blast

lemma cp_ii_unit_upper:
  "R \<sqsubseteq>\<up> R \<odot> 1\<^sub>\<inter>\<^sub>\<inter>"
  by (meson cp_right_ii_unit in_mono subsetI upper_iu_increasing)

lemma lower_ii_down:
  "R \<sqsubseteq>\<down> S \<longleftrightarrow> R\<down> = (R \<inter>\<inter> S)\<down>"
  apply safe
    apply (metis down_dist_ii_oi inf.orderE lower_ii_decreasing lower_transitive)
  using ii_assoc lower_ii_decreasing apply blast
  by (metis IntE down_dist_ii_oi lower_reflexive subset_eq)

lemma lower_ii_lower_bound:
  "R \<sqsubseteq>\<down> S \<longleftrightarrow> R \<subseteq> R \<inter>\<inter> S"
  by (clarsimp simp: mr_simp) blast

lemma upper_ii_up:
  "R \<sqsubseteq>\<up> S \<longleftrightarrow> S\<up> = (R \<union>\<union> S)\<up>"
  by (metis inf.absorb_iff2 up_dist_iu_oi upclosed_ext upper_iu_increasing upper_transitive)

lemma upper_ii_upper_bound:
  "R \<sqsubseteq>\<up> S \<longleftrightarrow> S \<subseteq> R \<union>\<union> S"
  by (clarsimp simp: mr_simp) blast

lemma
  "R \<sqsubseteq>\<down> S \<longleftrightarrow> R = R \<inter>\<inter> S"
  nitpick[expect=genuine,card=1]
  oops

lemma
  "R \<sqsubseteq>\<up> S \<longleftrightarrow> S = R \<union>\<union> S"
  nitpick[expect=genuine,card=1]
  oops

lemma convex_oi_Convex_iu:
  "R\<updown> \<inter> S\<updown> \<sqsubseteq>\<Updown> R \<union>\<union> S"
  by (meson inf_le1 inf_le2 iu_Convex_isotone order_trans subidem_par)

lemma convex_oi_Convex_ii:
  "R\<updown> \<inter> S\<updown> \<sqsubseteq>\<Updown> R \<inter>\<inter> S"
  by (meson ii_Convex_isotone ii_sub_idempotent inf_le1 inf_le2 order_trans)

lemma convex_oi_iu_ii:
  "R\<updown> \<inter> S\<updown> = (R \<union>\<union> S)\<up> \<inter> (R \<inter>\<inter> S)\<down>"
  by (metis down_dist_ii_oi inf_assoc inf_left_commute up_dist_iu_oi)

lemma ii_lower_iu:
  "R \<inter>\<inter> S \<sqsubseteq>\<down> R \<union>\<union> S"
  apply (clarsimp simp: mr_simp)
  by (metis Un_Int_eq(2) inf_left_commute)

lemma ii_upper_iu:
  "R \<inter>\<inter> S \<sqsubseteq>\<up> R \<union>\<union> S"
  by (simp add: ic_antidist_ii ic_antidist_iu ii_lower_iu upper_ic_lower)

lemma ii_convex_iu:
  "R \<inter>\<inter> S \<sqsubseteq>\<updown> R \<union>\<union> S"
  by (simp add: ii_lower_iu ii_upper_iu)

lemma convex_oi_iu_ii_convex:
  "R\<updown> \<inter> S\<updown> = (R \<union>\<union> S)\<updown> \<inter> (R \<inter>\<inter> S)\<updown>"
  by (metis convex_oi_iu_ii ii_lower_iu ii_upper_iu inf.commute lower_ii_down upper_ii_up)

subsection \<open>Functional properties of multirelations\<close>

lemma id_one_converse:
  "Id = 1 ; 1\<^sup>\<smile>"
  unfolding Id_def converse_def relcomp_unfold s_id_def by force

lemma dom_explicit:
  "Dom R = R ; U \<inter> 1"
  by (clarsimp simp: mr_simp Dom_def) blast

lemma dom_explicit_2:
  "Dom R = R ; top \<inter> 1"
  apply (clarsimp simp: mr_simp Dom_def)
  apply safe
    apply (simp add: relcomp.relcompI top_def)
   apply blast
  by blast

lemma total_dom:
  "total R \<longleftrightarrow> Dom R = 1"
  unfolding total_def dom_explicit_2
  apply (rule iffI)
  using top_def apply fastforce
  by (metis Int_subset_iff dom_def dom_gla_top dom_top id_one_converse inf.idem inf_le1)

lemma total_eq:
  "total R \<longleftrightarrow> 1\<^sub>\<union>\<^sub>\<union> = R * 1\<^sub>\<union>\<^sub>\<union>"
  by (metis total_dom U_c cd_iso dc dc_prop2)

lemma domain_pointwise:
  "x \<in> R * 1\<^sub>\<union>\<^sub>\<union> \<longleftrightarrow> (\<exists>a B . (a,B) \<in> R \<and> x = (a,{}))"
  by (smt mem_Collect_eq p_id_st)

text \<open>\<open>card\<close> only works for finite sets\<close>

lemma univalent_2:
  "univalent R \<longleftrightarrow> (\<forall>a . finite { B . (a,B) \<in> R } \<and> card { B . (a,B) \<in> R } \<le> one_class.one)"
proof
  assume 1: "univalent R"
  show "\<forall>a . finite { B . (a,B) \<in> R } \<and> card { B . (a,B) \<in> R } \<le> one_class.one"
  proof
    fix a
    let ?B = "{ B . (a,B) \<in> R }"
    show "finite ?B \<and> card ?B \<le> one_class.one"
    proof (rule conjI)
      show 2: "finite ?B"
      proof (rule ccontr)
        assume 3: "infinite ?B"
        from this obtain B where 4: "(a,B) \<in> R"
          using not_finite_existsD by auto
        have "?B = {B}"
        proof
          show "?B \<subseteq> {B}"
            using 1 4 by (metis (no_types, lifting) univalent_set insertCI mem_Collect_eq subsetI)
        next
          show "{B} \<subseteq> ?B"
            using 4 by simp
        qed
        thus False
          using 3 by auto
      qed
      show "card ?B \<le> one_class.one"
      proof (rule ccontr)
        assume 5: "\<not> card ?B \<le> one_class.one"
        from this obtain B where 6: "(a,B) \<in> R"
          by fastforce
        hence "card (?B - {B}) \<ge> one_class.one"
          using 2 5 by auto
        from this obtain C where "(a,C) \<in> R \<and> B \<noteq> C"
          using 5 by (metis (no_types, lifting) CollectD One_nat_def card.insert_remove card_Diff_singleton_if card.empty card_mono empty_iff finite.emptyI finite.insertI insert_iff subsetI)
        thus False
          using 1 6 by (meson univalent_set)
      qed
    qed
  qed
next
  assume 5: "\<forall>a . finite { B . (a,B) \<in> R } \<and> card { B . (a,B) \<in> R } \<le> one_class.one"
  have "\<forall>a B C . (a,B) \<in> R \<and> (a,C) \<in> R \<longrightarrow> B = C"
  proof (intro allI, rule impI)
    fix a B C
    let ?B = "{ B . (a,B) \<in> R }"
    have 6: "finite ?B"
      using 5 by simp
    assume "(a,B) \<in> R \<and> (a,C) \<in> R"
    hence "{B,C} \<subseteq> ?B"
      by simp
    hence "card {B,C} \<le> one_class.one"
      using 5 6 by (meson card_mono le_trans)
    thus "B = C"
      by (metis One_nat_def card.empty card_insert_disjoint empty_iff finite.emptyI finite.insertI insert_absorb lessI not_le singleton_insert_inj_eq)
  qed
  thus "univalent R"
    by (simp add: univalent_set)
qed

lemma univalent_3:
  "univalent R \<longleftrightarrow> (\<forall>S . R * 1\<^sub>\<union>\<^sub>\<union> = S * 1\<^sub>\<union>\<^sub>\<union> \<and> S \<subseteq> R \<longrightarrow> S = R)"
proof
  assume 1: "\<forall>S . R * 1\<^sub>\<union>\<^sub>\<union> = S * 1\<^sub>\<union>\<^sub>\<union> \<and> S \<subseteq> R \<longrightarrow> S = R"
  have "\<forall>a B C . (a,B) \<in> R \<and> (a,C) \<in> R \<longrightarrow> B = C"
  proof (intro allI, rule impI)
    fix a B C
    assume 2: "(a,B) \<in> R \<and> (a,C) \<in> R"
    show "B = C"
    proof (rule ccontr)
      assume 3: "B \<noteq> C"
      let ?S = "R - { (a,C) }"
      have 4: "R * 1\<^sub>\<union>\<^sub>\<union> = ?S * 1\<^sub>\<union>\<^sub>\<union>"
      proof
        show "R * 1\<^sub>\<union>\<^sub>\<union> \<subseteq> ?S * 1\<^sub>\<union>\<^sub>\<union>"
        proof
          fix x::"'a \<times> 'f set"
          assume "x \<in> R * 1\<^sub>\<union>\<^sub>\<union>"
          from this obtain b D where "(b,D) \<in> R \<and> x = (b,{})"
            by (meson domain_pointwise)
          thus "x \<in> ?S * 1\<^sub>\<union>\<^sub>\<union>"
            using 2 3 by (metis domain_pointwise Pair_inject insertE insert_Diff)
        qed
      next
        show "?S * 1\<^sub>\<union>\<^sub>\<union> \<subseteq> R * 1\<^sub>\<union>\<^sub>\<union>"
          by (simp add: s_prod_isol)
      qed
      have "?S \<noteq> R"
        using 2 by blast
      thus False
        using 1 4 by blast
    qed
  qed
  thus "univalent R"
    by (simp add: univalent_set)
next
  assume 5: "univalent R"
  show "\<forall>S . R * 1\<^sub>\<union>\<^sub>\<union> = S * 1\<^sub>\<union>\<^sub>\<union> \<and> S \<subseteq> R \<longrightarrow> S = R"
  proof
    fix S
    show "R * 1\<^sub>\<union>\<^sub>\<union> = S * 1\<^sub>\<union>\<^sub>\<union> \<and> S \<subseteq> R \<longrightarrow> S = R"
    proof
      assume 6: "R * 1\<^sub>\<union>\<^sub>\<union> = S * 1\<^sub>\<union>\<^sub>\<union> \<and> S \<subseteq> R"
      have "R \<subseteq> S"
      proof
        fix x
        assume 7: "x \<in> R"
        from this obtain a B where 8: "x = (a,B)"
          by fastforce
        show "x \<in> S"
        proof (cases "\<exists>C . C \<noteq> B \<and> (a,C) \<in> S")
          case True
          thus ?thesis
            using 5 6 7 8 by (metis subsetD univalent_set)
        next
          case False
          thus ?thesis
            using 6 7 8 by (metis (no_types, lifting) domain_pointwise prod.inject)
        qed
      qed
      thus "S = R"
        using 6 by simp
    qed
  qed
qed

lemma total_2:
  "total R \<longleftrightarrow> (\<forall>a . { B . (a,B) \<in> R } \<noteq> {})"
  by (simp add: total_set)

lemma total_3:
  "total R \<longleftrightarrow> (\<forall>a . finite { B . (a,B) \<in> R } \<longrightarrow> card { B . (a,B) \<in> R } \<ge> one_class.one)"
  by (metis finite.emptyI nonempty_set_card total_2)

lemma total_4: "total R \<longleftrightarrow> 1\<^sub>\<union>\<^sub>\<union> \<subseteq> R * 1\<^sub>\<union>\<^sub>\<union>"
  by (simp add: c6 order_antisym_conv total_eq)

lemma deterministic_2:
  "deterministic R \<longleftrightarrow> (\<forall>a . card { B . (a,B) \<in> R } = one_class.one)"
  apply (rule iffI)
   apply (metis One_nat_def bot_nat_0.extremum_unique deterministic_def le_simps(2) less_Suc_eq nonempty_set_card total_2 univalent_2)
  by (metis card_1_singletonE deterministic_def finite.emptyI finite_insert order.refl total_3 univalent_2)

lemma univalent_convex:
  assumes "univalent S"
  shows "S = S\<updown>"
  apply (rule antisym)
   apply (simp add: lower_reflexive upper_reflexive)
  apply (clarsimp simp: mr_simp)
  by (metis assms lattice_class.sup_inf_absorb sup_left_idem univalent_set)

lemma univalent_iu_idempotent:
  assumes "univalent S"
  shows "S = S \<union>\<union> S"
  apply (rule antisym)
   apply (meson convex_reflexive upper_ii_upper_bound)
  apply (clarsimp simp: mr_simp)
  by (metis assms sup.idem univalent_set)

lemma univalent_ii_idempotent:
  assumes "univalent S"
  shows "S = S \<inter>\<inter> S"
  apply (rule antisym)
   apply (simp add: ii_sub_idempotent)
  apply (clarsimp simp: mr_simp)
  by (metis assms semilattice_inf_class.inf.idem univalent_set)

lemma univalent_down_iu_idempotent:
  assumes "univalent S"
  shows "S = S\<down> \<union>\<union> S"
  apply (rule antisym)
   apply (meson convex_reflexive subset_upper upper_ii_upper_bound)
  apply (clarsimp simp: mr_simp)
  by (metis assms lattice_class.sup_inf_absorb sup_commute univalent_set)

lemma univalent_up_ii_idempotent:
  assumes "univalent S"
  shows "S = S\<up> \<inter>\<inter> S"
  apply (rule antisym)
   apply (metis assms ii_left_isotone univalent_ii_idempotent upclosed_ext)
  apply (clarsimp simp: mr_simp)
  by (metis Int_commute assms lattice_class.inf_sup_absorb univalent_set)

lemma univalent_convex_iu_idempotent:
  assumes "univalent S"
  shows "S = S\<updown> \<union>\<union> S"
  by (metis assms univalent_convex univalent_iu_idempotent)

lemma univalent_convex_ii_idempotent:
  assumes "univalent S"
  shows "S = S\<updown> \<inter>\<inter> S"
  by (metis assms univalent_convex univalent_ii_idempotent)

lemma univalent_iu_closed:
  "univalent R \<Longrightarrow> univalent S \<Longrightarrow> univalent (R \<union>\<union> S)"
  by (smt (verit, best) case_prodD mem_Collect_eq p_prod_def univalent_set)

lemma univalent_ii_closed:
  "univalent R \<Longrightarrow> univalent S \<Longrightarrow> univalent (R \<inter>\<inter> S)"
  by (smt (verit, ccfv_SIG) CollectD Pair_inject case_prodE inner_intersection_def univalent_set)

lemma total_lower:
  "total R \<longleftrightarrow> 1\<^sub>\<union>\<^sub>\<union> \<sqsubseteq>\<down> R"
  unfolding lower_less_eq
  by (simp add: p_id_def total_set)

lemma total_upper:
  "total R \<longleftrightarrow> R \<sqsubseteq>\<up> 1\<^sub>\<inter>\<^sub>\<inter>"
  unfolding upper_less_eq
  by (simp add: ii_unit_def total_set)

lemma total_lower_iu:
  assumes "total T"
  shows "R \<sqsubseteq>\<down> R \<union>\<union> T"
  by (metis assms iu_lower_right_isotone iu_unit total_lower)

lemma total_upper_ii:
  assumes "total T"
  shows "R \<inter>\<inter> T \<sqsubseteq>\<up> R"
  by (smt (verit, ccfv_threshold) U_par_idem assms iu_assoc iu_commute lower_ii_lower_bound total_lower_iu up_dist_ii upper_ii_up)

lemma total_univalent_lower_iu:
  assumes "total T"
    and "univalent S"
    and "T \<sqsubseteq>\<down> S"
  shows "T \<union>\<union> S = S"
proof -
  have 1: "\<forall>a. \<exists>B. (a, B) \<in> T"
    by (meson assms(1) total_set)
  have 2: "\<forall>a B C. (a, B) \<in> S \<and> (a, C) \<in> S \<longrightarrow> B = C"
    by (meson assms(2) univalent_set)
  hence 3: "T \<union>\<union> S \<subseteq> S"
    by (metis assms(2,3) iu_left_isotone univalent_down_iu_idempotent)
  hence "S \<subseteq> T \<union>\<union> S"
    apply (clarsimp simp: mr_simp)
    using 1 2 by (metis (mono_tags, lifting) CollectI Un_iff case_prodI subset_Un_eq)
  thus ?thesis
    using 3 by (simp add: subset_antisym)
qed

lemma total_iu_closed:
  "total R \<Longrightarrow> total S \<Longrightarrow> total (R \<union>\<union> S)"
  by (meson lower_transitive total_lower total_lower_iu)

lemma total_ii_closed:
  "total R \<Longrightarrow> total S \<Longrightarrow> total (R \<inter>\<inter> S)"
  by (metis down_dist_ii_oi le_inf_iff total_lower)

lemma deterministic_lower:
  assumes "deterministic V"
  shows "R \<sqsubseteq>\<down> V \<longleftrightarrow> (\<forall>a B C . (a,B) \<in> R \<and> (a,C) \<in> V \<longrightarrow> B \<subseteq> C)"
proof -
  have "R \<sqsubseteq>\<down> V \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<longrightarrow> (\<exists>C . (a,C) \<in> V \<and> B \<subseteq> C))"
    by (simp add: lower_less_eq)
  also have "... \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<longrightarrow> (\<forall>C . (a,C) \<in> V \<longrightarrow> B \<subseteq> C))"
    by (metis assms deterministic_set)
  finally show ?thesis
    by blast
qed

lemma deterministic_upper:
  assumes "deterministic V"
  shows "V \<sqsubseteq>\<up> R \<longleftrightarrow> (\<forall>a B C . (a,B) \<in> R \<and> (a,C) \<in> V \<longrightarrow> C \<subseteq> B)"
proof -
  have "V \<sqsubseteq>\<up> R \<longleftrightarrow> (\<forall>a C . (a,C) \<in> R \<longrightarrow> (\<exists>B . (a,B) \<in> V \<and> B \<subseteq> C))"
    by (simp add: upper_less_eq)
  also have "... \<longleftrightarrow> (\<forall>a C . (a,C) \<in> R \<longrightarrow> (\<forall>B . (a,B) \<in> V \<longrightarrow> B \<subseteq> C))"
    by (metis assms deterministic_set)
  finally show ?thesis
    by blast
qed

lemma deterministic_iu_closed:
  "deterministic R \<Longrightarrow> deterministic S \<Longrightarrow> deterministic (R \<union>\<union> S)"
  by (simp add: deterministic_def univalent_iu_closed total_iu_closed)

lemma deterministic_ii_closed:
  "deterministic R \<Longrightarrow> deterministic S \<Longrightarrow> deterministic (R \<inter>\<inter> S)"
  by (simp add: deterministic_def univalent_ii_closed total_ii_closed)

lemma total_univalent_lower_implies_upper:
  assumes "total T"
    and "univalent S"
    and "T \<sqsubseteq>\<down> S"
  shows "T \<sqsubseteq>\<up> S"
  by (simp add: assms total_univalent_lower_iu upper_ii_upper_bound)

lemma total_univalent_lower_implies_convex:
  assumes "total T"
    and "univalent S"
    and "T \<sqsubseteq>\<down> S"
  shows "T \<sqsubseteq>\<updown> S"
  by (simp add: assms total_univalent_lower_implies_upper)

lemma total_univalent_upper_implies_lower:
  assumes "total T"
    and "univalent S"
    and "S \<sqsubseteq>\<up> T"
  shows "S \<sqsubseteq>\<down> T"
proof (clarsimp simp: mr_simp)
  fix a B
  assume 1: "(a,B) \<in> S"
  from this obtain C where 2: "(a,C) \<in> T"
    by (meson assms(1) total_set)
  hence "(a,C) \<in> S\<up>"
    using assms(3) by auto
  from this obtain D where 3: "(a,D) \<in> S \<and> D \<subseteq> C"
    using 2 by (meson assms(3) upper_less_eq)
  hence "D = B"
    using 1 by (meson assms(2) univalent_set)
  thus "\<exists>C . (\<exists>D . B = C \<inter> D) \<and> (a,C) \<in> T"
    using 2 3 by (metis Int_absorb1)
qed

lemma total_univalent_upper_implies_convex:
  assumes "total T"
    and "univalent S"
    and "S \<sqsubseteq>\<up> T"
  shows "S \<sqsubseteq>\<updown> T"
  by (simp add: assms total_univalent_upper_implies_lower)

lemma deterministic_lower_upper:
  assumes "deterministic T"
    and "deterministic S"
  shows "S \<sqsubseteq>\<down> T \<longleftrightarrow> S \<sqsubseteq>\<up> T"
  by (meson assms deterministic_def total_univalent_lower_implies_convex total_univalent_upper_implies_lower)

lemma deterministic_lower_convex:
  assumes "deterministic T"
    and "deterministic S"
  shows "S \<sqsubseteq>\<down> T \<longleftrightarrow> S \<sqsubseteq>\<updown> T"
  by (simp add: assms deterministic_lower_upper)

lemma deterministic_upper_convex:
  assumes "deterministic T"
    and "deterministic S"
  shows "S \<sqsubseteq>\<up> T \<longleftrightarrow> S \<sqsubseteq>\<updown> T"
  by (simp add: assms deterministic_lower_upper)

lemma total_down_sp_sp_down:
  assumes "total T"
  shows "R\<down> * T \<subseteq> R * T\<down>"
proof -
  have "R\<down> * T \<subseteq> R * ((1\<^sub>\<union>\<^sub>\<union> \<union> 1) * T)"
    by (simp add: down_sp s_prod_assoc1)
  also have "... = R * (1\<^sub>\<union>\<^sub>\<union> \<union> T * 1)"
    by (simp add: s_prod_distr)
  also have "... = R * (T * 1\<^sub>\<union>\<^sub>\<union> \<union> T * 1)"
    by (metis assms c6 order_antisym_conv total_4)
  also have "... \<subseteq> R * (T * (1\<^sub>\<union>\<^sub>\<union> \<union> 1))"
    by (metis down_sp le_supI s_prod_isor sp_iu_unit_lower sup_ge2)
  also have "... = R * T\<down>"
    by (simp add: down_sp)
  finally show ?thesis
    by simp
qed

lemma total_down_sp_semi_commute:
  "total T \<Longrightarrow> R\<down> * T \<subseteq> (R * T)\<down>"
  by (simp add: down_dist_sp total_down_sp_sp_down)

lemma total_down_dist_sp:
  "total T \<Longrightarrow> (R * T)\<down> = R\<down> * T\<down>"
  by (smt (verit, best) down_dist_sp equalityI ii_assoc ii_isotone lower_reflexive s_prod_isol top_down total_down_sp_semi_commute)

lemma univalent_ic_closed:
  "univalent R \<longleftrightarrow> univalent (\<sim>R)"
  apply (unfold univalent_set)
  apply (clarsimp simp: mr_simp)
  by (metis double_compl)

lemma total_ic_closed:
  "total R \<longleftrightarrow> total (\<sim>R)"
  by (metis total_dom d_def_expl domain_up_down_conjugate equalityI ic_down ic_top ic_up ii_commute inf.orderE lower_ic_upper top_down top_lower_greatest total_lower total_upper_ii)

lemma deterministic_ic_closed:
  "deterministic R \<longleftrightarrow> deterministic (\<sim>R)"
  by (meson deterministic_def total_ic_closed univalent_ic_closed)

lemma iu_unit_deterministic:
  "deterministic (1\<^sub>\<union>\<^sub>\<union>)"
  by (metis Lambda_empty det_lambda)

lemma ii_unit_deterministic:
  "deterministic (1\<^sub>\<inter>\<^sub>\<inter>)"
  using deterministic_ic_closed iu_unit_deterministic by force

lemma univalent_upper_iu:
  assumes "univalent R"
  shows "(R \<sqsubseteq>\<up> S) \<longleftrightarrow> (R \<union>\<union> S = S)"
proof -
  have 1: "R \<union>\<union> S = S \<Longrightarrow> R \<sqsubseteq>\<up> S"
    using upper_iu_increasing by blast
  have 2: "R \<sqsubseteq>\<up> S \<Longrightarrow> S \<subseteq> R \<union>\<union> S"
    by (simp add: upper_ii_upper_bound)
  have "R \<sqsubseteq>\<up> S \<Longrightarrow> R \<union>\<union> S \<subseteq> S"
    apply (clarsimp simp: mr_simp)
    by (smt (verit) Ball_Collect assms case_prodD le_iff_sup subset_refl sup.bounded_iff univalent_set)
  thus ?thesis
    using 1 2 by blast
qed

lemma univalent_lower_ii:
  assumes "univalent S"
  shows "(R \<sqsubseteq>\<down> S) = (R \<inter>\<inter> S = R)"
  apply (clarsimp simp: mr_simp)
  apply safe
    apply (smt (z3) CollectD CollectI Collect_cong Int_iff assms case_prodD inf_set_def subsetD univalent_set)
   apply blast
  by (smt (verit, ccfv_threshold) CollectD Pair_inject case_prodE inf_commute)

subsection \<open>Equivalences induced by powerdomain preorders\<close>

abbreviation lower_eq :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> bool" (infixl "=\<down>" 50) where
  "R =\<down> S \<equiv> R \<sqsubseteq>\<down> S \<and> S \<sqsubseteq>\<down> R"

abbreviation upper_eq :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> bool" (infixl "=\<up>" 50) where
  "R =\<up> S \<equiv> R \<sqsubseteq>\<up> S \<and> S \<sqsubseteq>\<up> R"

abbreviation convex_eq :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> bool" (infixl "=\<updown>" 50) where
  "R =\<updown> S \<equiv> R \<sqsubseteq>\<updown> S \<and> S \<sqsubseteq>\<updown> R"

lemma Convex_eq:
  "R =\<updown> S \<equiv> R \<sqsubseteq>\<Updown> S \<and> S \<sqsubseteq>\<Updown> R"
  by (smt (z3) semilattice_inf_class.le_inf_iff)

lemma convex_lower_upper:
  "R =\<updown> S \<longleftrightarrow> R =\<down> S \<and> R =\<up> S"
  by auto

lemma lower_eq_down:
  "R =\<down> S \<longleftrightarrow> R\<down> = S\<down>"
  using down_idempotent down_lower_isotone lower_reflexive by blast

lemma upper_eq_up:
  "R =\<up> S \<longleftrightarrow> R\<up> = S\<up>"
  by (metis p_prod_comm upclosed_ext upper_ii_up)

lemma convex_eq_convex:
  "R =\<updown> S \<longleftrightarrow> R\<updown> = S\<updown>"
  by (metis Convex_lower_upper lower_eq_down upper_eq_up)

lemma lower_eq:
  "R =\<down> S \<longleftrightarrow> (\<forall>a B . (\<exists>C . (a,C) \<in> R \<and> B \<subseteq> C) \<longleftrightarrow> (\<exists>C . (a,C) \<in> S \<and> B \<subseteq> C))"
  by (meson lower_less_eq order_refl order_trans)

lemma upper_eq:
  "R =\<up> S \<longleftrightarrow> (\<forall>a C . (\<exists>B . (a,B) \<in> R \<and> B \<subseteq> C) \<longleftrightarrow> (\<exists>B . (a,B) \<in> S \<and> B \<subseteq> C))"
  by (meson order_refl order_trans upper_less_eq)

lemma lower_eq_reflexive:
  "R =\<down> R"
  by (simp add: lower_reflexive)

lemma upper_eq_reflexive:
  "R =\<up> R"
  by (simp add: upper_reflexive)

lemma convex_eq_reflexive:
  "R =\<updown> R"
  by (simp add: lower_reflexive upper_reflexive)

lemma lower_eq_symmetric:
  "R =\<down> S \<Longrightarrow> S =\<down> R"
  by simp

lemma upper_eq_symmetric:
  "R =\<up> S \<Longrightarrow> S =\<up> R"
  by simp

lemma convex_eq_symmetric:
  "R =\<updown> S \<Longrightarrow> S =\<updown> R"
  by simp

lemma lower_eq_transitive:
  "R =\<down> S \<Longrightarrow> S =\<down> T \<Longrightarrow> R =\<down> T"
  using lower_transitive by auto

lemma upper_eq_transitive:
  "R =\<up> S \<Longrightarrow> S =\<up> T \<Longrightarrow> R =\<up> T"
  using upper_transitive by auto

lemma convex_eq_transitive:
  "R =\<updown> S \<Longrightarrow> S =\<updown> T \<Longrightarrow> R =\<updown> T"
  by (meson lower_transitive upper_transitive)

lemma ou_lower_eq_left_congruence:
  "R =\<down> S \<Longrightarrow> R \<union> T =\<down> S \<union> T"
  using ou_lower_left_isotone by blast

lemma ou_upper_eq_left_congruence:
  "R =\<up> S \<Longrightarrow> R \<union> T =\<up> S \<union> T"
  using ou_upper_left_isotone by blast

lemma ou_convex_eq_left_congruence:
  "R =\<updown> S \<Longrightarrow> R \<union> T =\<updown> S \<union> T"
  by (meson ou_lower_left_isotone ou_upper_left_isotone)

lemma ou_lower_eq_right_congruence:
  "R =\<down> S \<Longrightarrow> T \<union> R =\<down> T \<union> S"
  using ou_lower_right_isotone by blast

lemma ou_upper_eq_right_congruence:
  "R =\<up> S \<Longrightarrow> T \<union> R =\<up> T \<union> S"
  using ou_upper_right_isotone by blast

lemma ou_convex_eq_right_congruence:
  "R =\<updown> S \<Longrightarrow> T \<union> R =\<updown> T \<union> S"
  by (meson ou_lower_right_isotone ou_upper_right_isotone)

lemma ou_lower_eq_congruence:
  "R =\<down> S \<Longrightarrow> P =\<down> Q \<Longrightarrow> R \<union> P =\<down> S \<union> Q"
  using ou_lower_isotone by blast

lemma ou_upper_eq_congruence:
  "R =\<up> S \<Longrightarrow> P =\<up> Q \<Longrightarrow> R \<union> P =\<up> S \<union> Q"
  using ou_upper_isotone by blast

lemma ou_convex_eq_congruence:
  "R =\<updown> S \<Longrightarrow> P =\<updown> Q \<Longrightarrow> R \<union> P =\<updown> S \<union> Q"
  by (meson ou_lower_isotone ou_upper_isotone)

lemma iu_lower_eq_left_congruence:
  "R =\<down> S \<Longrightarrow> R \<union>\<union> T =\<down> S \<union>\<union> T"
  using iu_lower_left_isotone by blast

lemma iu_upper_eq_left_congruence:
  "R =\<up> S \<Longrightarrow> R \<union>\<union> T =\<up> S \<union>\<union> T"
  using iu_upper_left_isotone by blast

lemma iu_convex_eq_left_congruence:
  "R =\<updown> S \<Longrightarrow> R \<union>\<union> T =\<updown> S \<union>\<union> T"
  by (simp add: iu_lower_left_isotone iu_upper_left_isotone)

lemma iu_lower_eq_right_congruence:
  "R =\<down> S \<Longrightarrow> T \<union>\<union> R =\<down> T \<union>\<union> S"
  using iu_lower_right_isotone by blast

lemma iu_upper_eq_right_congruence:
  "R =\<up> S \<Longrightarrow> T \<union>\<union> R =\<up> T \<union>\<union> S"
  using iu_upper_right_isotone by blast

lemma iu_convex_eq_right_congruence:
  "R =\<updown> S \<Longrightarrow> T \<union>\<union> R =\<updown> T \<union>\<union> S"
  by (simp add: iu_lower_right_isotone iu_upper_right_isotone)

lemma iu_lower_eq_congruence:
  "R =\<down> S \<Longrightarrow> P =\<down> Q \<Longrightarrow> R \<union>\<union> P =\<down> S \<union>\<union> Q"
  using iu_lower_isotone by blast

lemma iu_upper_eq_congruence:
  "R =\<up> S \<Longrightarrow> P =\<up> Q \<Longrightarrow> R \<union>\<union> P =\<up> S \<union>\<union> Q"
  using iu_upper_isotone by blast

lemma iu_convex_eq_congruence:
  "R =\<updown> S \<Longrightarrow> P =\<updown> Q \<Longrightarrow> R \<union>\<union> P =\<updown> S \<union>\<union> Q"
  by (simp add: iu_lower_isotone iu_upper_isotone)

lemma ii_lower_eq_left_congruence:
  "R =\<down> S \<Longrightarrow> R \<inter>\<inter> T =\<down> S \<inter>\<inter> T"
  using ii_lower_left_isotone by blast

lemma ii_upper_eq_left_congruence:
  "R =\<up> S \<Longrightarrow> R \<inter>\<inter> T =\<up> S \<inter>\<inter> T"
  using ii_upper_left_isotone by blast

lemma ii_convex_eq_left_congruence:
  "R =\<updown> S \<Longrightarrow> R \<inter>\<inter> T =\<updown> S \<inter>\<inter> T"
  by (simp add: ii_lower_left_isotone ii_upper_left_isotone)

lemma ii_lower_eq_right_congruence:
  "R =\<down> S \<Longrightarrow> T \<inter>\<inter> R =\<down> T \<inter>\<inter> S"
  using ii_lower_right_isotone by blast

lemma ii_upper_eq_right_congruence:
  "R =\<up> S \<Longrightarrow> T \<inter>\<inter> R =\<up> T \<inter>\<inter> S"
  using ii_upper_right_isotone by blast

lemma ii_convex_eq_right_congruence:
  "R =\<updown> S \<Longrightarrow> T \<inter>\<inter> R =\<updown> T \<inter>\<inter> S"
  by (simp add: ii_lower_right_isotone ii_upper_right_isotone)

lemma ii_lower_eq_congruence:
  "R =\<down> S \<Longrightarrow> P =\<down> Q \<Longrightarrow> R \<inter>\<inter> P =\<down> S \<inter>\<inter> Q"
  using ii_lower_isotone by blast

lemma ii_upper_eq_congruence:
  "R =\<up> S \<Longrightarrow> P =\<up> Q \<Longrightarrow> R \<inter>\<inter> P =\<up> S \<inter>\<inter> Q"
  using ii_upper_isotone by blast

lemma ii_convex_eq_congruence:
  "R =\<updown> S \<Longrightarrow> P =\<updown> Q \<Longrightarrow> R \<inter>\<inter> P =\<updown> S \<inter>\<inter> Q"
  by (simp add: ii_lower_isotone ii_upper_isotone)

lemma sp_lower_eq_left_congruence:
  "R =\<down> S \<Longrightarrow> T * R =\<down> T * S"
  by (simp add: sp_lower_left_isotone)

lemma sp_upper_eq_left_congruence:
  "R =\<up> S \<Longrightarrow> T * R =\<up> T * S"
  by (simp add: sp_upper_left_isotone)

lemma sp_convex_eq_left_congruence:
  "R =\<updown> S \<Longrightarrow> T * R =\<updown> T * S"
  by (simp add: sp_lower_left_isotone sp_upper_left_isotone)

lemma cp_lower_eq_left_congruence:
  "R =\<down> S \<Longrightarrow> T \<odot> R =\<down> T \<odot> S"
  by (simp add: cp_lower_left_isotone)

lemma cp_upper_eq_left_congruence:
  "R =\<up> S \<Longrightarrow> T \<odot> R =\<up> T \<odot> S"
  by (simp add: cp_upper_left_isotone)

lemma cp_convex_eq_left_congruence:
  "R =\<updown> S \<Longrightarrow> T \<odot> R =\<updown> T \<odot> S"
  by (simp add: cp_lower_left_isotone cp_upper_left_isotone)

lemma lower_eq_ic_upper:
  "R =\<down> S \<longleftrightarrow> \<sim>R =\<up> \<sim>S"
  using lower_ic_upper by auto

lemma upper_eq_ic_lower:
  "R =\<up> S \<longleftrightarrow> \<sim>R =\<down> \<sim>S"
  using upper_ic_lower by auto

lemma convex_eq_ic_lower:
  "R =\<updown> S \<longleftrightarrow> \<sim>R =\<updown> \<sim>S"
  by (meson lower_ic_upper upper_ic_lower)

lemma up_lower_eq_congruence:
  "R =\<down> S \<Longrightarrow> R\<up> =\<down> S\<up>"
  by (fact iu_lower_eq_left_congruence)

lemma up_upper_eq_congruence:
  "R =\<up> S \<Longrightarrow> R\<up> =\<up> S\<up>"
  by (fact iu_upper_eq_left_congruence)

lemma up_convex_eq_congruence:
  "R =\<updown> S \<Longrightarrow> R\<up> =\<updown> S\<up>"
  by (fact iu_convex_eq_left_congruence)

lemma down_lower_eq_congruence:
  "R =\<down> S \<Longrightarrow> R\<down> =\<down> S\<down>"
  by (fact ii_lower_eq_left_congruence)

lemma down_upper_eq_congruence:
  "R =\<up> S \<Longrightarrow> R\<down> =\<up> S\<down>"
  by (fact ii_upper_eq_left_congruence)

lemma down_convex_eq_congruence:
  "R =\<updown> S \<Longrightarrow> R\<down> =\<updown> S\<down>"
  by (fact ii_convex_eq_left_congruence)

lemma convex_lower_eq_congruence:
  "R =\<down> S \<Longrightarrow> R\<updown> =\<down> S\<updown>"
  by (simp add: convex_lower_isotone)

lemma convex_upper_eq_congruence:
  "R =\<up> S \<Longrightarrow> R\<updown> =\<up> S\<updown>"
  by (simp add: convex_upper_isotone)

lemma convex_convex_eq_congruence:
  "R =\<updown> S \<Longrightarrow> R\<updown> =\<updown> S\<updown>"
  by (simp add: convex_lower_isotone convex_upper_isotone)

lemma univalent_lower_eq_subset:
  assumes "univalent S"
    and "S =\<down> R"
  shows "S \<subseteq> R"
proof -
  have 1: "\<forall>a B C. (a, B) \<in> S \<and> (a, C) \<in> S \<longrightarrow> B = C"
    using assms(1) by (simp add: univalent_set)
  have "\<forall>a B. (\<exists>A. (a,A) \<in> S \<and> B \<subseteq> A) = (\<exists>A. (a,A) \<in> R \<and> B \<subseteq> A)"
    by (meson assms(2) lower_eq)
  hence "\<forall>a B. (a,B) \<in> S \<longrightarrow> (a,B) \<in> R"
    using 1 by (smt (verit, del_insts) assms(2) lower_less_eq subset_antisym)
  thus ?thesis
    by (simp add: subset_iff)
qed

lemma univalent_lower_eq:
  assumes "univalent R"
    and "univalent S"
    and "R =\<down> S"
  shows "R = S"
  by (meson assms subset_antisym univalent_lower_eq_subset)

lemma univalent_lower_eq_iff:
  assumes "univalent R"
    and "univalent S"
  shows "(R =\<down> S) \<longleftrightarrow> (R = S)"
  using assms lower_reflexive univalent_lower_eq by auto

lemma univalent_upper_eq_subset:
  assumes "univalent S"
    and "S =\<up> R"
  shows "S \<subseteq> R"
proof -
  have 1: "\<forall>a B C. (a, B) \<in> S \<and> (a, C) \<in> S \<longrightarrow> B = C"
    using assms(1) by (simp add: univalent_set)
  have "\<forall>a B. (\<exists>A. (a,A) \<in> S \<and> A \<subseteq> B) = (\<exists>A. (a,A) \<in> R \<and> A \<subseteq> B)"
    by (meson assms(2) upper_eq)
  hence "\<forall>a B. (a,B) \<in> S \<longrightarrow> (a,B) \<in> R"
    using 1 by (smt (verit) order_refl subset_antisym)
  thus ?thesis
    by (simp add: subset_iff)
qed

lemma univalent_upper_eq:
  assumes "univalent R"
    and "univalent S"
    and "R =\<up> S"
  shows "R = S"
  by (meson assms subset_antisym univalent_upper_eq_subset)

lemma univalent_upper_eq_iff:
  assumes "univalent R"
    and "univalent S"
  shows "(R =\<up> S) \<longleftrightarrow> (R = S)"
  using assms univalent_upper_eq upclosed_ext by blast

lemma univalent_convex_eq_iff:
  assumes "univalent R"
    and "univalent S"
  shows "(R =\<updown> S) \<longleftrightarrow> (R = S)"
  by (metis assms univalent_lower_eq_iff univalent_upper_eq_iff)

lemma total_univalent_upper_ii:
  assumes "total T"
    and "univalent S"
    and "S \<sqsubseteq>\<up> T"
  shows "T \<inter>\<inter> S = S"
  apply (rule antisym)
   apply (metis assms(2,3) ii_left_isotone univalent_up_ii_idempotent)
  by (metis assms ii_commute lower_ii_lower_bound total_univalent_upper_implies_lower)

lemma lower_eq_down_closed:
  "R =\<down> R\<down>"
  by (simp add: subset_lower)

lemma upper_eq_up_closed:
  "R =\<up> R\<up>"
  by (simp add: subset_upper)

lemma convex_eq_up_closed:
  "R =\<updown> R\<updown>"
  by (simp add: subset_lower subset_upper)

lemma lower_join:
  "(\<forall>P . Q \<sqsubseteq>\<down> P \<longleftrightarrow> R \<sqsubseteq>\<down> P \<and> S \<sqsubseteq>\<down> P) \<longleftrightarrow> Q =\<down> R \<union> S"
  by (meson Un_subset_iff lower_reflexive lower_transitive)

lemma lower_meet:
  "(\<forall>P . P \<sqsubseteq>\<down> Q \<longleftrightarrow> P \<sqsubseteq>\<down> R \<and> P \<sqsubseteq>\<down> S) \<longleftrightarrow> Q =\<down> R \<inter>\<inter> S"
  by (metis (no_types, lifting) down_dist_ii_oi le_inf_iff lower_eq_down lower_reflexive)

lemma upper_join:
  "(\<forall>P . Q \<sqsubseteq>\<up> P \<longleftrightarrow> R \<sqsubseteq>\<up> P \<and> S \<sqsubseteq>\<up> P) \<longleftrightarrow> Q =\<up> R \<union>\<union> S"
  by (metis (no_types, lifting) convex_increasing le_inf_iff up_dist_iu_oi upper_eq_up)

lemma upper_meet:
  "(\<forall>P . P \<sqsubseteq>\<up> Q \<longleftrightarrow> P \<sqsubseteq>\<up> R \<and> P \<sqsubseteq>\<up> S) \<longleftrightarrow> Q =\<up> R \<union> S"
  by (meson Un_subset_iff upper_reflexive upper_transitive)

lemma lower_ii_idempotent:
  "R \<inter>\<inter> R =\<down> R"
  using ii_down lower_reflexive by blast

lemma upper_iu_idempotent:
  "R \<union>\<union> R =\<up> R"
  using iu_up upper_reflexive by auto

lemma lower_iI_idempotent:
  "I \<noteq> {} \<Longrightarrow> (\<Inter>\<Inter>(\<lambda>j . R)|I) =\<down> R"
  by (metis iI_down lower_eq_down)

lemma upper_iU_idempotent:
  "I \<noteq> {} \<Longrightarrow> (\<Union>\<Union>(\<lambda>j . R)|I) =\<up> R"
  by (metis iU_up upper_eq_up)

lemma down_closed_intersection_closed:
  "R = R\<down> \<Longrightarrow> \<forall>I . I \<noteq> {} \<longrightarrow> (\<Inter>\<Inter>(\<lambda>j . R)|I) \<subseteq> R"
  by (metis lower_iI_idempotent)

lemma up_closed_union_closed:
  "R = R\<up> \<Longrightarrow> \<forall>I . I \<noteq> {} \<longrightarrow> (\<Union>\<Union>(\<lambda>j . R)|I) \<subseteq> R"
  by (metis upper_iU_idempotent)

lemma ou_down_lower_eq_ou:
  "R\<down> \<union> S\<down> =\<down> R \<union> S"
  using down_dist_ou lower_eq_down_closed by blast

lemma oi_down_lower_eq_ii:
  "R\<down> \<inter> S\<down> =\<down> R \<inter>\<inter> S"
  by (simp add: down_dist_ii_oi lower_reflexive)

lemma ou_up_upper_eq_ou:
  "R\<up> \<union> S\<up> =\<up> R \<union> S"
  by (metis ou_upper_isotone up_idempotent upper_reflexive)

lemma oi_up_upper_eq_iu:
  "R\<up> \<inter> S\<up> =\<up> R \<union>\<union> S"
  by (simp add: up_dist_iu_oi upper_reflexive)

lemma oU_down_lower_eq_oU:
  "(\<Union>R\<in>X . R\<down>) =\<down> \<Union>X"
  by (metis down_dist_oU lower_eq_down_closed)

lemma oI_down_lower_eq_iI:
  "(\<Inter>i\<in>I . X i\<down>) =\<down> \<Inter>\<Inter>X|I"
  apply safe
  using down_dist_iI_oI apply fastforce
  by (metis (no_types, lifting) down_dist_iI_oI image_cong image_image lower_eq_down subsetD)

lemma oU_up_upper_eq_oU:
  "(\<Union>R\<in>X . R\<up>) =\<up> \<Union>X"
  by (metis up_dist_oU upper_eq_up_closed)

lemma oI_up_upper_eq_iI:
  "(\<Inter>i\<in>I . X i\<up>) =\<up> \<Union>\<Union>X|I"
  by (smt (z3) INT_extend_simps(10) Sup.SUP_cong U_par_idem p_prod_assoc p_prod_comm top_upper_least up_dist_iU_oI upper_ii_upper_bound)

lemma down_order_lower:
  "R\<down> \<subseteq> S\<down> \<longleftrightarrow> R \<sqsubseteq>\<down> S"
  by (meson lower_eq_down_closed lower_transitive)

lemma up_order_upper:
  "R\<up> \<subseteq> S\<up> \<longleftrightarrow> S \<sqsubseteq>\<up> R"
  by (meson upper_eq_up_closed upper_transitive)

lemma convex_order_lower_upper:
  "R\<updown> \<subseteq> S\<updown> \<longleftrightarrow> R \<sqsubseteq>\<down> S \<and> S \<sqsubseteq>\<up> R"
  by (meson convex_eq_up_closed le_inf_iff lower_transitive upper_transitive)

lemma convex_order_Convex:
  "R\<updown> \<subseteq> S\<updown> \<longleftrightarrow> R \<sqsubseteq>\<Updown> S"
  by (meson Convex_lower_upper convex_order_lower_upper)

section \<open>Fusion and Fission\<close>

subsection \<open>Atoms and co-atoms\<close>

definition atoms :: "('a,'b) mrel" ("A\<^sub>\<union>\<^sub>\<union>")
  where "A\<^sub>\<union>\<^sub>\<union> \<equiv> { (a,{b}) | a b . True }"

definition co_atoms :: "('a,'b) mrel" ("A\<^sub>\<inter>\<^sub>\<inter>")
  where "A\<^sub>\<inter>\<^sub>\<inter> \<equiv> { (a,UNIV - {b}) | a b . True }"

declare atoms_def [mr_simp] co_atoms_def [mr_simp]

lemma atoms_solution:
  "A\<^sub>\<union>\<^sub>\<union>\<up> = -1\<^sub>\<union>\<^sub>\<union>"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
  apply (clarsimp simp: mr_simp)
  by (metis equals0I insert_is_Un mk_disjoint_insert)

lemma atoms_least_solution:
  assumes "R\<up> = -1\<^sub>\<union>\<^sub>\<union>"
  shows "A\<^sub>\<union>\<^sub>\<union> \<subseteq> R"
proof
  fix x :: "'a \<times> 'b set"
  assume 1: "x \<in> A\<^sub>\<union>\<^sub>\<union>"
  from this obtain a b where 2: "x = (a,{b})"
    by (smt CollectD atoms_def)
  have 3: "x \<in> R\<up>"
    using 1 assms atoms_solution upper_reflexive by fastforce
  have "(a,{}) \<notin> R\<up>"
    by (metis ComplD IntE U_c U_par_idem assms domain_pointwise p_prod_assoc up_dist_iu_oi)
  thus "x \<in> R"
    using 2 3 by (smt (verit) U_par_st subsetD subset_singletonD upclosed_ext)
qed

lemma ic_atoms:
  "\<sim>A\<^sub>\<union>\<^sub>\<union> = A\<^sub>\<inter>\<^sub>\<inter>"
  apply (clarsimp simp: mr_simp)
  by fastforce

lemma ic_co_atoms:
  "\<sim>A\<^sub>\<inter>\<^sub>\<inter> = A\<^sub>\<union>\<^sub>\<union>"
  by (metis ic_atoms ic_involutive)

lemma co_atoms_solution:
  "A\<^sub>\<inter>\<^sub>\<inter>\<down> = -1\<^sub>\<inter>\<^sub>\<inter>"
  by (metis atoms_solution ic_atoms ic_dist_oc ic_iu_unit ic_up)

lemma co_atoms_least_solution:
  assumes "R\<down> = -1\<^sub>\<inter>\<^sub>\<inter>"
  shows "A\<^sub>\<inter>\<^sub>\<inter> \<subseteq> R"
  by (metis assms atoms_least_solution ic_atoms ic_dist_oc ic_down ic_ii_unit ic_involutive ic_isotone)

lemma iu_unit_atoms_disjoint:
  "1\<^sub>\<union>\<^sub>\<union> \<inter> A\<^sub>\<union>\<^sub>\<union> = {}"
  by (metis Compl_disjoint atoms_solution iu_unit_down oi_down_up_iff)

lemma ii_unit_co_atoms_disjoint:
  "1\<^sub>\<inter>\<^sub>\<inter> \<inter> A\<^sub>\<inter>\<^sub>\<inter> = {}"
  using co_atoms_solution lower_reflexive by fastforce

lemma atoms_sp_idempotent:
  "A\<^sub>\<union>\<^sub>\<union> * A\<^sub>\<union>\<^sub>\<union> = A\<^sub>\<union>\<^sub>\<union>"
  by (auto simp: mr_simp)

lemma atoms_sp_cp:
  "(R \<inter> A\<^sub>\<union>\<^sub>\<union>) * S = (R \<inter> A\<^sub>\<union>\<^sub>\<union>) \<odot> S"
  by (auto simp: mr_simp)

subsection \<open>Inner-functional properties\<close>

abbreviation inner_univalent :: "('a,'b) mrel \<Rightarrow> bool" where
  "inner_univalent R \<equiv> R \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<union> A\<^sub>\<union>\<^sub>\<union>"

abbreviation inner_total :: "('a,'b) mrel \<Rightarrow> bool" where
  "inner_total R \<equiv> R \<subseteq> -1\<^sub>\<union>\<^sub>\<union>"

abbreviation inner_deterministic :: "('a,'b) mrel \<Rightarrow> bool" where
  "inner_deterministic R \<equiv> inner_total R \<and> inner_univalent R"

lemma inner_deterministic_atoms:
  "inner_deterministic R \<longleftrightarrow> R \<subseteq> A\<^sub>\<union>\<^sub>\<union>"
  using atoms_solution upper_reflexive by fastforce

lemma inner_univalent:
  "inner_univalent R \<longleftrightarrow> (\<forall>a b c B . (a,B) \<in> R \<and> b \<in> B \<and> c \<in> B \<longrightarrow> b = c)"
  apply (clarsimp simp: mr_simp, safe)
   apply blast
  by (smt (z3) UNIV_I UN_iff equals0I insertI1 insert_absorb singleton_insert_inj_eq' subsetI)

lemma inner_univalent_2:
  "inner_univalent R \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<longrightarrow> finite B \<and> card B \<le> one_class.one)"
  apply (rule iffI)
   apply (metis card_eq_0_iff finite.emptyI inner_univalent is_singletonI' is_singleton_altdef linear nonempty_set_card)
  by (metis all_not_in_conv card_1_singletonE eq_iff inner_univalent nonempty_set_card singletonD)

lemma inner_total:
  "inner_total R \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<longrightarrow> (\<exists>b . b \<in> B))"
  apply (rule iffI)
   apply (smt (verit, del_insts) Collect_empty_eq all_not_in_conv disjoint_eq_subset_Compl p_id_zero_st)
  by (smt (verit) Collect_empty_eq disjoint_eq_subset_Compl ex_in_conv p_id_zero_st)

lemma inner_total_2:
  "inner_total R \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<longrightarrow> B \<noteq> {})"
  by (meson all_not_in_conv inner_total)

lemma inner_total_3:
  "inner_total R \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<and> finite B \<longrightarrow> card B \<ge> one_class.one)"
  by (metis finite.emptyI inner_total_2 nonempty_set_card)

lemma inner_deterministic:
  "inner_deterministic R \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<longrightarrow> (\<exists>!b . b \<in> B))"
  by (metis (no_types, lifting) inner_total inner_univalent)

lemma inner_deterministic_2:
  "inner_deterministic R \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<longrightarrow> card B = one_class.one)"
  by (metis card_1_singletonE eq_iff finite.emptyI finite_insert inner_total_3 inner_univalent_2)

lemma inner_deterministic_sp_unit:
  "inner_deterministic 1"
  by (simp add: inner_deterministic s_id_def)

lemma inner_univalent_down:
  assumes "inner_univalent S"
  shows "S\<down> \<subseteq> S \<union> 1\<^sub>\<union>\<^sub>\<union>"
  using assms by (auto simp: mr_simp)

lemma inner_deterministic_lower_eq:
  assumes "inner_deterministic V"
    and "inner_deterministic W"
    and "V =\<down> W"
  shows "V = W"
  using assms inner_univalent_down by blast

lemma inner_total_down_closed:
  "inner_total T \<Longrightarrow> R \<subseteq> T \<Longrightarrow> inner_total R"
  by simp

lemma inner_univalent_down_closed:
  "inner_univalent T \<Longrightarrow> R \<subseteq> T \<Longrightarrow> inner_univalent R"
  by simp

lemma inner_deterministic_down_closed:
  "inner_deterministic T \<Longrightarrow> R \<subseteq> T \<Longrightarrow> inner_deterministic R"
  by blast

lemma inner_univalent_convex:
  assumes "inner_univalent R"
  shows "R = R\<updown>"
  apply (rule antisym)
  using convex_increasing apply blast
  apply (clarsimp simp: mr_simp)
  by (smt (verit) Un_Int_eq(2) Un_Int_eq(3) assms boolean_algebra_cancel.sup0 disjoint_iff inner_univalent semilattice_inf_class.inf.orderE subsetI)

lemma inner_deterministic_alt_closure:
  "inner_deterministic R = (R O converse 1 O 1 = R)"
  apply (clarsimp simp: mr_simp)
  apply safe
    apply force
  by blast+

lemma inner_deterministic_s_id_conv_epsiloff:
  "inner_deterministic R \<Longrightarrow> R O converse s_id = R O epsiloff"
  apply (clarsimp simp: mr_simp)
  unfolding epsiloff_def
  by blast

lemma inner_deterministic_lower_iff:
  assumes "inner_deterministic R"
    and "inner_deterministic S"
  shows "(R \<sqsubseteq>\<down> S) \<longleftrightarrow> (R \<subseteq> S)"
  apply standard
   apply (smt (verit, ccfv_threshold) Un_commute assms disjoint_eq_subset_Compl inf.orderE inf.orderI inf_commute inf_sup_distrib2 inner_univalent_down sup.orderE sup_bot_left)
  by (simp add: subset_lower)

lemma inner_deterministic_upper_iff:
  assumes "inner_deterministic R"
    and "inner_deterministic S"
  shows "(R \<sqsubseteq>\<up> S) \<longleftrightarrow> (S \<subseteq> R)"
  apply standard
   apply (clarsimp simp: mr_simp)
  using inner_deterministic apply (smt (verit, del_insts) Ball_Collect Un_subset_iff assms case_prodD subsetD subsetI subset_antisym)
  by (simp add: subset_upper)

lemma inner_deterministic_lower_eq_iff:
  assumes "inner_deterministic R"
    and "inner_deterministic S"
  shows "(R =\<down> S) \<longleftrightarrow> (R = S)"
  by (meson assms inner_deterministic_lower_eq lower_reflexive)

lemma inner_deterministic_upper_eq_iff:
  assumes "inner_deterministic R"
    and "inner_deterministic S"
  shows "(R =\<up> S) \<longleftrightarrow> (R = S)"
  by (simp add: antisym assms inner_deterministic_upper_iff)

lemma inner_deterministic_convex_eq_iff:
  assumes "inner_deterministic R"
    and "inner_deterministic S"
  shows "(R =\<updown> S) \<longleftrightarrow> (R = S)"
  by (metis assms inner_deterministic_lower_eq_iff inner_deterministic_upper_eq_iff)

lemma
  "inner_univalent R \<Longrightarrow> inner_univalent S \<Longrightarrow> inner_univalent (R \<union>\<union> S)"
  nitpick[expect=genuine,card=1,2]
  oops

lemma inner_univalent_ii_closed:
  "inner_univalent R \<Longrightarrow> inner_univalent S \<Longrightarrow> inner_univalent (R \<inter>\<inter> S)"
  by (metis (no_types, lifting) Un_subset_iff convex_reflexive down_dist_ii_oi inner_univalent_down inner_univalent_down_closed le_inf_iff subsetI)

lemma inner_total_iu_closed:
  "inner_total R \<Longrightarrow> inner_total S \<Longrightarrow> inner_total (R \<union>\<union> S)"
  by (metis U_par_idem U_par_p_id atoms_solution c_prod_idr iu_upper_isotone s_prod_p_idl top_upper_least)

lemma
  "inner_total R \<Longrightarrow> inner_total S \<Longrightarrow> inner_total (R \<inter>\<inter> S)"
  nitpick[expect=genuine,card=1,2]
  oops

  subsection \<open>Fusion\<close>

lemma fusion_set:
  "fus R \<equiv> { (a,B) . B = \<Union>{ C . (a,C) \<in> R } }"
  unfolding fus_set Image_singleton
  by (smt (verit) Collect_cong Pair_inject case_prodE case_prodI2)

declare fusion_set [mr_simp]

lemma fusion_lower_increasing:
  "R \<sqsubseteq>\<down> fus R"
  apply (clarsimp simp: mr_simp)
  by blast

lemma fusion_deterministic:
  "deterministic (fus R)"
  by (simp add: deterministic_set fusion_set)

lemma fusion_least:
  assumes "R \<sqsubseteq>\<down> S"
    and "deterministic S"
  shows "fus R \<sqsubseteq>\<down> S"
proof (clarsimp simp: mr_simp)
  fix a::'a
  from assms(2) obtain C::"'b set" where 1: "(a,C) \<in> S"
    by (meson deterministic_set)
  hence "\<Union>{ B . (a,B) \<in> R } \<subseteq> C"
    using assms deterministic_lower by (smt (verit, del_insts) Sup_le_iff mem_Collect_eq)
  thus "\<exists>C . (\<exists>D . \<Union>{ B . (a,B) \<in> R } = C \<inter> D) \<and> (a,C) \<in> S"
    using 1 by blast
qed

lemma fusion_unique:
  assumes "\<forall>R . R \<sqsubseteq>\<down> f R"
    and "\<forall>R . deterministic (f R)"
    and "\<forall>R S . R \<sqsubseteq>\<down> S \<and> deterministic S \<longrightarrow> f R \<sqsubseteq>\<down> S"
  shows "f T = fus T"
  apply (rule univalent_lower_eq)
  using assms(2) deterministic_def apply blast
  using deterministic_def fusion_deterministic apply blast
  by (simp add: assms fusion_deterministic fusion_least fusion_lower_increasing)

lemma fusion_down_char:
  "(fus R)\<down> = -((-(R\<down>) \<inter> A\<^sub>\<union>\<^sub>\<union>)\<up>)"
proof
  show "(fus R)\<down> \<subseteq> -((-(R\<down>) \<inter> A\<^sub>\<union>\<^sub>\<union>)\<up>)"
    apply (clarsimp simp: mr_simp)
    by blast
next
  show "-((-(R\<down>) \<inter> A\<^sub>\<union>\<^sub>\<union>)\<up>) \<subseteq> (fus R)\<down>"
  proof (clarsimp simp: mr_simp)
    fix a A
    assume 1: "\<forall>B . (\<forall>C . A \<noteq> B \<union> C) \<or> (\<exists>C . (\<exists>D . B = C \<inter> D) \<and> (a,C) \<in> R) \<or> (\<forall>b . B \<noteq> {b})"
    have "A \<subseteq> \<Union>{ C . (a,C) \<in> R }"
    proof
      fix x
      assume "x \<in> A"
      from this obtain C where "x \<in> C \<and> (a,C) \<in> R"
        using 1 by (metis IntD1 insert_Diff insert_is_Un singletonI)
      thus "x \<in> \<Union>{ C . (a,C) \<in> R }"
        by blast
    qed
    thus "\<exists>D . A = \<Union>{ C . (a,C) \<in> R } \<inter> D"
      by auto
  qed
qed

lemma fusion_up_char:
  "(fus R)\<up> = -((\<sim>(R\<down>) \<inter> A\<^sub>\<inter>\<^sub>\<inter>)\<down>)"
proof
  show "(fus R)\<up> \<subseteq> -((\<sim>(R\<down>) \<inter> A\<^sub>\<inter>\<^sub>\<inter>)\<down>)"
    apply (clarsimp simp: mr_simp)
    by blast
next
  show "-((\<sim>(R\<down>) \<inter> A\<^sub>\<inter>\<^sub>\<inter>)\<down>) \<subseteq> (fus R)\<up>"
  proof (clarsimp simp: mr_simp)
    fix a A
    assume 1: "\<forall>C . (\<forall>D . A \<noteq> C \<inter> D) \<or> (\<forall>B . (\<forall>D . - C \<noteq> B \<inter> D) \<or> (a,B) \<notin> R) \<or> (\<forall>b . C \<noteq> UNIV - {b})"
    have "\<Union>{ C . (a,C) \<in> R } \<subseteq> A"
    proof
      fix x
      assume "x \<in> \<Union>{ C . (a,C) \<in> R }"
      from this obtain C where "x \<in> C \<and> (a,C) \<in> R"
        by blast
      thus "x \<in> A"
        using 1 by (metis Compl_eq_Diff_UNIV Diff_Diff_Int Diff_cancel Diff_eq Diff_insert_absorb Int_commute double_complement insert_Diff insert_inter_insert)
    qed
    thus "\<exists>C . A = \<Union>{ C . (a,C) \<in> R } \<union> C"
      by auto
  qed
qed

lemma fusion_up_char_2:
  "(fus R)\<up> = -(((R\<down> \<inter> A\<^sub>\<union>\<^sub>\<union>) * \<sim>1)\<down>)"
  by (simp add: atoms_sp_cp co_prod fusion_up_char ic_atoms ic_dist_oi)

lemma fusion_char:
  "fus R = -((-(R\<down>) \<inter> A\<^sub>\<union>\<^sub>\<union>)\<up>) \<inter> -((\<sim>(R\<down>) \<inter> A\<^sub>\<inter>\<^sub>\<inter>)\<down>)"
  by (metis deterministic_def fusion_deterministic fusion_down_char fusion_up_char inf_commute univalent_convex)

lemma fusion_char_2:
  "fus R = -((-(R\<down>) \<inter> A\<^sub>\<union>\<^sub>\<union>)\<up>) \<inter> -(((R\<down> \<inter> A\<^sub>\<union>\<^sub>\<union>) * \<sim>1)\<down>)"
  using fusion_char fusion_up_char fusion_up_char_2 by blast

lemma fusion_lower_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> fus R \<sqsubseteq>\<down> fus S"
  by (meson fusion_deterministic fusion_least fusion_lower_increasing lower_transitive)

lemma fusion_iu_idempotent:
  "fus R \<union>\<union> fus R = fus R"
  using deterministic_def fusion_deterministic univalent_iu_idempotent by blast

lemma fusion_down:
  "fus R = fus (R\<down>)"
  by (simp add: fusion_char)

lemma fusion_iu_total:
  "total T \<Longrightarrow> T \<union>\<union> fus T = fus T"
  by (meson deterministic_def fusion_deterministic fusion_lower_increasing total_univalent_lower_iu)

lemma fusion_deterministic_fixpoint:
  "deterministic R \<longleftrightarrow> R = fus R"
  by (metis deterministic_def fusion_deterministic fusion_iu_total fusion_least lower_reflexive p_prod_comm total_univalent_lower_iu)

abbreviation non_empty :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("ne _" [100] 100)
  where "ne R \<equiv> R \<inter> -1\<^sub>\<union>\<^sub>\<union>"

lemma non_empty:
  "ne R = { (a,B) | a B . (a,B) \<in> R \<and> B \<noteq> {} }"
  by (auto simp: mr_simp)

lemma ne_equality:
  "ne R = R \<longleftrightarrow> R \<subseteq> -1\<^sub>\<union>\<^sub>\<union>"
  by blast

lemma ne_dist_ou:
  "ne (R \<union> S) = ne R \<union> ne S"
  by (fact inf_sup_distrib2)

lemma ne_down_idempotent:
  "ne ((ne (R\<down>))\<down>) = ne (R\<down>)"
  by (auto simp: mr_simp)

lemma ne_up:
  "(ne R)\<up> = ne R * 1\<up>"
proof
  show "(ne R)\<up> \<subseteq> ne R * 1\<up>"
    apply (clarsimp simp: mr_simp)
    by (metis UN_constant Un_insert_left insert_absorb)
next
  show "ne R * 1\<up> \<subseteq> (ne R)\<up>"
  proof (clarsimp simp: mr_simp)
    fix a B f
    assume 1: "(a,B) \<in> R" and 2: "B \<noteq> {}" and "\<forall>b\<in>B . \<exists>C . f b = insert b C"
    hence "B \<subseteq> (\<Union>x\<in>B . f x)"
      by blast
    thus "\<exists>D . (\<exists>C . (\<Union>x\<in>B . f x) = D \<union> C) \<and> (a,D) \<in> R \<and> D \<noteq> {}"
      using 1 2 by blast
  qed
qed

lemma ne_dist_down_sp:
  "ne (R\<down> * S) = ne (R\<down>) * ne S"
proof (rule antisym)
  show "ne (R\<down> * S) \<subseteq> ne (R\<down>) * ne S"
  proof (clarsimp simp: mr_simp)
    fix a C f D x
    assume 1: "(a,C) \<in> R" and 2: "\<forall>b\<in>C\<inter>D . (b,f b) \<in> S" and 3: "f x \<noteq> {}" and 4: "x \<in> C" and 5: "x \<in> D"
    let ?B = "{ b\<in>C\<inter>D . f b \<noteq> {} }"
    have 6: "\<exists>C . (\<exists>D . ?B = C \<inter> D) \<and> (a,C) \<in> R"
      using 1 by auto
    have 7: "?B \<noteq> {}"
      using 3 4 5 by auto
    have 8: "\<forall>b\<in>?B . (b,f b) \<in> S \<and> f b \<noteq> {}"
      using 2 by auto
    have "(\<Union>x\<in>C\<inter>D . f x) = (\<Union>x\<in>?B . f x)"
      by auto
    thus "\<exists>B . (\<exists>C . (\<exists>D . B = C \<inter> D) \<and> (a,C) \<in> R) \<and> B \<noteq> {} \<and> (\<exists>g . (\<forall>b\<in>B . (b,g b) \<in> S \<and> g b \<noteq> {}) \<and> (\<Union>x\<in>C\<inter>D . f x) = (\<Union>x\<in>B . g x))"
      using 6 7 8 by blast
  qed
next
  show "ne (R\<down>) * ne S \<subseteq> ne (R\<down> * S)"
    by (clarsimp simp: mr_simp) blast
qed

lemma total_ne_down_dist_sp:
  "total T \<Longrightarrow> ne ((R * T)\<down>) = ne (R\<down>) * ne (T\<down>)"
  by (simp add: ne_dist_down_sp total_down_dist_sp)

lemma inner_univalent_char:
  "inner_univalent S \<longleftrightarrow> (\<forall>R . fus R = fus S \<and> R \<sqsubseteq>\<down> S \<longrightarrow> ne R = ne S)"
proof
  assume 1: "inner_univalent S"
  show "\<forall>R . fus R = fus S \<and> R \<sqsubseteq>\<down> S \<longrightarrow> ne R = ne S"
  proof (rule allI, rule impI)
    fix R
    assume 2: "fus R = fus S \<and> R \<sqsubseteq>\<down> S"
    show "ne R = ne S"
    proof (rule antisym)
      show "ne R \<subseteq> ne S"
      proof
        fix x
        assume 3: "x \<in> ne R"
        from this obtain a B where 4: "x = (a,B) \<and> x \<in> R \<and> B \<noteq> {}"
          by (metis Int_iff Int_lower2 inner_total_2 surj_pair)
        from this obtain C where 5: "B \<subseteq> C \<and> (a,C) \<in> S"
          using 2 by (meson lower_less_eq)
        from this obtain b where "C = {b}"
          using 1 4 by (metis Un_empty inner_univalent is_singletonI' is_singleton_the_elem subset_Un_eq)
        hence "B = C"
          using 4 5 by blast
        thus "x \<in> ne S"
          using 3 4 5 by blast
      qed
    next
      show "ne S \<subseteq> ne R"
      proof
        fix x
        assume 6: "x \<in> ne S"
        from this obtain a B where 7: "x = (a,B) \<and> x \<in> S \<and> B \<noteq> {}"
          by (metis Int_absorb Int_iff inner_total_2 semilattice_inf_class.inf.absorb_iff2 surj_pair)
        from this obtain b where 8: "B = {b}"
          using 1 by (meson antisym card_1_singletonE inner_univalent_2 nonempty_set_card)
        from this obtain C where 9: "b \<in> C \<and> (a,C) \<in> fus S"
          using 7 by (meson fusion_lower_increasing insert_subset lower_less_eq)
        hence "(a,C) \<in> fus R"
          using 2 by simp
        hence "C = \<Union>{ D . (a,D) \<in> R }"
          by (clarsimp simp: mr_simp)
        from this obtain D where 10: "b \<in> D \<and> (a,D) \<in> R"
          using 9 by blast
        from this obtain E where 11: "D \<subseteq> E \<and> (a,E) \<in> S"
          using 2 by (meson lower_less_eq)
        from this obtain c where "E = {c}"
          using 1 10 by (metis antisym card_1_singletonE empty_iff inner_univalent_2 nonempty_set_card subsetI)
        hence "D = {b}"
          using 10 11 by blast
        thus "x \<in> ne R"
          using 6 7 8 10 by blast
      qed
    qed
  qed
next
  assume 12: "\<forall>R . fus R = fus S \<and> R \<sqsubseteq>\<down> S \<longrightarrow> ne R = ne S"
  show "inner_univalent S"
  proof (unfold inner_univalent, intro allI, rule impI)
    fix a b c B
    assume 13: "(a,B) \<in> S \<and> b \<in> B \<and> c \<in> B"
    let ?R = "{ (f,{e}) | f e . \<exists>C . (f,C) \<in> S \<and> e \<in> C }"
    have 14: "fus ?R = fus S"
      apply (clarsimp simp: mr_simp)
      by blast
    have "?R \<sqsubseteq>\<down> S"
      using lower_less_eq by fastforce
    hence "ne ?R = ne S"
      using 12 14 by simp
    hence "(a,B) \<in> ?R"
      using 13 by (smt (verit, del_insts) empty_iff mem_Collect_eq non_empty)
    thus "b = c"
      using 13 by blast
  qed
qed

lemma ne_dist_oU:
  "ne (\<Union>X) = \<Union>(non_empty ` X)"
  by blast

subsection \<open>Fission\<close>

lemma fission_set:
  "fis R = { (a,{b}) | a b . \<exists>B . (a,B) \<in> R \<and> b \<in> B }"
  unfolding fis_set Image_singleton
  by simp

declare fission_set [mr_simp]

lemma fission_var:
  "fis R = R\<down> \<inter> A\<^sub>\<union>\<^sub>\<union>"
  apply (clarsimp simp: mr_simp)
  by blast

lemma fission_lower_decreasing:
  "fis R \<sqsubseteq>\<down> R"
  by (simp add: fission_var)

lemma fission_inner_deterministic:
  "inner_deterministic (fis R)"
  by (simp add: fission_var inner_deterministic_atoms)

lemma fission_greatest:
  assumes "S \<sqsubseteq>\<down> R"
    and "inner_deterministic S"
  shows "S \<sqsubseteq>\<down> fis R"
proof (clarsimp simp: mr_simp)
  fix a B
  assume 1: "(a,B) \<in> S"
  from this obtain b where 2: "B = {b}"
    using assms(2) by (meson card_1_singletonE inner_deterministic_2)
  from 1 obtain C where "B \<subseteq> C \<and> (a,C) \<in> R"
    using assms(1) by (meson lower_less_eq)
  thus "\<exists>C . (\<exists>D . B = C \<inter> D) \<and> (\<exists>b . C = {b} \<and> (\<exists>E . (a,E) \<in> R \<and> b \<in> E))"
    using 2 by auto
qed

lemma fission_unique:
  assumes "\<forall>R . f R \<sqsubseteq>\<down> R"
    and "\<forall>R . inner_deterministic (f R)"
    and "\<forall>R S . S \<sqsubseteq>\<down> R \<and> inner_deterministic S \<longrightarrow> S \<sqsubseteq>\<down> f R"
  shows "f T = fis T"
  apply (rule inner_deterministic_lower_eq)
    apply (simp add: assms(2))
   apply (simp add: fission_inner_deterministic)
  by (simp add: assms fission_greatest fission_inner_deterministic fission_lower_decreasing)

lemma fission_lower_isotone:
  "R \<sqsubseteq>\<down> S \<Longrightarrow> fis R \<sqsubseteq>\<down> fis S"
  by (meson fission_greatest fission_inner_deterministic fission_lower_decreasing lower_transitive)

lemma fission_idempotent:
  "fis (fis R) = fis R"
  by (metis comp_apply fis_fis)

lemma fission_top:
  "fis U = A\<^sub>\<union>\<^sub>\<union>"
  using fission_var top_down top_upper_least by fastforce

lemma fission_down:
  "fis R = fis (R\<down>)"
  by (simp add: fission_var)

lemma fission_ne_fixpoint:
  "fis R = ne (fis R)"
  using fission_inner_deterministic by blast

lemma fission_down_ne_fixpoint:
  "fis R = ne ((fis R)\<down>)"
  by (metis fission_inner_deterministic fission_ne_fixpoint fusion_down inner_univalent_char lower_ii_decreasing)

lemma fission_inner_deterministic_fixpoint:
  "inner_deterministic R \<longleftrightarrow> R = fis R"
  apply (rule iffI)
   apply (metis comp_eq_dest_lhs fission_lower_decreasing fission_ne_fixpoint fus_fis inner_univalent_char le_iff_inf)
  using fission_inner_deterministic by auto

lemma fission_sp_subdist:
  "fis (R * S) \<subseteq> fis R * fis S"
proof
  fix x
  assume "x \<in> fis (R * S)"
  from this obtain a b B where 1: "x = (a,{b}) \<and> (a,B) \<in> R * S \<and> b \<in> B"
    by (smt CollectD fission_set)
  from this obtain C f where 2: "(a,C) \<in> R \<and> (\<forall>c \<in> C . (c,f c) \<in> S) \<and> B = \<Union>{ f c | c . c \<in> C }"
    by (simp add: mr_simp) blast
  from this obtain c where 3: "b \<in> f c \<and> c \<in> C"
    using 1 by blast
  let ?B = "{c}"
  let ?f = "\<lambda>x . {b}"
  have 4: "(a,?B) \<in> fis R"
    using 2 3 fission_set by blast
  have 5: "\<forall>b\<in>?B . (b,?f b) \<in> fis S"
    using 2 3 fission_set by blast
  have "{b} = \<Union>{ ?f b | b . b \<in> ?B }"
    by simp
  hence "\<exists>f . (\<forall>b\<in>?B . (b,f b) \<in> fis S) \<and> {b} = \<Union>{ f b | b . b \<in> ?B }"
    using 5 by auto
  hence "(a,{b}) \<in> fis R * fis S"
    apply (unfold s_prod_def)
    using 4 by auto
  thus "x \<in> fis R * fis S"
    using 1 by simp
qed

lemma fission_sp_total_dist:
  assumes "total T"
  shows "fis (R * T) = fis R * fis T"
  by (metis assms atoms_sp_idempotent fis_lax fission_var sp_oi_subdist_2 subset_antisym total_down_dist_sp)

lemma fission_dist_ou:
  "fis (R \<union> S) = fis R \<union> fis S"
  by (simp add: down_dist_ou fission_var inf_sup_distrib2)

lemma fission_sp_iu_unit:
  "fis (R * 1\<^sub>\<union>\<^sub>\<union>) = {}"
  by (metis c_nc down_sp fission_lower_decreasing nu_def nu_fis nu_fis_var s_prod_zerol subset_empty)

lemma fission_fusion_lower_decreasing:
  "fis (fus R) \<sqsubseteq>\<down> R"
  apply (clarsimp simp: mr_simp)
  by blast

lemma fusion_fission_lower_increasing:
  "R \<sqsubseteq>\<down> fus (fis R)"
  apply (clarsimp simp: mr_simp)
  by blast

lemma fission_fusion_galois:
  "fis R \<sqsubseteq>\<down> S \<longleftrightarrow> R \<sqsubseteq>\<down> fus S"
  apply (rule iffI)
   apply (meson fusion_fission_lower_increasing fusion_lower_isotone lower_transitive)
  by (meson fission_fusion_lower_decreasing fission_lower_isotone lower_transitive)

lemma fission_fusion:
  "fis (fus R) = fis R"
  by (metis fission_fusion_lower_decreasing fission_idempotent fission_inner_deterministic fission_lower_isotone fusion_lower_increasing inner_deterministic_lower_eq)

lemma fusion_fission:
  "fus (fis R) = fus R"
  by (metis comp_def fus_fis)

lemma same_fusion_fission_lower:
  "fus R = fus S \<Longrightarrow> fis R \<sqsubseteq>\<down> S"
  by (metis fission_fusion_galois fusion_lower_increasing)

lemma fission_below_ne_down_fusion:
  "fis R \<subseteq> ne ((fus R)\<down>)"
  using fission_fusion fission_inner_deterministic fission_lower_decreasing by blast

lemma ne_fusion_fission:
  "(ne ((fus R)\<down>))\<up> = (fis R)\<up>"
  by (metis (mono_tags, lifting) atoms_solution fission_below_ne_down_fusion fission_fusion oi_down_sub_up subset_trans upper_eq_up upper_reflexive fission_var)

lemma fission_up_ne_down_up:
  "(fis R)\<up> = (ne (R\<down>))\<up>"
  by (metis (mono_tags, lifting) atoms_solution fission_ne_fixpoint fission_top oi_down_sub_up semilattice_inf_class.inf_le2 semilattice_inf_class.inf_left_commute subset_trans upper_eq_up fission_var)

lemma fusion_idempotent:
  "fus (fus R) = fus R"
  by (metis fission_fusion fusion_fission)

lemma fission_dist_oU:
  "fis (\<Union>X) = \<Union>(fis ` X)"
  by (metis (no_types, lifting) SUP_cong UN_simps(4) fission_var ii_right_dist_oU)

subsection \<open>Co-fusion and co-fission\<close>

definition co_fusion :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("\<Sqinter>\<Sqinter> _" [80] 80) where
  "\<Sqinter>\<Sqinter>R \<equiv> { (a,B) . B = \<Inter>{ C . (a,C) \<in> R } }"

declare co_fusion_def [mr_simp]

lemma co_fusion_upper_decreasing:
  "\<Sqinter>\<Sqinter>R \<sqsubseteq>\<up> R"
  apply (clarsimp simp: mr_simp)
  by blast

lemma co_fusion_deterministic:
  "deterministic (\<Sqinter>\<Sqinter>R)"
  by (simp add: deterministic_set co_fusion_def)

lemma co_fusion_greatest:
  assumes "S \<sqsubseteq>\<up> R"
    and "deterministic S"
  shows "S \<sqsubseteq>\<up> \<Sqinter>\<Sqinter>R"
proof (clarsimp simp: mr_simp)
  fix a
  from assms(2) obtain B where 1: "(a,B) \<in> S"
    by (meson deterministic_set)
  hence "B \<subseteq> \<Inter>{ C . (a,C) \<in> R }"
    using assms deterministic_upper by (smt (verit, ccfv_threshold) Inter_greatest mem_Collect_eq)
  thus "\<exists>B . (\<exists>D . \<Inter>{ C . (a,C) \<in> R } = B \<union> D) \<and> (a,B) \<in> S"
    using 1 by blast
qed

lemma co_fusion_unique:
  assumes "\<forall>R . f R \<sqsubseteq>\<up> R"
    and "\<forall>R . deterministic (f R)"
    and "\<forall>R S . S \<sqsubseteq>\<up> R \<and> deterministic S \<longrightarrow> S \<sqsubseteq>\<up> f R"
  shows "f T = \<Sqinter>\<Sqinter>T"
  apply (rule univalent_upper_eq)
  using assms(2) deterministic_def apply blast
  using co_fusion_deterministic deterministic_def apply blast
  by (simp add: assms co_fusion_deterministic co_fusion_greatest co_fusion_upper_decreasing)

lemma co_fusion_up_char:
  "(\<Sqinter>\<Sqinter>R)\<up> = -((-(R\<up>) \<inter> A\<^sub>\<inter>\<^sub>\<inter>)\<down>)"
proof
  show "(\<Sqinter>\<Sqinter>R)\<up> \<subseteq> -((-(R\<up>) \<inter> A\<^sub>\<inter>\<^sub>\<inter>)\<down>)"
    apply (clarsimp simp: mr_simp)
    by blast
next
  show "-((-(R\<up>) \<inter> A\<^sub>\<inter>\<^sub>\<inter>)\<down>) \<subseteq> (\<Sqinter>\<Sqinter>R)\<up>"
  proof (clarsimp simp: mr_simp)
    fix a A
    assume 1: "\<forall>B . (\<forall>C . A \<noteq> B \<inter> C) \<or> (\<exists>C . (\<exists>D . B = C \<union> D) \<and> (a,C) \<in> R) \<or> (\<forall>b . B \<noteq> UNIV - {b})"
    have "\<Inter>{ C . (a,C) \<in> R } \<subseteq> A"
    proof
      fix x
      assume "x \<in> \<Inter>{ C . (a,C) \<in> R }"
      hence "\<forall>C . A \<noteq> (UNIV - {x}) \<inter> C"
        using 1 by blast
      thus "x \<in> A"
        by blast
    qed
    thus "\<exists>D . A = \<Inter>{ C . (a,C) \<in> R } \<union> D"
      by auto
  qed
qed

lemma co_fusion_down_char:
  "(\<Sqinter>\<Sqinter>R)\<down> = -((\<sim>(R\<up>) \<inter> A\<^sub>\<union>\<^sub>\<union>)\<up>)"
proof
  show "(\<Sqinter>\<Sqinter>R)\<down> \<subseteq> -((\<sim>(R\<up>) \<inter> A\<^sub>\<union>\<^sub>\<union>)\<up>)"
    apply (clarsimp simp: mr_simp)
    by blast
next
  show "-((\<sim>(R\<up>) \<inter> A\<^sub>\<union>\<^sub>\<union>)\<up>) \<subseteq> (\<Sqinter>\<Sqinter>R)\<down>"
  proof (clarsimp simp: mr_simp)
    fix a A
    assume 1: "\<forall>C . (\<forall>D . A \<noteq> C \<union> D) \<or> (\<forall>B . (\<forall>D . - C \<noteq> B \<union> D) \<or> (a,B) \<notin> R) \<or> (\<forall>b . C \<noteq> {b})"
    have "A \<subseteq> \<Inter>{ C . (a,C) \<in> R }"
    proof
      fix x
      assume "x \<in> A"
      hence "\<forall>B . (\<forall>D . - {x} \<noteq> B \<union> D) \<or> (a,B) \<notin> R"
        using 1 by blast
      thus "x \<in> \<Inter>{ C . (a,C) \<in> R }"
        by blast
    qed
    thus "\<exists>C . A = \<Inter>{ C . (a,C) \<in> R } \<inter> C"
      by auto
  qed
qed

lemma co_fusion_down_char_2:
  "(\<Sqinter>\<Sqinter>R)\<down> = -(((R\<up> \<inter> A\<^sub>\<inter>\<^sub>\<inter>) \<odot> \<sim>1)\<up>)"
  by (metis co_fusion_down_char ic_co_atoms ic_cp_ic_unit ic_dist_oi)

lemma co_fusion_char:
  "\<Sqinter>\<Sqinter>R = -((-(R\<up>) \<inter> A\<^sub>\<inter>\<^sub>\<inter>)\<down>) \<inter> -((\<sim>(R\<up>) \<inter> A\<^sub>\<union>\<^sub>\<union>)\<up>)"
  by (metis deterministic_def co_fusion_deterministic co_fusion_down_char co_fusion_up_char univalent_convex)

lemma co_fusion_char_2:
  "\<Sqinter>\<Sqinter>R = -((-(R\<up>) \<inter> A\<^sub>\<inter>\<^sub>\<inter>)\<down>) \<inter> -(((R\<up> \<inter> A\<^sub>\<inter>\<^sub>\<inter>) \<odot> \<sim>1)\<up>)"
  using co_fusion_char co_fusion_down_char co_fusion_down_char_2 by blast

lemma co_fusion_upper_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> \<Sqinter>\<Sqinter>R \<sqsubseteq>\<up> \<Sqinter>\<Sqinter>S"
  by (meson co_fusion_deterministic co_fusion_greatest co_fusion_upper_decreasing upper_transitive)

lemma co_fusion_ii_idempotent:
  "\<Sqinter>\<Sqinter>R \<inter>\<inter> \<Sqinter>\<Sqinter>R = \<Sqinter>\<Sqinter>R"
  by (metis deterministic_def co_fusion_deterministic univalent_ii_idempotent)

lemma co_fusion_up:
  "\<Sqinter>\<Sqinter>R = \<Sqinter>\<Sqinter>(R\<up>)"
  by (simp add: co_fusion_char)

lemma co_fusion_ii_total:
  "total T \<Longrightarrow> T \<inter>\<inter> \<Sqinter>\<Sqinter>T = \<Sqinter>\<Sqinter>T"
  by (meson co_fusion_deterministic co_fusion_upper_decreasing deterministic_def total_univalent_upper_ii)

lemma co_fusion_deterministic_fixpoint:
  "deterministic R \<longleftrightarrow> R = \<Sqinter>\<Sqinter>R"
  apply (rule iffI)
   apply (metis deterministic_def co_fusion_deterministic co_fusion_greatest co_fusion_ii_total ii_commute total_univalent_upper_ii upper_reflexive)
  by (metis co_fusion_deterministic)

abbreviation co_fission :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("at\<^sub>\<inter>\<^sub>\<inter> _" [80] 80) where
  "at\<^sub>\<inter>\<^sub>\<inter> R \<equiv> R\<up> \<inter> A\<^sub>\<inter>\<^sub>\<inter>"

lemma co_fission:
  "at\<^sub>\<inter>\<^sub>\<inter> R = { (a,B) | a B . (\<exists>b . -B = {b}) \<and> (\<exists>C . (a,C) \<in> R \<and> C \<subseteq> B) }"
  apply (clarsimp simp: mr_simp)
  by blast

declare co_fission [mr_simp]

lemma co_fission_upper_increasing:
  "R \<sqsubseteq>\<up> at\<^sub>\<inter>\<^sub>\<inter> R"
  by (fact semilattice_inf_class.inf_le1)

lemma co_fission_ic_inner_deterministic:
  "inner_deterministic (\<sim>at\<^sub>\<inter>\<^sub>\<inter> R)"
  by (simp add: ic_co_atoms ic_dist_oi inner_deterministic_atoms)

lemma co_fission_least:
  assumes "R \<sqsubseteq>\<up> S"
    and "inner_deterministic (\<sim>S)"
  shows "at\<^sub>\<inter>\<^sub>\<inter> R \<sqsubseteq>\<up> S"
proof (clarsimp simp: mr_simp)
  fix a B
  assume 1: "(a,B) \<in> S"
  hence "(a,-B) \<in> \<sim>S"
    by (simp add: inner_complement_def)
  from this obtain b where 2: "-B = {b}"
    using assms(2) by (meson card_1_singletonE inner_deterministic_2)
  from 1 obtain C where "C \<subseteq> B \<and> (a,C) \<in> R"
    using assms(1) by (meson upper_less_eq)
  thus "\<exists>C . (\<exists>D . B = C \<union> D) \<and> (\<exists>E . (\<exists>D . C = E \<union> D) \<and> (a,E) \<in> R) \<and> (\<exists>b . C = UNIV - {b})"
    using 2 by (metis Compl_eq_Diff_UNIV double_compl subset_Un_eq sup.idem)
qed

lemma co_fission_unique:
  assumes "\<forall>R . R \<sqsubseteq>\<up> f R"
    and "\<forall>R . inner_deterministic (\<sim>f R)"
    and "\<forall>R S . R \<sqsubseteq>\<up> S \<and> inner_deterministic (\<sim>S) \<longrightarrow> f R \<sqsubseteq>\<up> S"
  shows "f T = at\<^sub>\<inter>\<^sub>\<inter> T"
  apply (rule ic_injective)
  apply (rule inner_deterministic_lower_eq)
    apply (simp add: assms(2))
   apply (simp add: co_fission_ic_inner_deterministic)
  by (meson assms co_fission_ic_inner_deterministic co_fission_least semilattice_inf_class.inf_le1 upper_ic_lower)

lemma co_fission_upper_isotone:
  "R \<sqsubseteq>\<up> S \<Longrightarrow> at\<^sub>\<inter>\<^sub>\<inter> R \<sqsubseteq>\<up> at\<^sub>\<inter>\<^sub>\<inter> S"
  by (simp add: oi_subset_upper_left_antitone upper_transitive)

lemma co_fission_idempotent:
  "at\<^sub>\<inter>\<^sub>\<inter> (at\<^sub>\<inter>\<^sub>\<inter> R) = at\<^sub>\<inter>\<^sub>\<inter> R"
  by (meson equalityI semilattice_inf_class.inf_le1 semilattice_inf_class.inf_le2 semilattice_inf_class.le_inf_iff upper_reflexive upper_transitive)

lemma co_fission_top:
  "at\<^sub>\<inter>\<^sub>\<inter> U = A\<^sub>\<inter>\<^sub>\<inter>"
  using top_lower_greatest U_par_idem top_down by blast

lemma co_fission_up:
  "at\<^sub>\<inter>\<^sub>\<inter> R = at\<^sub>\<inter>\<^sub>\<inter> (R\<up>)"
  by simp

lemma co_fission_ic_inner_deterministic_fixpoint:
  "inner_deterministic (\<sim>R) \<longleftrightarrow> R = at\<^sub>\<inter>\<^sub>\<inter> R"
  apply (rule iffI)
   apply (simp add: fission_var fission_inner_deterministic_fixpoint ic_antidist_iu ic_co_atoms ic_dist_oi ic_injective ic_up)
  by (metis co_fission_ic_inner_deterministic)

lemma co_fusion_co_fission_upper_decreasing:
  "\<Sqinter>\<Sqinter>(at\<^sub>\<inter>\<^sub>\<inter> R) \<sqsubseteq>\<up> R"
proof (clarsimp simp: mr_simp)
  fix a B
  assume 1: "(a,B) \<in> R"
  have "\<Inter>{ D . (\<exists>E . (\<exists>F . D = E \<union> F) \<and> (a,E) \<in> R) \<and> (\<exists>b . D = UNIV - {b}) } \<subseteq> B"
  proof
    fix x
    assume 2: "x \<in> \<Inter>{ D . (\<exists>E . (\<exists>F . D = E \<union> F) \<and> (a,E) \<in> R) \<and> (\<exists>b . D = UNIV - {b}) }"
    show "x \<in> B"
    proof (rule ccontr)
      let ?D = "-{x}"
      assume 3: "x \<notin> B"
      hence "B \<subseteq> ?D"
        by simp
      hence "\<Inter>{ D . (\<exists>E . (\<exists>F . D = E \<union> F) \<and> (a,E) \<in> R) \<and> (\<exists>b . D = UNIV - {b}) } \<subseteq> ?D"
        using 1 by (smt CollectI Compl_eq_Diff_UNIV Inf_lower subset_Un_eq)
      thus False
        using 2 by auto
    qed
  qed
  thus "\<exists>C . B = \<Inter>{ D . (\<exists>E . (\<exists>F . D = E \<union> F) \<and> (a,E) \<in> R) \<and> (\<exists>b . D = UNIV - {b}) } \<union> C"
    by auto
qed

lemma co_fission_co_fusion_upper_increasing:
  "R \<sqsubseteq>\<up> at\<^sub>\<inter>\<^sub>\<inter> (\<Sqinter>\<Sqinter>R)"
proof (clarsimp simp: mr_simp)
  fix a b B
  assume "\<Inter>{ C . (a,C) \<in> R } \<union> B = UNIV - {b}"
  hence "b \<notin> \<Inter>{ C . (a,C) \<in> R }"
    by blast
  hence "\<exists>C . b \<notin> C \<and> (a,C) \<in> R"
    by blast
  thus "\<exists>C . (\<exists>D . UNIV - {b} = C \<union> D) \<and> (a,C) \<in> R"
    by blast
qed

lemma co_fusion_co_fission_galois:
  "\<Sqinter>\<Sqinter>R \<sqsubseteq>\<up> S \<longleftrightarrow> R \<sqsubseteq>\<up> at\<^sub>\<inter>\<^sub>\<inter> S"
  apply (rule iffI)
   apply (meson co_fission_co_fusion_upper_increasing co_fission_upper_isotone upper_transitive)
  by (meson co_fusion_co_fission_upper_decreasing co_fusion_upper_isotone upper_transitive)

lemma co_fission_co_fusion:
  "at\<^sub>\<inter>\<^sub>\<inter> (\<Sqinter>\<Sqinter>R) = at\<^sub>\<inter>\<^sub>\<inter> R"
  using co_fission_co_fusion_upper_increasing co_fission_idempotent co_fission_upper_isotone co_fusion_upper_decreasing by blast

lemma co_fusion_co_fission:
  "\<Sqinter>\<Sqinter>(at\<^sub>\<inter>\<^sub>\<inter> R) = \<Sqinter>\<Sqinter>R"
  apply (rule antisym)
   apply (metis deterministic_def co_fission_co_fusion co_fission_co_fusion_upper_increasing co_fusion_co_fission_upper_decreasing co_fusion_deterministic co_fusion_upper_isotone univalent_upper_eq_subset)
  by (metis deterministic_def co_fission_co_fusion co_fission_co_fusion_upper_increasing co_fusion_co_fission_upper_decreasing co_fusion_deterministic co_fusion_upper_isotone univalent_upper_eq_subset)

lemma same_co_fusion_co_fission_upper:
  "\<Sqinter>\<Sqinter>R = \<Sqinter>\<Sqinter>S \<Longrightarrow> S \<sqsubseteq>\<up> at\<^sub>\<inter>\<^sub>\<inter> R"
  by (metis co_fusion_co_fission_galois co_fusion_upper_decreasing)

lemma co_fusion_idempotent:
  "\<Sqinter>\<Sqinter>(\<Sqinter>\<Sqinter>R) = \<Sqinter>\<Sqinter>R"
  by (metis co_fission_co_fusion co_fusion_co_fission)

section \<open>Modalities\<close>

subsection \<open>Tests\<close>

abbreviation test :: "('a,'a) mrel \<Rightarrow> bool" where
  "test R \<equiv> R \<subseteq> 1"

lemma test:
  "test R \<longleftrightarrow> (\<forall>a B . (a,B) \<in> R \<longrightarrow> B = {a})"
  by (force simp: s_id_def)

lemma test_fix: "test R \<equiv> R \<inter> 1\<^sub>\<sigma> = R"
  by (simp add: le_iff_inf)

lemma test_ou_closed:
  "test p \<Longrightarrow> test q \<Longrightarrow> test (p \<union> q)"
  by (fact sup_least)

lemma test_oi_closed:
  "test p \<Longrightarrow> test (p \<inter> q)"
  by blast

abbreviation test_complement :: "('a,'a) mrel \<Rightarrow> ('a,'a) mrel" ("\<wrong> _" [80] 80) where
  "\<wrong> R \<equiv> -R \<inter> 1"

lemma test_complement_closed:
  "test (\<wrong> p)"
  by simp

lemma test_double_complement:
  "test p \<longleftrightarrow> p = \<wrong> \<wrong> p"
  by blast

lemma test_complement:
  "(a,{a}) \<in> \<wrong> p \<longleftrightarrow> \<not> (a,{a}) \<in> p"
  by (simp add: s_id_def)

declare test_complement [mr_simp]

lemma test_complement_antitone:
  assumes "test p"
  shows "p \<subseteq> q \<longleftrightarrow> \<wrong> q \<subseteq> \<wrong> p"
  using assms(1) by blast

lemma test_complement_huntington:
  "test p \<Longrightarrow> p = \<wrong> (\<wrong> p \<union> \<wrong> q) \<union> \<wrong> (\<wrong> p \<union> q)"
  by blast

abbreviation test_implication :: "('a,'a) mrel \<Rightarrow> ('a,'a) mrel \<Rightarrow> ('a,'a) mrel" (infixl "\<rightarrow>" 65) where
  "p \<rightarrow> q \<equiv> \<wrong> p \<union> q"

lemma test_implication_closed:
  "test q \<Longrightarrow> test (p \<rightarrow> q)"
  by simp

lemma test_implication:
  "(a,{a}) \<in> p \<rightarrow> q \<longleftrightarrow> ((a,{a}) \<in> p \<longrightarrow> (a,{a}) \<in> q)"
  by (simp add: s_id_def)

declare test_implication [mr_simp]

lemma test_implication_left_antitone:
  assumes "test p"
  shows "p \<subseteq> r \<Longrightarrow> r \<rightarrow> q \<subseteq> p \<rightarrow> q"
  by blast

lemma test_implication_right_isotone:
  assumes "test p"
  shows "q \<subseteq> r \<Longrightarrow> p \<rightarrow> q \<subseteq> p \<rightarrow> r"
  by blast

lemma test_sp_idempotent:
  "test p \<Longrightarrow> p * p = p"
  by (metis d_rest_ax inf.order_iff s_subid_iff2)

lemma test_sp:
  assumes "test p"
  shows "p * R = (p * U) \<inter> R"
  apply (clarsimp simp: mr_simp)
  apply safe
    apply blast
  using assms subid_aux2 by fastforce+

lemma sp_test:
  "test p \<Longrightarrow> R * p = R \<inter> (U * p)"
  apply (rule antisym)
   apply (metis (no_types, lifting) U_par_idem inf.absorb_iff2 inf.idem le_inf_iff s_prod_idr sp_oi_subdist top_upper_least)
  using test_fix by (smt IntE s_prod_test_aux1 s_prod_test_aux2 subrelI)

lemma sp_test_dist_oi:
  "test p \<Longrightarrow> (R \<inter> S) * p = (R * p) \<inter> (S * p)"
  by (smt Int_left_commute semilattice_inf_class.inf.assoc semilattice_inf_class.inf.right_idem sp_test)

lemma sp_test_dist_oi_left:
  "test p \<Longrightarrow> (R \<inter> S) * p = (R * p) \<inter> S"
  by (smt Int_commute semilattice_inf_class.inf.left_commute sp_test)

lemma sp_test_dist_oi_right:
  "test p \<Longrightarrow> (R \<inter> S) * p = R \<inter> (S * p)"
  by (metis semilattice_inf_class.inf.commute sp_test_dist_oi_left)

lemma sp_test_sp_oi_left:
  "test p \<Longrightarrow> (R \<inter> (U * p)) * T = R * p * T"
  by (metis sp_test)

lemma sp_test_sp_oi_right:
  "test p \<Longrightarrow> R * ((p * U) \<inter> T) = R * p * T"
  by (metis inf.orderE test_assoc1 test_sp)

lemma test_sp_ne:
  "test p \<Longrightarrow> p * ne R = ne (p * R)"
  by (smt lattice_class.inf_sup_aci(1) lattice_class.inf_sup_aci(3) test_sp)

lemma ne_sp_test:
  "test p \<Longrightarrow> ne R * p = ne (R * p)"
  by (fact sp_test_dist_oi_left)

lemma top_sp_test_down_closed:
  assumes "test p"
  shows "U * p = (U * p)\<down>"
proof -
  have 1: "p \<inter> 1\<^sub>\<sigma> = p"
    using assms by blast
  hence "(U * p)\<down> = {(a,A). (a,A) \<in> U \<and> (\<forall>a \<in> A. (a,{a}) \<in> p)} \<inter>\<inter> U"
    by (smt (verit) Collect_cong case_prodI2 case_prod_conv s_prod_test_var)
  also have "\<dots> = {(a,A). \<forall>a \<in> A. (a,{a}) \<in> p} \<inter>\<inter> U"
    by (smt (verit) Collect_cong ii_assoc lower_ii_down mem_Collect_eq split_cong subsetD top_down)
  also have "\<dots> = {(a,A). (a,A) \<in> U \<and> (\<forall>a \<in> A. (a,{a}) \<in> p)}"
    by (auto simp: mr_simp)
  also have "\<dots> = U * p"
    using 1 by (smt (verit) Collect_cong case_prodI2 case_prod_conv s_prod_test_var)
  finally show ?thesis
    by blast
qed

lemma oc_top_sp_test_up_closed:
  "test p \<Longrightarrow> -(U * p) = (-(U * p))\<up>"
  by (metis antisym convex_reflexive disjoint_eq_subset_Compl inf_compl_bot oi_down_up_iff semilattice_inf_class.inf.commute top_sp_test_down_closed)

lemma top_sp_test:
  "test p \<Longrightarrow> (a,B) \<in> U * p \<longleftrightarrow> (\<forall>b\<in>B . (b,{b}) \<in> p)"
  using test_fix by (metis IntE UNIV_I s_prod_test sp_test)

lemma oc_top_sp_test:
  "test p \<Longrightarrow> (a,B) \<in> -(U * p) \<longleftrightarrow> (\<exists>b\<in>B . (b,{b}) \<notin> p)"
  by (simp add: top_sp_test)

declare top_sp_test [mr_simp] oc_top_sp_test [mr_simp]

lemma oc_top_sp_test_0:
  "-1\<^sub>\<union>\<^sub>\<union> * \<wrong> p = ne (U * \<wrong> p)"
  by (metis Int_lower1 semilattice_inf_class.inf.commute sp_test)

lemma oc_top_sp_test_1:
  assumes "test p"
  shows "-(U * p) = (ne (U * \<wrong> p))\<up>"
proof (rule antisym)
  show "-(U * p) \<subseteq> (ne (U * \<wrong> p))\<up>"
  proof
    fix x::"'c \<times> 'a set"
    assume 1: "x \<in> -(U * p)"
    from this obtain a B where 2: "x = (a,B)"
      by force
    from this obtain c where 3: "c \<in> B \<and> (c,{c}) \<notin> p"
      using 1 by (meson assms oc_top_sp_test)
    hence 4: "(a,{c}) \<in> U * \<wrong> p"
      by (metis singletonD test_complement test_complement_closed top_sp_test)
    have "(a,{c}) \<in> -1\<^sub>\<union>\<^sub>\<union>"
      using oc_top_sp_test by (smt (verit, del_insts) ComplI Int_iff assms boolean_algebra.conj_cancel_left inf.coboundedI2 p_id_zero s_prod_test_aux1 singleton_iff)
    hence "(a,{c}) \<in> ne (U * \<wrong> p)"
      using 4 by simp
    thus "x \<in> (ne (U * \<wrong> p))\<up>"
      using 2 3 by (metis (no_types, lifting) U_par_st singletonD subset_eq)
  qed
next
  have "(U * p)\<down> = U * p"
    using assms top_sp_test_down_closed by auto
  also have "... \<subseteq> -(-1\<^sub>\<union>\<^sub>\<union> * \<wrong> p)"
    by (smt (verit) Compl_disjoint assms disjoint_eq_subset_Compl inf_commute oc_top_sp_test_0 p_id_zero s_prod_idl sp_test_dist_oi_right test_assoc1 test_double_complement)
  also have "... = -ne (U * \<wrong> p)"
    by (simp add: oc_top_sp_test_0)
  finally have "U * p \<subseteq> -((ne (U * \<wrong> p))\<up>)"
    by (simp add: down_double_complement_up)
  thus "(ne (U * \<wrong> p))\<up> \<subseteq> -(U * p)"
    by auto
qed

lemma oc_top_sp_test_2:
  "test p \<Longrightarrow> -(U * p) = (-1\<^sub>\<union>\<^sub>\<union> * \<wrong> p)\<up>"
  by (simp add: oc_top_sp_test_1 oc_top_sp_test_0)

lemma split_sp_test:
  assumes "test p"
  shows "R = (R * p) \<union> (ne R \<inter> (ne (R\<down> * \<wrong> p))\<up>)"
proof (rule antisym)
  show "R \<subseteq> (R * p) \<union> (ne R \<inter> (ne (R\<down> * \<wrong> p))\<up>)"
  proof
    fix x
    assume 1: "x \<in> R"
    from this obtain a B where 2: "x = (a,B)"
      by force
    show "x \<in> (R * p) \<union> (ne R \<inter> (ne (R\<down> * \<wrong> p))\<up>)"
    proof (cases "\<forall>b\<in>B . (b,{b}) \<in> p")
      case True
      hence "(a,B) \<in> U * p"
        by (simp add: assms top_sp_test)
      thus ?thesis
        using 1 2 by (metis Int_iff UnCI assms sp_test)
    next
      case False
      from this obtain b where 3: "{b} \<subseteq> B \<and> (b,{b}) \<notin> p"
        by auto
      hence "(a,{b}) \<in> R\<down>"
        using 1 2 down by fastforce
      hence "(a,{b}) \<in> R\<down> * \<wrong> p"
        using 3 by (metis s_prod_test_aux2 singletonD test_complement)
      hence "(a,{b}) \<in> ne (R\<down> * \<wrong> p)"
        by (simp add: non_empty)
      hence "(a,B) \<in> (ne (R\<down> * \<wrong> p))\<up>"
        using 3 by (meson U_par_st)
      thus ?thesis
        using 1 2 3 non_empty by auto
    qed
  qed
next
  show "(R * p) \<union> (ne R \<inter> (ne (R\<down> * \<wrong> p))\<up>) \<subseteq> R"
    using assms sp_test by auto
qed

lemma top_sp_test_down_iff_1:
  assumes "test p"
  shows "R \<subseteq> U * p \<longleftrightarrow> R\<down> \<subseteq> U * p"
  by (smt (verit, del_insts) assms down_order_lower top_sp_test_down_closed)

lemma test_ne:
  "test p \<Longrightarrow> ne p = p"
  using inner_deterministic_sp_unit by blast

lemma ne_test_up:
  "test p \<Longrightarrow> ne (p\<up>) = p\<up>"
  by (metis atoms_solution ne_equality test_ne up_idempotent up_isotone)

lemma ne_sp_test_up:
  "test p \<Longrightarrow> (ne (R * p))\<up> = ne R * p\<up>"
  using test_fix by (smt ne_up sp_test_dist_oi_left test_assoc1 test_ne)

lemma ne_down_sp_test_up:
  "test p \<Longrightarrow> ne (R\<down> * p\<up>) = ne (R\<down>) * p\<up>"
  by (simp add: ne_dist_down_sp ne_test_up)

lemma test_up_sp:
  "test p \<Longrightarrow> p\<up> = p * 1\<up>"
  by (metis ne_up test_ne)

lemma top_test_oi_top_complement:
  "test p \<Longrightarrow> (U * p) \<inter> (U * \<wrong> p) = 1\<^sub>\<union>\<^sub>\<union>"
  by (smt (verit) Compl_disjoint U_par_idem inf.absorb_iff2 inf_commute p_id_zero s_prod_idl sp_test_dist_oi_right test_assoc1 top_upper_least)

lemma sp_test_oi_complement:
  "test p \<Longrightarrow> (R * p) \<inter> (R * \<wrong> p) = R \<inter> 1\<^sub>\<union>\<^sub>\<union>"
  by (smt semilattice_inf_class.inf_idem sp_test sp_test_dist_oi_left sp_test_dist_oi_right test_complement_closed top_test_oi_top_complement)

lemma ne_top_sp_test_complement:
  assumes "test p"
  shows "ne (U * p) * \<wrong> p = {}"
  by (metis Compl_disjoint Int_assoc assms oc_top_sp_test_0 semilattice_inf_class.inf_le2 sp_test_dist_oi_right top_test_oi_top_complement)

lemma complement_test_sp_top:
  assumes "test p"
  shows "-(p * U) = \<wrong> p * U"
proof -
  have "-(p * U) = -{(a,A). (a,{a}) \<in> p \<and> (a,A) \<in> U}"
    by (metis (no_types, lifting) Collect_cong assms inf.orderE split_cong test_s_prod_var)
  also have "\<dots> = -{(a,A). (a,{a}) \<in> p}"
    using top_upper_least by auto
  also have "\<dots> = {(a,A). (a,{a}) \<notin> p}"
    by force
  also have "\<dots> = {(a,A). (a,{a}) \<in> \<wrong> p}"
    by (meson test_complement)
  also have "\<dots> = {(a,A). (a,{a}) \<in> \<wrong> p \<and> (a,A) \<in> U}"
    using U_par_idem top_upper_least by auto
  also have "\<dots> =  \<wrong> p * U"
    by (simp add: test_s_prod_var)
  finally show ?thesis
    .
qed

lemma top_sp_test_shunt:
  assumes "test p"
  shows "R \<subseteq> U * p \<longrightarrow> R * \<wrong> p \<subseteq> 1\<^sub>\<union>\<^sub>\<union>"
  by (metis assms inf.absorb_iff1 sp_test sp_test_dist_oi test_complement_closed top_test_oi_top_complement)

lemma top_sp_test_down_iff_2:
  assumes "test p"
  shows "R\<down> \<subseteq> U * p \<longleftrightarrow> R\<down> * \<wrong> p \<subseteq> 1\<^sub>\<union>\<^sub>\<union>"
proof
  assume "R\<down> \<subseteq> U * p"
  thus "R\<down> * \<wrong> p \<subseteq> 1\<^sub>\<union>\<^sub>\<union>"
    using assms top_sp_test_shunt by blast
next
  assume 1: "R\<down> * \<wrong> p \<subseteq> 1\<^sub>\<union>\<^sub>\<union>"
  have "R \<subseteq> U * p"
  proof
    fix x
    assume "x \<in> R"
    from this obtain a B where 2: "x = (a,B) \<and> x \<in> R"
      by force
    have "\<forall>b\<in>B . (b,{b}) \<in> p"
    proof
      fix b
      assume 3: "b \<in> B"
      have "(b,{b}) \<notin> \<wrong> p"
      proof
        assume 4: "(b,{b}) \<in> \<wrong> p"
        have "(a,{b}) \<in> R\<down>"
          using 2 3 down by fastforce
        hence "(a,{b}) \<in> R\<down> * \<wrong> p"
          using 4 by (simp add: s_prod_test)
        thus False
          using 1 by (metis Pair_inject domain_pointwise insert_not_empty p_subid_iff)
      qed
      thus "(b,{b}) \<in> p"
        by (meson test_complement)
    qed
    thus "x \<in> U * p"
      using 2 by (simp add: assms top_sp_test)
  qed
  thus "R\<down> \<subseteq> U * p"
    using assms top_sp_test_down_iff_1 by blast
qed

lemma top_sp_test_down_iff_3:
  "R\<down> * \<wrong> p \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<longleftrightarrow> ne (R\<down>) * \<wrong> p \<subseteq> {}"
  by (simp add: disjoint_eq_subset_Compl ne_sp_test)

lemma top_sp_test_down_iff_4:
  assumes "test p"
  shows "R\<down> \<inter> (U * \<wrong> p) \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<longleftrightarrow> R\<down> \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<union> (U * p)"
  by (metis assms lattice_class.sup_inf_absorb semilattice_inf_class.inf_le2 sp_test sup_commute top_sp_test_down_iff_2 top_test_oi_top_complement)

lemma top_sp_test_down_iff_5:
  assumes "test p"
  shows "R\<down> \<subseteq> U * p \<longleftrightarrow> R\<down> \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<union> (U * p)"
  by (metis assms semilattice_inf_class.inf_le1 sup.absorb2 top_test_oi_top_complement)

lemma iu_test_sp_left_zero:
  assumes "q \<subseteq> 1\<^sub>\<union>\<^sub>\<union>"
  shows "q * R = q"
  by (metis assms p_id_assoc2 p_subid_iff s_prod_p_idl)

lemma test_iu_test_split:
  "t \<subseteq> 1 \<union> 1\<^sub>\<union>\<^sub>\<union> \<longleftrightarrow> (\<exists>p q . p \<subseteq> 1 \<and> q \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<and> t = p \<union> q)"
  by (meson subset_UnE sup.mono)

lemma test_iu_test_sp_assoc_1:
  "t \<subseteq> 1 \<union> 1\<^sub>\<union>\<^sub>\<union> \<Longrightarrow> t * (R * S) = (t * R) * S"
  unfolding test_iu_test_split
  by (smt (verit, ccfv_threshold) inf.orderE p_id_assoc2 p_subid_iff s_prod_distr s_prod_p_idl test_assoc2)

lemma test_iu_test_sp_assoc_2:
  "t \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<Longrightarrow> R * (t * S) = (R * t) * S"
proof -
  assume 1: "t \<subseteq> 1\<^sub>\<union>\<^sub>\<union>"
  have "R * (t * S) = R * (t * {})"
    using 1 by (metis iu_test_sp_left_zero p_id_assoc2 s_prod_p_idl)
  also have "\<dots> = (R * t) * {}"
    by (metis cl5 s_prod_idl)
  also have "\<dots> \<subseteq> (R * t) * S"
    by (simp add: s_prod_isor)
  finally have "R * (t * S) \<subseteq> (R * t) * S"
    .
  thus ?thesis
    by (simp add: s_prod_assoc1 set_eq_subset)
qed

lemma test_iu_test_sp_assoc_3:
  assumes "t \<subseteq> 1 \<union> 1\<^sub>\<union>\<^sub>\<union>"
  shows "R * (t * S) = (R * t) * S"
proof
  let ?g = "\<lambda>b . if (b,{b}) \<in> t \<and> (b,{}) \<notin> t then {b} else {}"
  show "R * (t * S) \<subseteq> (R * t) * S"
  proof
    fix x
    assume "x \<in> R * (t * S)"
    from this obtain a B C f where 1: "x = (a,C) \<and> (a,B) \<in> R \<and> (\<forall>b\<in>B . (b,f b) \<in> t * S) \<and> C = \<Union>{ f b | b . b\<in>B }"
      by (simp add: mr_simp) blast
    hence "\<forall>b\<in>B . \<exists>D . (b,D) \<in> t \<and> (\<exists>g . (\<forall>e\<in>D . (e,g e) \<in> S) \<and> f b = \<Union>{ g e | e . e \<in> D })"
      by (simp add: mr_simp Setcompr_eq_image)
    hence "\<exists>Db . \<forall>b\<in>B . (b,Db b) \<in> t \<and> (\<exists>g . (\<forall>e\<in>Db b . (e,g e) \<in> S) \<and> f b = \<Union>{ g e | e . e \<in> Db b })"
      by (rule bchoice)
    from this obtain Db where 2: "\<forall>b\<in>B . (b,Db b) \<in> t \<and> (\<exists>g . (\<forall>e\<in>Db b . (e,g e) \<in> S) \<and> f b = \<Union>{ g e | e . e \<in> Db b })"
      by auto
    let ?D = "\<Union>{ Db b | b . b \<in> B }"
    have "\<forall>b\<in>B . (b,Db b) \<in> t"
      using 2 by auto
    hence 3: "\<forall>b\<in>B . Db b = {b} \<or> Db b = {}"
      using assms by (metis Pair_inject Un_iff domain_pointwise inf.orderE p_subid_iff subid_aux2 test_iu_test_split)
    have 4: "(a,?D) \<in> R * t"
      apply (simp add: mr_simp)
      apply (rule exI[where ?x="B"])
      apply (rule conjI)
      using 1 apply simp
      apply (rule exI[where ?x="Db"])
      using 2 by auto
    have 5: "\<forall>b\<in>?D . (b,f b) \<in> S"
    proof
      fix b
      assume "b \<in> ?D"
      hence "b \<in> B \<and> Db b = {b}"
        using 3 by auto
      thus "(b,f b) \<in> S"
        using 2 by force
    qed
    have 6: "C = \<Union>{ f b | b . b \<in> ?D }"
    proof
      show "C \<subseteq> \<Union>{ f b | b . b \<in> ?D }"
      proof
        fix y
        assume "y \<in> C"
        from this 1 obtain b where 7: "b \<in> B \<and> y \<in> f b"
          by auto
        hence "Db b = {b}"
          using 2 3 by blast
        thus "y \<in> \<Union>{ f b | b . b \<in> ?D }"
          using 7 by blast
      qed
    next
      show "\<Union>{ f b | b . b \<in> ?D } \<subseteq> C"
      proof
        fix y
        assume "y \<in> \<Union>{ f b | b . b \<in> ?D }"
        from this obtain b where 8: "b \<in> ?D \<and> y \<in> f b"
          by auto
        hence "b \<in> B"
          using 3 by auto
        thus "y \<in> C"
          using 1 8 by auto
      qed
    qed
    have "(a,C) \<in> (R * t) * S"
      using 4 5 6 apply (clarsimp simp: mr_simp) by blast
    thus "x \<in> (R * t) * S"
      using 1 by simp
  qed
next
  show "(R * t) * S \<subseteq> R * (t * S)"
    using s_prod_assoc1 by blast
qed

lemma test_iu_test_sp_assoc_4:
  "t \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<Longrightarrow> R * (S * t) = (R * S) * t"
  by (metis cl5 iu_test_sp_left_zero)

lemma test_iu_test_sp_assoc_5:
  assumes "t \<subseteq> 1 \<union> 1\<^sub>\<union>\<^sub>\<union>"
  shows "R * (S * t) = (R * S) * t"
proof
  show "R * (S * t) \<subseteq> (R * S) * t"
  proof
    fix x
    assume "x \<in> R * (S * t)"
    from this obtain a B C f where 1: "x = (a,C) \<and> (a,B) \<in> R \<and> (\<forall>b\<in>B . (b,f b) \<in> S * t) \<and> C = \<Union>{ f b | b . b\<in>B }"
      by (clarsimp simp: mr_simp) blast
    hence "\<forall>b\<in>B . \<exists>D . (b,D) \<in> S \<and> (\<exists>g . (\<forall>e\<in>D . (e,g e) \<in> t) \<and> f b = \<Union>{ g e | e . e \<in> D })"
      by (clarsimp simp: mr_simp Setcompr_eq_image)
    hence "\<exists>Db . \<forall>b\<in>B . (b,Db b) \<in> S \<and> (\<exists>g . (\<forall>e\<in>Db b . (e,g e) \<in> t) \<and> f b = \<Union>{ g e | e . e \<in> Db b })"
      by (rule bchoice)
    from this obtain Db where 2: "\<forall>b\<in>B . (b,Db b) \<in> S \<and> (\<exists>g . (\<forall>e\<in>Db b . (e,g e) \<in> t) \<and> f b = \<Union>{ g e | e . e \<in> Db b })"
      by auto
    hence "\<exists>gb . \<forall>b\<in>B . (\<forall>e\<in>Db b . (e,gb b e) \<in> t) \<and> f b = \<Union>{ gb b e | e . e \<in> Db b }"
      by (auto intro: bchoice)
    from this obtain gb where 3: "\<forall>b\<in>B . (\<forall>e\<in>Db b . (e,gb b e) \<in> t) \<and> f b = \<Union>{ gb b e | e . e \<in> Db b }"
      by auto
    let ?g = "\<lambda>x . \<Union>{ gb b x | b . b \<in> B \<and> x \<in> Db b }"
    have 4: "\<forall>b\<in>B . \<forall>e\<in>Db b . gb b e = {} \<or> gb b e = {e}"
    proof (intro ballI)
      fix b e
      assume "b \<in> B" "e \<in> Db b"
      hence "(e,gb b e) \<in> t"
        using 3 by simp
      thus "gb b e = {} \<or> gb b e = {e}"
        by (metis Un_iff assms domain_pointwise inf.orderE p_subid_iff prod.inject subid_aux2 test_iu_test_split)
    qed
    hence "\<forall>e . ?g e \<subseteq> {e}"
      by auto
    hence 5: "\<forall>e . ?g e = {} \<or> ?g e = {e}"
      by auto
    let ?D = "\<Union>{ Db b | b . b \<in> B }"
    have 6: "(a,?D) \<in> R * S"
      apply (unfold s_prod_def)
      using 1 2 by blast
    have 7: "\<forall>b\<in>?D . (b,?g b) \<in> t"
    proof
      fix e
      assume "e \<in> ?D"
      from this obtain b where 8: "b \<in> B \<and> e \<in> Db b"
        by auto
      show "(e,?g e) \<in> t"
      proof (cases "?g e = {}")
        case True
        hence "gb b e = {}"
          using 8 by auto
        thus ?thesis
          using 3 8 True by metis
      next
        case False
        hence 9: "?g e = {e}"
          using 5 by auto
        from this obtain bb where 10: "bb \<in> B \<and> e \<in> Db bb \<and> e \<in> gb bb e"
          by auto
        hence "gb bb e = {e}"
          using 4 by auto
        thus ?thesis
          using 3 9 10 by force
      qed
    qed
    have 11: "C = \<Union>{ ?g e | e . e \<in> ?D }"
    proof
      show "C \<subseteq> \<Union>{ ?g e | e . e \<in> ?D }"
      proof
        fix y
        assume "y \<in> C"
        from this obtain b where 12: "b \<in> B \<and> y \<in> f b"
          using 1 by auto
        from this 3 obtain e where "e \<in> Db b \<and> y \<in> gb b e"
          by auto
        thus "y \<in> \<Union>{ ?g e | e . e \<in> ?D }"
          using 4 12 by auto
      qed
    next
      show "\<Union>{ ?g e | e . e \<in> ?D } \<subseteq> C"
      proof
        fix y
        assume "y \<in> \<Union>{ ?g e | e . e \<in> ?D }"
        from this obtain b e where 13: "b \<in> B \<and> e \<in> Db b \<and> y \<in> gb b e"
          by auto
        hence "y \<in> f b"
          using 3 by auto
        thus "y \<in> C"
          using 1 13 by auto
      qed
    qed
    have "(a,C) \<in> (R * S) * t"
      apply (simp add: mr_simp)
      apply (rule exI[where ?x="?D"])
      apply (rule conjI)
      using 6 apply (simp add: mr_simp)
      apply (rule exI[where ?x="?g"])
      using 7 11 by auto
    thus "x \<in> (R * S) * t"
      using 1 by simp
  qed
next
  show "(R * S) * t \<subseteq> R * (S * t)"
    using s_prod_assoc1 by blast
qed

lemma inner_deterministic_sp_assoc:
  assumes "inner_univalent t"
  shows "t * (R * S) = (t * R) * S"
proof (rule antisym)
  show "t * (R * S) \<subseteq> (t * R) * S"
  proof
    fix x
    assume "x \<in> t * (R * S)"
    from this obtain a B D f where 1: "x = (a,D) \<and> (a,B) \<in> t \<and> (\<forall>b\<in>B . (b,f b) \<in> R * S) \<and> D = \<Union>{ f b | b . b\<in>B }"
      by (simp add: mr_simp) blast
    have "(a,D) \<in> (t * R) * S"
    proof (cases "(a,B) \<in> 1\<^sub>\<union>\<^sub>\<union>")
      case True
      hence "B = {}"
        by (metis Pair_inject domain_pointwise iu_test_sp_left_zero order_refl)
      hence "D = {}"
        using 1 by fastforce
      hence "(a,D) \<in> t * (R * {})"
        using 1 \<open>(B::'b::type set) = {}\<close> s_prod_def by fastforce
      hence "(a,D) \<in> (t * R) * {}"
        by (metis cl5 s_prod_idl)
      thus ?thesis
        using s_prod_isor by auto
    next
      case False
      hence "(a,B) \<in> A\<^sub>\<union>\<^sub>\<union>"
        using 1 assms by blast
      from this obtain b where 2: "B = {b}"
        by (smt atoms_def Pair_inject mem_Collect_eq)
      hence "D = f b \<and> (b,f b) \<in> R * S"
        using 1 by auto
      from this obtain C g where 3: "(b,C) \<in> R \<and> (\<forall>c\<in>C . (c,g c) \<in> S) \<and> D = \<Union>{ g c | c . c\<in>C }"
        by (clarsimp simp: mr_simp) blast
      have "(a,C) \<in> t * R"
        apply (simp add: mr_simp)
        apply (rule exI[where ?x="B"])
        using 1 2 3 by auto
      thus ?thesis
        using 3 s_prod_def by blast
    qed
    thus "x \<in> (t * R) * S"
      using 1 by auto
  qed
next
  show "(t * R) * S \<subseteq> t * (R * S)"
    using s_prod_assoc1 by blast
qed

lemma iu_unit_below_top_sp_test:
  "1\<^sub>\<union>\<^sub>\<union> \<subseteq> U * R"
  by (clarsimp simp: mr_simp) force

lemma ne_oi_complement_top_sp_test_1:
  "ne (R \<inter> -(U * S)) = R \<inter> -(U * S)"
  using iu_unit_below_top_sp_test by auto

lemma ne_oi_complement_top_sp_test_2:
  "ne R \<inter> -(U * S) = R \<inter> -(U * S)"
  using iu_unit_below_top_sp_test by auto

lemma schroeder_test:
  assumes "test p"
  shows "R * p \<subseteq> S \<longleftrightarrow> -S * p \<subseteq> -R"
  by (metis assms disjoint_eq_subset_Compl double_compl semilattice_inf_class.inf_commute sp_test_dist_oi_right)

lemma complement_test_sp_test:
  "test p \<Longrightarrow> -p * p \<subseteq> -1"
  by (simp add: schroeder_test)

lemma test_sp_commute:
  "test p \<Longrightarrow> test q \<Longrightarrow> p * q = q * p"
  by (metis s_prod_idl sp_test_dist_oi_left sp_test_dist_oi_right test_fix)

lemma test_shunting:
  assumes "test p"
    and "test q"
    and "test r"
  shows "p * q \<subseteq> r \<longleftrightarrow> p \<subseteq> r \<union> \<wrong> q"
proof
  assume 1: "p * q \<subseteq> r"
  have "p = p * q \<union> p * \<wrong> q"
    by (smt (verit, del_insts) Int_Un_distrib assms(1,2) inf_sup_aci(1) inf_sup_ord(2) le_iff_inf s_distl_test s_prod_idr sup_neg_inf)
  also have "... \<subseteq> r \<union> \<wrong> q"
    using 1 by (metis assms(1) inf_le2 sup.mono test_sp)
  finally show "p \<subseteq> r \<union> \<wrong> q"
    .
next
  assume "p \<subseteq> r \<union> \<wrong> q"
  hence "p * q \<subseteq> p * r"
    by (smt (verit) assms boolean_algebra_class.boolean_algebra.double_compl inf.orderE inf_le1 le_inf_iff schroeder_test sup_neg_inf test_double_complement test_s_prod_is_meet test_sp_commute)
  also have "... \<subseteq> r"
    using assms(1) test_sp by auto
  finally show "p * q \<subseteq> r"
    .
qed

lemma test_sp_is_iu:
  "test p \<Longrightarrow> test q \<Longrightarrow> p * q = p \<union>\<union> q"
  by (metis Int_assoc inf.right_idem p_prod_comm s_prod_idr test_p_prod_is_meet test_sp)

lemma test_set:
  "test p \<Longrightarrow> p = { (a,{a}) | a . (a,{a}) \<in> p }"
  using s_id_st by blast

lemma test_sp_is_ii:
  assumes "test p"
    and "test q"
  shows "p * q = p \<inter>\<inter> q"
proof -
  have "p \<inter> q = { (a,{a}) | a . (a,{a}) \<in> p } \<inter> { (a,{a}) | a . (a,{a}) \<in> q }"
    using assms test_set by blast
  also have "... = { (a,{a}) | a . (a,{a}) \<in> p } \<inter>\<inter> { (a,{a}) | a . (a,{a}) \<in> q }"
    apply (rule antisym)
     apply (clarsimp simp: mr_simp)
    apply (rule Int_greatest)
     apply (clarsimp simp: mr_simp)
    by (clarsimp simp: mr_simp)
  also have "... = p \<inter>\<inter> q"
    using test_set[symmetric, OF assms(1)] test_set[symmetric, OF assms(2)] by simp
  finally show "p * q = p \<inter>\<inter> q"
    by (metis assms inf.orderE test_oi_closed test_s_prod_is_meet)
qed

lemma test_galois_1:
  assumes "test p"
    and "test q"
  shows "p * q \<subseteq> r \<longleftrightarrow> q \<subseteq> p \<rightarrow> r"
  by (metis (no_types, lifting) Int_Un_eq(2) assms inf.orderE sup_neg_inf test_double_complement test_s_prod_is_meet test_sp_commute)

lemma test_sp_shunting:
  assumes "test p"
  shows "\<wrong> p * R \<subseteq> {} \<longleftrightarrow> R \<subseteq> p * R"
  apply (rule iffI)
   apply (metis (no_types, opaque_lifting) assms complement_test_sp_top disjoint_eq_subset_Compl double_compl semilattice_inf_class.inf.absorb_iff2 semilattice_inf_class.inf_commute semilattice_inf_class.inf_right_idem test_sp)
  by (metis (no_types, opaque_lifting) assms complement_test_sp_top disjoint_eq_subset_Compl double_compl semilattice_inf_class.inf_commute semilattice_inf_class.inf_le1 subset_antisym test_sp)

lemma test_oU_closed:
  "\<forall>p\<in>X . test p \<Longrightarrow> test (\<Union>X)"
  by blast

lemma test_oI_closed:
  "\<exists>p\<in>X . test p \<Longrightarrow> test (\<Inter>X)"
  by blast

lemma sp_test_dist_oI:
  assumes "test p"
    and "X \<noteq> {}"
  shows "(\<Inter>X) * p = (\<Inter>R\<in>X . R * p)"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply blast
  apply (clarsimp simp: mr_simp)
  subgoal for a C proof -
    assume 1: "\<forall>R\<in>X . \<exists>B . (a,B) \<in> R \<and> (\<exists>f . (\<forall>b\<in>B . (b,f b) \<in> p) \<and> C = \<Union>(f ` B))"
    have 2: "(\<forall>R\<in>X . (a,C) \<in> R \<and> (\<forall>b\<in>C . (b,{b}) \<in> p))"
    proof
      fix R
      assume "R \<in> X"
      from this obtain B where 3: "(a,B) \<in> R \<and> (\<exists>f . (\<forall>b\<in>B . (b,f b) \<in> p) \<and> C = \<Union>(f ` B))"
        using 1 by force
      from this obtain f where 4: "\<forall>b\<in>B . (b,f b) \<in> p" and 5: "C = \<Union>(f ` B)"
        by auto
      hence 6: "\<forall>b\<in>B . f b = {b}"
        using assms(1) test by blast
      hence 7: "C = B"
        using 5 by auto
      hence "(a,C) \<in> R"
        using 3 by auto
      thus "(a,C) \<in> R \<and> (\<forall>b\<in>C . (b,{b}) \<in> p)"
        using 4 6 7 by fastforce
    qed
    show ?thesis
      apply (rule exI[of _ C])
      apply (rule conjI)
      using 2 apply simp
      apply (rule exI[of _ "\<lambda>x . {x}"])
      apply (rule conjI)
      using 2 assms(2) apply blast
      by simp
  qed
  done

lemma test_iU_is_iI:
  assumes "\<forall>i\<in>I . test (X i)"
    and "I \<noteq> {}"
  shows "\<Union>\<Union>X|I = \<Inter>\<Inter>X|I"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
  subgoal for a f proof -
    assume 1: "\<forall>i\<in>I . (a,f i) \<in> X i"
    hence "\<forall>i\<in>I . f i = {a}"
      using assms(1) by (meson test)
    hence "\<Union>(f ` I) = \<Inter>(f ` I) \<and> (\<forall>i\<in>I . (a,f i) \<in> X i)"
      using 1 assms(2) by auto
    thus ?thesis
      by meson
  qed
  apply (clarsimp simp: mr_simp)
  by (metis (no_types, opaque_lifting) INF_eq_const SUP_eq_const assms test)

lemma test_iU_is_oI:
  assumes "\<forall>i\<in>I . test (X i)"
    and "I \<noteq> {}"
  shows "\<Union>\<Union>X|I = \<Inter>(X ` I)"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply (metis (no_types, opaque_lifting) SUP_eq_const assms test)
  apply (clarsimp simp: mr_simp)
  by (metis UN_constant assms(2))

subsection \<open>Domain and antidomain\<close>

declare Dom_def [mr_simp]

abbreviation aDom :: "('a,'b) mrel \<Rightarrow> ('a,'a) mrel" where
  "aDom R \<equiv> \<wrong> Dom R"

lemma ad_set: "aDom R = {(a,{a})| a. \<not>(\<exists>A. (a,A) \<in> R)}"
  by (clarsimp simp: mr_simp) force

lemma d_test:
  "test (Dom R)"
  unfolding Dom_def using s_id_def by fastforce

lemma ad_test:
  "test (aDom R)"
  by simp

lemma ad_expl:
  "aDom R = -((R * 1\<^sub>\<union>\<^sub>\<union>) \<union>\<union> 1) \<inter> 1"
  by (simp add: d_def_expl)

lemma ad_expl_2:
  "aDom (R::('a,'b) mrel) = -((R * (1\<^sub>\<union>\<^sub>\<union>::('b,'a) mrel))\<up>) \<inter> (1::('a,'a) mrel)"
proof
  have "-((R * 1\<^sub>\<union>\<^sub>\<union>)\<up>) \<inter> 1 = -((R * 1\<^sub>\<union>\<^sub>\<union>) \<union>\<union> U) \<inter> 1"
    by simp
  also have "\<dots> \<subseteq> -((R * 1\<^sub>\<union>\<^sub>\<union>) \<union>\<union> 1) \<inter> 1"
    by (metis c6 convex_increasing iu_commute iu_isotone iu_unit sp_unit_convex test_complement_antitone upper_iu_increasing)
  also have "\<dots> = aDom R"
    by (simp add: d_def_expl)
  finally show "-((R * 1\<^sub>\<union>\<^sub>\<union>)\<up>) \<inter> 1 \<subseteq> aDom R"
    using \<open>\<wrong> ((R::('a::type \<times> 'b::type set) set) * 1\<^sub>\<union>\<^sub>\<union>)\<up> \<subseteq> \<wrong> (R * 1\<^sub>\<union>\<^sub>\<union> \<union>\<union> 1)\<close> by blast
  have "aDom R = {(a,{a}) |a. \<not>(\<exists>B. (a,B) \<in> R)}"
    by (simp add: ad_set)
  also have "\<dots> \<subseteq> {(a,{a}) |a. (a,{a}) \<notin> (R * (p_id::('b,'a) mrel))\<up>}"
    by (simp add: U_par_st domain_pointwise)
  also have "\<dots> = {(a,{a}) |a. (a,{a}) \<in> -(R * (p_id::('b,'a) mrel))\<up> \<inter> 1}"
    using test_complement by fastforce
  finally show "aDom R \<subseteq> -((R * (1\<^sub>\<union>\<^sub>\<union>::('b,'a) mrel))\<up>) \<inter> (1::('a,'a) mrel)"
    by blast
qed

lemma aDom:
  "aDom R = { (a,{a}) | a . \<not>(\<exists>B . (a,B) \<in> R) }"
  by (simp add: ad_set)

declare aDom [mr_simp]

lemma d_down_oi_up_1:
  "Dom (R\<down> \<inter> S) = Dom (R \<inter> S\<up>)"
  by (metis Int_commute d_def_expl domain_up_down_conjugate)

lemma d_down_oi_up_2:
  "Dom (R\<down> \<inter> S) = Dom (R\<down> \<inter> S\<up>)"
  by (simp add: d_down_oi_up_1)

lemma d_ne_down_dp_complement_test:
  assumes "test p"
  shows "Dom (R \<inter> -(U * p)) = Dom (ne (R\<down>) * \<wrong> p)"
  by (simp add: assms d_down_oi_up_1 oc_top_sp_test_0 oc_top_sp_test_1 sp_test_dist_oi_right)

lemma d_strict:
  "R = {} \<longleftrightarrow> Dom R = {}"
  using Dom_def by fastforce

lemma d_sp_strict:
  "R * S = {} \<longleftrightarrow> R * Dom S = {}"
  apply (clarsimp simp: mr_simp)
  apply safe
   apply metis
  by (metis UN_singleton)

lemma d_complement_ad:
  "Dom R = \<wrong> aDom R"
  using d_test by blast

lemma down_sp_below_iu_unit:
  "R\<down> * S \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<longleftrightarrow> R \<subseteq> U * aDom (ne S)"
proof -
  have "R\<down> * S \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<longleftrightarrow> ne (R\<down> * S) = {}"
    by (simp add: disjoint_eq_subset_Compl)
  also have "... \<longleftrightarrow> ne (R\<down>) * ne S = {}"
    by (simp add: ne_dist_down_sp)
  also have "... \<longleftrightarrow> ne (R\<down>) * Dom (ne S) = {}"
    using d_sp_strict by auto
  also have "... \<longleftrightarrow> ne (R\<down>) * \<wrong> aDom (ne S) = {}"
    by (metis d_complement_ad)
  also have "... \<longleftrightarrow> R \<subseteq> U * aDom (ne S)"
    by (metis top_sp_test_down_iff_1 top_sp_test_down_iff_2 top_sp_test_down_iff_3 ad_test subset_empty)
  finally show ?thesis
    .
qed

lemma ad_sp_bot:
  "aDom R * R = {}"
  by (simp add: d_s_id_ax d_sp_strict inf_sup_aci(1) sp_test_dist_oi_left)

lemma sp_top_d:
  "R * U \<subseteq> Dom R * U"
  by (simp add: cl8_var iu_unit_up sp_upper_left_isotone)

lemma d_sp_top:
  "Dom (R * U) = Dom R"
  by (clarsimp simp: mr_simp) blast

lemma d_down:
  "Dom (R\<down>) = Dom R"
  by (metis U_par_idem d_down_oi_up_1 inf.orderE top_down top_lower_greatest)

lemma d_up:
  "Dom (R\<up>) = Dom R"
  by (metis Int_absorb1 U_par_idem d_down_oi_up_1 top_down top_upper_least)

lemma d_isotone:
  "R \<subseteq> S \<Longrightarrow> Dom R \<subseteq> Dom S"
  unfolding Dom_def by blast

lemma ad_antitone:
  "R \<subseteq> S \<Longrightarrow> aDom S \<subseteq> aDom R"
  by (simp add: Int_commute d_isotone semilattice_inf_class.le_infI2)

lemma d_dist_ou:
  "Dom (R \<union> S) = Dom R \<union> Dom S"
  unfolding Dom_def by blast

lemma d_dist_iu:
  "Dom (R \<union>\<union> S) = Dom R * Dom S"
  by (clarsimp simp: mr_simp) auto

lemma d_dist_ii:
  "Dom (R \<inter>\<inter> S) = Dom R * Dom S"
  by (metis antisym_conv d_U d_dist_iu d_down d_isotone ii_convex_iu s_prod_idr)

lemma d_loc:
  "Dom (R * Dom S) = Dom (R * S)"
  apply (clarsimp simp: mr_simp)
  apply safe
   apply metis
  by (metis UN_singleton)

lemma ad_loc:
  "aDom (R * Dom S) = aDom (R * S)"
  by simp

lemma d_ne_down:
  "Dom (ne (R\<down>)) = Dom (ne R)"
  by (metis atoms_solution d_down_oi_up_1 d_down_oi_up_2)

lemma ne_sp_iu_unit_up:
  "ne R = R \<Longrightarrow> (R * 1\<^sub>\<union>\<^sub>\<union>)\<up> = R * U"
  apply (clarsimp simp: mr_simp)
  apply safe
   apply (metis (no_types, lifting) Compl_iff IntE Inter_iff UNIV_I UN_simps(2) image_eqI singletonI)
  apply clarsimp
  by (metis SUP_bot sup_bot_left)

lemma ne_d_expl:
  "ne R = R \<Longrightarrow> Dom R = R * U \<inter> 1"
  by (metis cl8_var d_def_expl d_test ne_sp_iu_unit_up test_sp)

lemma ne_a_expl:
  "ne R = R \<Longrightarrow> aDom R = -(R * U) \<inter> 1"
  by (simp add: ad_expl_2 ne_sp_iu_unit_up)

lemma d_dist_oU:
  "Dom (\<Union>X) = \<Union>(Dom ` X)"
  apply (clarsimp simp: mr_simp)
  by blast

lemma d_dist_iU_iI:
  "Dom (\<Union>\<Union>X|I) = Dom (\<Inter>\<Inter>X|I)"
  by (clarsimp simp: mr_simp)

lemma d_dist_iU_oI:
  assumes "I \<noteq> {}"
  shows "Dom (\<Union>\<Union>X|I) = \<Inter>(Dom ` X ` I)"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply blast
  apply (clarsimp simp: mr_simp)
  by (meson all_not_in_conv assms)

subsection \<open>Left residual\<close>

definition sp_lres :: "('a,'c) mrel \<Rightarrow> ('b,'c) mrel \<Rightarrow> ('a,'b) mrel" (infixl "\<oslash>" 65) where
  "Q \<oslash> R \<equiv> { (a,B) . \<forall>f . (\<forall>b \<in> B . (b,f b) \<in> R) \<longrightarrow> (a,\<Union>{ f b | b . b \<in> B }) \<in> Q }"

declare sp_lres_def [mr_simp]

lemma sp_lres_galois:
  "S * R \<subseteq> Q \<longleftrightarrow> S \<subseteq> Q \<oslash> R"
proof
  assume 1: "S * R \<subseteq> Q"
  show "S \<subseteq> Q \<oslash> R"
  proof
    fix x
    assume "x \<in> S"
    from this obtain a B where 2: "x = (a,B) \<and> (a,B) \<in> S"
      by (metis surj_pair)
    have "\<forall>f . (\<forall>b \<in> B . (b,f b) \<in> R) \<longrightarrow> (a,\<Union>{ f b | b . b \<in> B }) \<in> Q"
    proof (rule allI, rule impI)
      fix f
      assume "\<forall>b \<in> B . (b,f b) \<in> R"
      hence "(a,\<Union>{ f b | b . b \<in> B }) \<in> S * R"
        apply (unfold s_prod_def)
        using 2 by auto
      thus "(a,\<Union>{ f b | b . b \<in> B }) \<in> Q"
        using 1 by auto
    qed
    thus "x \<in> Q \<oslash> R"
      using 2 sp_lres_def by auto
  qed
next
  assume 3: "S \<subseteq> Q \<oslash> R"
  have "(Q \<oslash> R) * R \<subseteq> Q"
  proof
    fix x
    assume "x \<in> (Q \<oslash> R) * R"
    from this obtain a D where 4: "x = (a,D) \<and> (a,D) \<in> (Q \<oslash> R) * R"
      by (metis surj_pair)
    from this obtain C where "(a,C) \<in> Q \<oslash> R \<and> (\<exists>g . (\<forall>c\<in>C . (c,g c) \<in> R) \<and> D = \<Union>{ g c | c . c \<in> C })"
      by (simp add: mr_simp) blast
    thus "x \<in> Q"
      apply (unfold sp_lres_def)
      using 4 by auto
  qed
  thus "S * R \<subseteq> Q"
    using 3 by (meson dual_order.trans s_prod_isol)
qed

lemma sp_lres_expl:
  "Q \<oslash> R = \<Union>{ S . S * R \<subseteq> Q }"
  using sp_lres_galois by blast

lemma bot_sp_lres_d:
  "{} \<oslash> R = {} \<oslash> Dom R"
  by (metis d_sp_strict order_refl sp_lres_galois subset_antisym subset_empty)

lemma bot_sp_lres_expl:
  "{} \<oslash> R = -(U * Dom R)"
  apply (rule antisym)
   apply (metis d_sp_strict d_test disjoint_eq_subset_Compl order_refl sp_lres_galois sp_test subset_empty)
  by (metis Compl_disjoint2 bot_sp_lres_d d_test sp_lres_galois sp_test subset_empty)

lemma sp_lres_sp_below:
  "(Q \<oslash> R) * R \<subseteq> Q"
  by (simp add: sp_lres_galois)

lemma sp_lres_left_isotone:
  "Q \<subseteq> S \<Longrightarrow> Q \<oslash> R \<subseteq> S \<oslash> R"
  by (meson dual_order.refl sp_lres_galois subset_trans)

lemma sp_lres_right_antitone:
  "S \<subseteq> R \<Longrightarrow> Q \<oslash> R \<subseteq> Q \<oslash> S"
  by (meson dual_order.trans s_prod_isor sp_lres_galois sp_lres_sp_below)

lemma sp_lres_down_closed_1:
  "Q\<down> \<oslash> R = Q\<down> \<oslash> R\<down>"
proof
  show "Q\<down> \<oslash> R \<subseteq> Q\<down> \<oslash> R\<down>"
    by (metis down_dist_sp down_idempotent down_isotone sp_lres_galois sp_lres_sp_below)
next
  show "Q\<down> \<oslash> R\<down> \<subseteq> Q\<down> \<oslash> R"
    by (simp add: lower_reflexive sp_lres_right_antitone)
qed

lemma sp_lres_down_closed_2:
  assumes "R\<down> = R"
    and "total T"
  shows "(R \<oslash> T)\<down> = R \<oslash> T"
proof -
  have "(R \<oslash> T)\<down> \<subseteq> R \<oslash> T"
    by (metis assms lower_transitive sp_lres_galois sp_lres_sp_below total_down_sp_semi_commute)
  thus ?thesis
    by (simp add: lower_reflexive subset_antisym)
qed

lemma down_sp_sp:
  "R\<down> * S = R * (1\<^sub>\<union>\<^sub>\<union> \<union> S)"
proof -
  have "R\<down> * S = R * (1\<^sub>\<union>\<^sub>\<union> \<union> 1) * S"
    by (simp add: down_sp)
  also have "... = R * ((1\<^sub>\<union>\<^sub>\<union> \<union> 1) * S)"
    by (simp add: test_iu_test_sp_assoc_3)
  also have "... = R * (1\<^sub>\<union>\<^sub>\<union> \<union> S)"
    apply (clarsimp simp: mr_simp)
    apply safe
     apply (smt (z3) Sup_empty ccpo_Sup_singleton image_empty image_insert singletonI)
    by (smt (verit, del_insts) Sup_empty all_not_in_conv ccpo_Sup_singleton image_insert image_is_empty singletonD)
  finally show ?thesis
    .
qed

lemma iu_unit_sp_lres_iu_unit_ou:
  "U * aDom (ne R) = 1\<^sub>\<union>\<^sub>\<union> \<oslash> (1\<^sub>\<union>\<^sub>\<union> \<union> R)"
  apply (rule antisym)
   apply (metis down_sp_sp sp_lres_galois down_sp_below_iu_unit order_refl)
  by (metis down_sp_sp sp_lres_galois down_sp_below_iu_unit order_refl)

lemma bot_sl_below_complement_d:
  "{} \<oslash> R \<subseteq> - Dom R"
  by (metis Compl_anti_mono bot_sp_lres_expl d_test dual_order.refl inf.order_iff sp_test test_s_prod_is_meet)

lemma sp_unit_oi_bot_sp_lres:
  "1 \<inter> - Dom R = 1 \<inter> ({} \<oslash> R)"
  by (smt (verit, ccfv_SIG) ad_sp_bot boolean_algebra_cancel.inf1 bot_sl_below_complement_d inf.orderE inf_bot_right inf_commute inf_le2 sp_lres_galois)

lemma ad_explicit_d:
  "aDom R = -(U * Dom R) \<inter> 1"
  by (simp add: bot_sp_lres_expl lattice_class.inf_sup_aci(1) sp_unit_oi_bot_sp_lres)

lemma top_test_sp_lres_total_expl_1:
  assumes "test p"
  shows "\<forall>S . S\<down> \<subseteq> (U * p) \<oslash> R \<longleftrightarrow> S \<subseteq> U * aDom (R \<inter> -(U * p))"
proof
  fix S::"('b,'c) mrel"
  have "S \<subseteq> U * aDom (R \<inter> -(U * p)) \<longleftrightarrow> ne (S\<down>) * Dom (R \<inter> -(U * p)) = {}"
    by (metis (no_types, lifting) d_complement_ad inf_le2 subset_empty top_sp_test_down_iff_1 top_sp_test_down_iff_2 top_sp_test_down_iff_3)
  also have "... \<longleftrightarrow> ne (S\<down>) * Dom (ne (R\<down>) * \<wrong> p) = {}"
    by (simp add: assms d_ne_down_dp_complement_test)
  also have "... \<longleftrightarrow> ne (S\<down>) * (ne (R\<down>) * \<wrong> p) = {}"
    using d_sp_strict by auto
  also have "... \<longleftrightarrow> ne (S\<down>) * ne (R\<down>) * \<wrong> p = {}"
    by (simp add: test_assoc3)
  also have "... \<longleftrightarrow> ne ((S\<down> * R)\<down>) * \<wrong> p = {}"
    by (simp add: down_dist_sp ne_dist_down_sp)
  also have "... \<longleftrightarrow> S\<down> * R \<subseteq> U * p"
    by (metis assms top_sp_test_down_iff_1 top_sp_test_down_iff_2 top_sp_test_down_iff_3 subset_empty)
  also have "... \<longleftrightarrow> S\<down> \<subseteq> (U * p) \<oslash> R"
    by (simp add: sp_lres_galois)
  finally show "S\<down> \<subseteq> (U * p) \<oslash> R \<longleftrightarrow> S \<subseteq> U * aDom (R \<inter> -(U * p))"
    by simp
qed

lemma top_test_sp_lres_total_expl_2:
  assumes "test p"
    and "total T"
  shows "(U * p) \<oslash> T = U * aDom (T \<inter> -(U * p))"
proof -
  have "\<forall>S . S \<subseteq> (U * p) \<oslash> T \<longleftrightarrow> S \<subseteq> U * aDom (T \<inter> -(U * p))"
    by (smt assms lower_reflexive sp_lres_down_closed_2 subset_trans top_sp_test_down_closed top_test_sp_lres_total_expl_1)
  thus ?thesis
    by blast
qed

lemma top_test_sp_lres_total_expl_3:
  assumes "test p"
  shows "((U * p) \<oslash> R) \<inter> 1 = aDom (R \<inter> -(U * p))"
proof
  have "(((U * p) \<oslash> R) \<inter> 1)\<down> * R = (((U * p) \<oslash> R) \<inter> 1) * (1\<^sub>\<union>\<^sub>\<union> \<union> R)"
    using down_sp_sp by blast
  also have "... = (((U * p) \<oslash> R) \<inter> 1) * 1\<^sub>\<union>\<^sub>\<union> \<union> (((U * p) \<oslash> R) \<inter> 1) * R"
    by (simp add: s_distl_test)
  also have "... \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<union> (((U * p) \<oslash> R) \<inter> 1) * R"
    using c6 by auto
  also have "... \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<union> ((U * p) \<oslash> R) * R"
    by (metis Un_Int_eq(4) inf_le2 iu_unit_convex iu_unit_down sp_oi_subdist sup.mono)
  also have "... \<subseteq> 1\<^sub>\<union>\<^sub>\<union> \<union> U * p"
    using sp_lres_sp_below by auto
  also have "... = U * p"
    by (simp add: iu_unit_below_top_sp_test sup.absorb2)
  finally have "(((U * p) \<oslash> R) \<inter> 1)\<down> \<subseteq> (U * p) \<oslash> R"
    by (simp add: sp_lres_galois)
  hence "((U * p) \<oslash> R) \<inter> 1 \<subseteq> U * aDom (R \<inter> -(U * p))"
    by (metis assms top_test_sp_lres_total_expl_1)
  thus "((U * p) \<oslash> R) \<inter> 1 \<subseteq> aDom (R \<inter> -(U * p))"
    by (metis (no_types, lifting) inf.idem inf.orderE inf_commute sp_oi_subdist sp_test test_s_prod_is_meet)
next
  have "aDom (R \<inter> -(U * p)) = U * aDom (R \<inter> -(U * p)) \<inter> 1"
    by (metis (no_types, lifting) inf.absorb_iff2 inf.idem inf_commute inf_le2 sp_test test_s_prod_is_meet)
  thus "aDom (R \<inter> -(U * p)) \<subseteq> ((U * p) \<oslash> R) \<inter> 1"
    by (metis Int_mono ad_test assms order_refl top_sp_test_down_closed top_test_sp_lres_total_expl_1)
qed

lemma top_test_sp_lres_total_expl_4:
  assumes "test p"
  shows "aDom (ne (R\<down>) * \<wrong> p) = ((U * p) \<oslash> R) \<inter> 1"
  by (simp add: assms d_ne_down_dp_complement_test top_test_sp_lres_total_expl_3)

lemma oi_complement_top_sp_test_top_1:
  assumes "test p"
  shows "(R \<inter> -(U * p)) * U = (R\<down> \<inter> -(U * p)) * U"
proof (rule antisym)
  show "(R \<inter> -(U * p)) * U \<subseteq> (R\<down> \<inter> -(U * p)) * U"
    by (metis (no_types, lifting) assms cl8_var d_down_oi_up_1 equalityD2 ne_oi_complement_top_sp_test_1 ne_sp_iu_unit_up oc_top_sp_test_up_closed)
next
  have "R\<down> \<inter> -(U * p) \<subseteq> (R \<inter> -(U * p))\<down>"
    by (metis oc_top_sp_test_up_closed down_oi_up_closed assms)
  also have "... \<subseteq> (R \<inter> -(U * p)) * U"
    by (simp add: down_below_sp_top)
  finally show "(R\<down> \<inter> -(U * p)) * U \<subseteq> (R \<inter> -(U * p)) * U"
    by (metis assms domain_up_down_conjugate inf_commute ne_oi_complement_top_sp_test_1 ne_sp_iu_unit_up oc_top_sp_test_up_closed set_eq_subset)
qed

lemma oi_complement_top_sp_test_top_2:
  assumes "test p"
  shows "(R\<down> \<inter> -(U * p)) * U = ne (R\<down>) * \<wrong> p * U"
proof (rule antisym)
  have "R\<down> \<inter> -(U * p) * U \<subseteq> Dom (R\<down> \<inter> -(U * p)) * U"
    using sp_top_d by blast
  also have "... = Dom (ne (R\<down>) * \<wrong> p) * U"
    by (simp add: assms d_ne_down_dp_complement_test)
  also have "... = Dom (ne (R\<down> * \<wrong> p)) * U"
    by (simp add: ne_sp_test)
  also have "... = ne (R\<down> * \<wrong> p) * U"
    by (simp add: cl8_var ne_sp_iu_unit_up)
  also have "... = ne (R\<down>) * \<wrong> p * U"
    by (simp add: ne_sp_test)
  finally show "(R\<down> \<inter> -(U * p)) * U \<subseteq> ne (R\<down>) * \<wrong> p * U"
    .
next
  have "ne (R\<down>) * \<wrong> p \<subseteq> -(U * p)"
    by (metis assms disjoint_eq_subset_Compl double_complement inf_compl_bot_right schroeder_test sp_test test_complement_closed top_test_oi_top_complement)
  thus "ne (R\<down>) * \<wrong> p * U \<subseteq> (R\<down> \<inter> -(U * p)) * U"
    by (metis (no_types) assms cl8_var d_down_oi_up_1 d_ne_down_dp_complement_test ne_oi_complement_top_sp_test_1 ne_sp_iu_unit_up oc_top_sp_test_up_closed sp_top_d)
qed

lemma oi_complement_top_sp_test_top_3:
  assumes "test p"
  shows "(R\<down> \<inter> -(U * p)) * U = ne (R\<down>) * -(p * U)"
  by (simp add: assms complement_test_sp_top oi_complement_top_sp_test_top_2 test_assoc1)

lemma split_sp_test_2:
  "test p \<Longrightarrow> R \<subseteq> R * p \<union> ne (R\<down>) * (\<wrong> p)\<up>"
proof -
  assume "test p"
  hence "R \<subseteq> R * p \<union> (ne (R\<down> * \<wrong> p))\<up>"
    by (smt (verit, best) IntE UnCI UnE split_sp_test subsetI)
  thus "R \<subseteq> R * p \<union> ne (R\<down>) * (\<wrong> p)\<up>"
    by (simp add: ne_sp_test_up)
qed

lemma split_sp_test_3:
  "test p \<Longrightarrow> R \<subseteq> R * p \<union> R\<down> * (\<wrong> p)\<up>"
  by (smt IntE UnCI UnE ne_dist_down_sp ne_sp_test_up ne_test_up split_sp_test subsetI)

lemma split_sp_test_4:
  assumes "test p"
    and "test q"
  shows "R * (p \<union> q) \<subseteq> R * p \<union> ne (R\<down>) * q\<up>"
proof -
  have 1: "(p \<union> q) * p = p"
    by (metis Un_Int_eq(1) assms sp_test_dist_oi_left test_ou_closed test_sp_commute test_sp_idempotent)
  have "(R * (p \<union> q))\<down> * \<wrong> p \<subseteq> R\<down> * q"
  proof -
    have "(R * (p \<union> q))\<down> * \<wrong> p = R * (p \<union> q) * (1\<^sub>\<union>\<^sub>\<union> \<union> \<wrong> p)"
      using down_sp_sp by blast
    also have "... = R * ((p \<union> q) * 1\<^sub>\<union>\<^sub>\<union> \<union> (p \<union> q) * \<wrong> p)"
      by (smt (verit) assms inf.orderE s_distl_test test_assoc1 test_ou_closed)
    also have "... \<subseteq> R * (1\<^sub>\<union>\<^sub>\<union> \<union> (p \<union> q) * \<wrong> p)"
      by (meson c6 s_prod_isor subset_refl sup.mono)
    also have "... = R\<down> * ((p \<union> q) * \<wrong> p)"
      using down_sp_sp by blast
    also have "... = R\<down> * (p * \<wrong> p \<union> q * \<wrong> p)"
      by (metis assms ii_right_dist_ou inf_commute inf_le1 test_ou_closed test_sp_is_ii)
    also have "... = R\<down> * (q * \<wrong> p)"
      by (metis Compl_disjoint assms(1) inf_commute inf_le1 s_prod_idl sp_test_dist_oi_left subset_Un_eq test_sp_commute)
    also have "... \<subseteq> R\<down> * q"
      by (metis inf_le1 inf_le2 s_prod_isor sp_test)
    finally show ?thesis
      .
  qed
  hence 2: "ne ((R * (p \<union> q))\<down>) * \<wrong> p \<subseteq> ne (R\<down>) * q"
    by (metis assms(2) inf_le2 ne_dist_ou ne_sp_test subset_Un_eq)
  have "R * (p \<union> q) \<subseteq> R * (p \<union> q) * p \<union> ne ((R * (p \<union> q))\<down>) * (\<wrong> p)\<up>"
    by (simp add: assms split_sp_test_2)
  also have "... = R * p \<union> ne ((R * (p \<union> q))\<down>) * (\<wrong> p)\<up>"
    using 1 by (metis assms(1) inf.orderE test_assoc3)
  also have "... \<subseteq> R * p \<union> ne (R\<down>) * q\<up>"
    using 2 by (metis (no_types, lifting) Un_Int_eq(1) assms(2) inf_le2 iu_isotone ne_sp_test ne_sp_test_up sup.mono)
  finally show ?thesis
    .
qed

lemma split_sp_test_5:
  assumes "test p"
    and "test q"
  shows "R * (p \<union> q) \<subseteq> R * p \<union> R\<down> * q\<up>"
proof -
  have "R * (p \<union> q) \<subseteq> R * p \<union> ne (R\<down>) * q\<up>"
    by (simp add: assms split_sp_test_4)
  thus ?thesis
    by (metis (no_types, lifting) assms(2) le_inf_iff ne_dist_down_sp ne_test_up sup_neg_inf)
qed

lemma split_sp_test_6:
  assumes "test p"
    and "test q"
  shows "Dom (R * (p \<union> q)) \<subseteq> Dom (R * p \<union> ne (R\<down>) * q)"
proof -
  have "Dom (R * (p \<union> q)) \<subseteq> Dom (R * p \<union> ne (R\<down>) * q\<up>)"
    by (simp add: assms d_isotone split_sp_test_4)
  also have "... = Dom (R * p \<union> (ne (R\<down>) * q)\<up>)"
    by (simp add: assms(2) ne_sp_test ne_sp_test_up)
  also have "... \<subseteq> Dom (R * p \<union> ne (R\<down>) * q)"
    by (metis d_up subsetI up_dist_ou up_idempotent)
  finally show ?thesis
    .
qed

lemma split_sp_test_7:
  assumes "test p"
    and "test q"
  shows "Dom (ne (R\<down>) * (p \<union> q)) = Dom (ne (R\<down>) * p \<union> ne (R\<down>) * q)"
  apply (rule antisym)
   apply (metis assms ne_down_idempotent split_sp_test_6)
  by (smt (verit, ccfv_SIG) Un_Int_eq(1) Un_subset_iff assms(2) d_isotone inf.orderE inf_le1 le_inf_iff lower_eq_down ne_dist_ou sp_oi_subdist_2 subset_Un_eq sup.mono)

lemma test_sp_left_dist_iu_1:
  "test p \<Longrightarrow> p * (R \<union>\<union> S) = p * R \<union>\<union> S"
  by (metis cl8_var inf.orderE p_prod_assoc s_subid_iff2)

lemma test_sp_left_dist_iu_2:
  "test p \<Longrightarrow> p * (R \<union>\<union> S) = R \<union>\<union> p * S"
  by (metis iu_commute test_sp_left_dist_iu_1)

lemma d_sp_below_iu_down:
  "Dom R * S \<subseteq> (R \<union>\<union> S)\<down>"
  by (simp add: cl8_var iu_lower_left_isotone sp_iu_unit_lower)

lemma d_sp_ne_down_below_ne_iu_down:
  "Dom R * ne (S\<down>) \<subseteq> ne ((R \<union>\<union> S)\<down>)"
proof -
  have "Dom R * S\<down> \<subseteq> (R \<union>\<union> S)\<down>"
    by (simp add: cl8_var iu_lower_isotone sp_iu_unit_lower)
  hence "ne (Dom R * S\<down>) \<subseteq> ne ((R \<union>\<union> S)\<down>)"
    by blast
  thus ?thesis
    by (smt d_test test_sp_ne)
qed

lemma top_test:
  "test p \<Longrightarrow> U * p = { (a,B) . (\<forall>b\<in>B . (b,{b}) \<in> p) }"
  apply (unfold test)
  apply (clarsimp simp: mr_simp)
  by fastforce

lemma iu_oi_complement_top_test_ou_up:
  "test p \<Longrightarrow> (R \<union>\<union> S) \<inter> -(U * p) \<subseteq> ((R \<union> S) \<inter> -(U * p))\<up>"
  apply (unfold top_test)
  apply (clarsimp simp: mr_simp)
  by blast

lemma d_ne_iu_down_sp_test_ou:
  assumes "test p"
  shows "Dom (ne ((R \<union>\<union> S)\<down>) * p) \<subseteq> Dom ((ne (R\<down>) \<union> ne (S\<down>)) * p)"
proof -
  have "Dom (ne ((R \<union>\<union> S)\<down>) * p) = Dom ((R \<union>\<union> S) \<inter> -(U * \<wrong> p))"
    by (metis assms d_ne_down_dp_complement_test test_double_complement)
  also have "... \<subseteq> Dom ((R \<union> S) \<inter> -(U * \<wrong> p))"
    by (metis iu_oi_complement_top_test_ou_up d_isotone d_up semilattice_inf_class.inf_le2)
  also have "... = Dom (ne ((R \<union> S)\<down>) * p)"
    by (metis assms d_ne_down_dp_complement_test test_double_complement)
  finally show ?thesis
    by (simp add: down_dist_ou ne_dist_ou)
qed

lemma test_sp_left_dist_iU:
  assumes "test p"
    and "I \<noteq> {}"
  shows "p * (\<Union>\<Union>X|I) = \<Union>\<Union>(\<lambda>i . p * X i)|I"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
  subgoal for a B f proof -
    assume 1: "(a,B) \<in> p"
    hence 2: "B = {a}"
      by (metis assms(1) test)
    assume "\<forall>b\<in>B . \<exists>g . f b = \<Union>(g ` I) \<and> (\<forall>i\<in>I . (b,g i) \<in> X i)"
    from this obtain g where 3: "f a = \<Union>(g ` I) \<and> (\<forall>i\<in>I . (a,g i) \<in> X i)"
      using 2 by auto
    have "\<Union>(f ` B) = \<Union>(g ` I) \<and> (\<forall>i\<in>I . \<exists>B . (a,B) \<in> p \<and> (\<exists>f . (\<forall>b\<in>B . (b,f b) \<in> X i) \<and> g i = \<Union>(f ` B)))"
      apply (rule conjI)
      using 2 3 apply blast
      apply (rule ballI)
      apply (rule exI[of _ B])
      apply (rule conjI)
      using 1 apply simp
      subgoal for i
        apply (rule exI[of _ "\<lambda>b . g i"])
        using 2 3 by blast
      done
    thus ?thesis
      by auto
  qed
  apply (clarsimp simp: mr_simp)
  subgoal for a f proof -
    assume 4: "\<forall>i\<in>I . \<exists>B . (a,B) \<in> p \<and> (\<exists>g . (\<forall>b\<in>B . (b,g b) \<in> X i) \<and> f i = \<Union>(g ` B))"
    have "(a,{a}) \<in> p \<and> (\<exists>g . (\<forall>b\<in>{a} . \<exists>f . g b = \<Union>(f ` I) \<and> (\<forall>i\<in>I . (b,f i) \<in> X i)) \<and> \<Union>(f ` I) = \<Union>(g ` {a}))"
      apply (rule conjI)
      using 4 apply (metis assms equals0I test)
      apply (rule exI[of _ "\<lambda>a . \<Union>(f ` I)"])
      apply clarsimp
      apply (rule exI[of _ f])
      using 4 assms(1) test by fastforce
    thus ?thesis
      by auto
  qed
  done

subsection \<open>Modal operations\<close>

definition adia :: "('a,'b) mrel \<Rightarrow> ('b,'b) mrel \<Rightarrow> ('a,'a) mrel" ("| _ \<rangle> _" [50,90] 95) where
  "|R\<rangle>p \<equiv> { (a,{a}) | a . \<exists>B . (a,B) \<in> R \<and> (\<forall>b\<in>B . (b,{b}) \<in> p) }"

definition abox :: "('a,'b) mrel \<Rightarrow> ('b,'b) mrel \<Rightarrow> ('a,'a) mrel" ("| _ ] _" [50,90] 95) where
  "|R]p \<equiv> { (a,{a}) | a . \<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>b\<in>B . (b,{b}) \<in> p) }"

definition edia :: "('a,'b) mrel \<Rightarrow> ('b,'b) mrel \<Rightarrow> ('a,'a) mrel" ("| _ \<rangle>\<rangle> _" [50,90] 95) where
  "|R\<rangle>\<rangle>p \<equiv> { (a,{a}) | a . \<exists>B . (a,B) \<in> R \<and> (\<exists>b\<in>B . (b,{b}) \<in> p) }"

definition ebox :: "('a,'b) mrel \<Rightarrow> ('b,'b) mrel \<Rightarrow> ('a,'a) mrel" ("| _ ]] _" [50,90] 95) where
  "|R]]p \<equiv> { (a,{a}) | a . \<forall>B . (a,B) \<in> R \<longrightarrow> (\<exists>b\<in>B . (b,{b}) \<in> p) }"

declare adia_def [mr_simp] abox_def [mr_simp] edia_def [mr_simp] ebox_def [mr_simp]

lemma adia:
  assumes "test p"
  shows "|R\<rangle>p = Dom (R * p)"
proof
  show "|R\<rangle>p \<subseteq> Dom (R * p)"
  proof
    fix x
    assume "x \<in> |R\<rangle>p"
    from this obtain a B where 1: "x = (a,{a}) \<and> (a,B) \<in> R \<and> (\<forall>b\<in>B . (b,{b}) \<in> p)"
      by (smt adia_def surj_pair mem_Collect_eq)
    have "(a,B) \<in> R * p"
      apply (clarsimp simp: s_prod_def)
      apply (rule exI[where ?x="B"])
      apply (rule conjI)
      using 1 apply simp
      apply (rule exI[where ?x="\<lambda>x . {x}"])
      using 1 by auto
    thus "x \<in> Dom (R * p)"
      using 1 Dom_def by auto
  qed
next
  show "Dom (R * p) \<subseteq> |R\<rangle>p"
  proof
    fix x
    assume "x \<in> Dom (R * p)"
    from this obtain a A where 2: "x = (a,{a}) \<and> (a,A) \<in> R * p"
      by (smt Dom_def surj_pair mem_Collect_eq)
    from this obtain B f where 3: "(a,B) \<in> R \<and> (\<forall>b\<in>B . (b,f b) \<in> p) \<and> A = \<Union>{ f b | b . b \<in> B }"
      by (simp add: mr_simp) blast
    hence "\<forall>b\<in>B . (b,{b}) \<in> p"
      using assms subid_aux2 by fastforce
    thus "x \<in> |R\<rangle>p"
      using 2 3 adia_def by blast
  qed
qed

lemma abox_1:
  assumes "test p"
  shows "|R]p = aDom (R \<inter> -(U * p))"
proof
  show "|R]p \<subseteq> aDom (R \<inter> -(U * p))"
  proof
    fix x
    assume "x \<in> |R]p"
    from this obtain a where 1: "x = (a,{a}) \<and> (\<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>b\<in>B . (b,{b}) \<in> p))"
      by (smt abox_def surj_pair mem_Collect_eq)
    have "\<not>(\<exists>B . (a,B) \<in> R \<inter> -(U * p))"
    proof
      assume "\<exists>B . (a,B) \<in> R \<inter> -(U * p)"
      from this obtain B where "(a,B) \<in> R \<and> (a,B) \<notin> U * p"
        by auto
      thus False
        using 1 by (metis (no_types, lifting) assms top_sp_test)
    qed
    thus "x \<in> aDom (R \<inter> -(U * p))"
      using 1 aDom by blast
  qed
next
  show "aDom (R \<inter> -(U * p)) \<subseteq> |R]p"
  proof
    fix x
    assume "x \<in> aDom (R \<inter> -(U * p))"
    from this obtain a where 2: "x = (a,{a}) \<and> \<not>(\<exists>B . (a,B) \<in> R \<inter> -(U * p))"
      by (smt aDom surj_pair mem_Collect_eq)
    hence "\<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>b\<in>B . (b,{b}) \<in> p)"
      using assms by (metis (no_types, lifting) IntI oc_top_sp_test)
    thus "x \<in> |R]p"
      using 2 abox_def by blast
  qed
qed

lemma abox:
  assumes "test p"
  shows "|R]p = aDom (ne (R\<down>) * \<wrong> p)"
  by (simp add: abox_1 assms d_ne_down_dp_complement_test)

lemma edia_1:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p = Dom (R \<inter> -(U * \<wrong> p))"
proof
  show "|R\<rangle>\<rangle>p \<subseteq> Dom (R \<inter> -(U * \<wrong> p))"
  proof
    fix x
    assume "x \<in> |R\<rangle>\<rangle>p"
    from this obtain a b B where 1: "x = (a,{a}) \<and> (a,B) \<in> R \<and> b \<in> B \<and> (b,{b}) \<in> p"
      by (smt edia_def surj_pair mem_Collect_eq)
    hence "(a,B) \<in> -(U * \<wrong> p)"
      by (metis (no_types, lifting) lattice_class.inf_sup_ord(2) oc_top_sp_test test_complement)
    thus "x \<in> Dom (R \<inter> -(U * \<wrong> p))"
      using 1 Dom_def by auto
  qed
next
  show "Dom (R \<inter> -(U * \<wrong> p)) \<subseteq> |R\<rangle>\<rangle>p"
  proof
    fix x
    assume "x \<in> Dom (R \<inter> -(U * \<wrong> p))"
    from this obtain a B where 2: "x = (a,{a}) \<and> (a,B) \<in> R \<and> (a,B) \<in> -(U * \<wrong> p)"
      by (smt Dom_def surj_pair mem_Collect_eq IntE)
    hence "\<exists>b\<in>B . (b,{b}) \<in> p"
      by (meson oc_top_sp_test test_complement test_complement_closed)
    thus "x \<in> |R\<rangle>\<rangle>p"
      using 2 edia_def by blast
  qed
qed

lemma edia:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p = Dom (ne (R\<down>) * p)"
  by (metis assms d_ne_down_dp_complement_test edia_1 test_double_complement)

lemma ebox:
  assumes "test p"
  shows "|R]]p = aDom (R * \<wrong> p)"
proof
  show "|R]]p \<subseteq> aDom (R * \<wrong> p)"
  proof
    fix x
    assume "x \<in> |R]]p"
    from this obtain a where 1: "x = (a,{a}) \<and> (\<forall>B . (a,B) \<in> R \<longrightarrow> (\<exists>b\<in>B . (b,{b}) \<in> p))"
      by (smt ebox_def surj_pair mem_Collect_eq)
    hence "\<not>(\<exists>B . (a,B) \<in> R * \<wrong> p)"
      by (metis (no_types, lifting) s_prod_test test_complement)
    thus "x \<in> aDom (R * \<wrong> p)"
      using 1 aDom by blast
  qed
next
  show "aDom (R * \<wrong> p) \<subseteq> |R]]p"
  proof
    fix x
    assume "x \<in> aDom (R * \<wrong> p)"
    from this obtain a where 2: "x = (a,{a}) \<and> \<not>(\<exists>B . (a,B) \<in> R * \<wrong> p)"
      by (smt aDom surj_pair mem_Collect_eq)
    have "\<forall>B . (a,B) \<in> R \<longrightarrow> (\<exists>b\<in>B . (b,{b}) \<in> p)"
    proof (rule allI, rule impI)
      fix B
      assume "(a,B) \<in> R"
      hence "(a,B) \<notin> U * \<wrong> p"
        using 2 by (metis Int_iff Int_lower2 sp_test)
      thus "\<exists>b\<in>B . (b,{b}) \<in> p"
        by (meson test_complement test_complement_closed top_sp_test)
    qed
    thus "x \<in> |R]]p"
      using 2 ebox_def by blast
  qed
qed

lemma abox_2:
  assumes "test p"
  shows "|R]p = -((R \<inter> -(U * p)) * U) \<inter> 1"
  by (simp add: abox_1 assms ne_a_expl ne_oi_complement_top_sp_test_1)

lemma abox_3:
  assumes "test p"
  shows "|R]p = -(ne (R\<down>) * \<wrong> p * U) \<inter> 1"
  by (simp add: abox assms ne_a_expl ne_sp_test)

lemma abox_4:
  assumes "test p"
  shows "|R]p = ((U * p) \<oslash> R) \<inter> 1"
  by (simp add: abox_1 assms top_test_sp_lres_total_expl_3)

lemma abox_ebox:
  assumes "test p"
  shows "|R]p = |ne (R\<down>)]]p"
  by (simp add: abox assms ebox)

lemma abox_edia:
  assumes "test p"
  shows "|R]p = \<wrong> |R\<rangle>\<rangle>(\<wrong> p)"
  by (simp add: abox assms edia)

lemma abox_adia:
  assumes "test p"
  shows "|R]p = \<wrong> |ne (R\<down>)\<rangle>(\<wrong> p)"
  by (simp add: abox adia assms)

lemma edia_adia:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p = |ne (R\<down>)\<rangle>p"
  by (simp add: adia assms edia)

lemma edia_abox:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p = \<wrong> |R](\<wrong> p)"
  by (metis abox_1 assms d_complement_ad edia_1 semilattice_inf_class.inf.cobounded2)

lemma edia_ebox:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p = \<wrong> |ne (R\<down>)]](\<wrong> p)"
  by (simp add: abox assms ebox edia_abox)

lemma abox_ne_down:
  assumes "test p"
  shows "|R]p = |ne (R\<down>)]p"
  by (simp add: abox assms ne_down_idempotent)

lemma edia_ne_down:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p = |ne (R\<down>)\<rangle>\<rangle>p"
  by (simp add: assms edia ne_down_idempotent)

lemma adia_up:
  assumes "test p"
  shows "|R\<rangle>p = |R\<up>\<rangle>p"
proof -
  have "|R\<up>\<rangle>p = Dom (R\<up> \<inter> U * p)"
    by (metis adia assms iu_assoc iu_unit_up up_dist_iu_oi)
  also have "... = Dom (R \<inter> U * p)"
    by (metis assms d_def_expl domain_up_down_conjugate sp_test_dist_oi_right top_sp_test_down_closed)
  also have "... = |R\<rangle>p"
    by (metis adia assms inf.absorb_iff2 inf_commute top_down top_lower_greatest)
  finally show ?thesis
    by simp
qed

lemma ebox_up:
  assumes "test p"
  shows "|R]]p = |R\<up>]]p"
  by (metis Int_commute adia adia_up assms ebox semilattice_inf_class.inf_le1)

lemma adia_ebox:
  assumes "test p"
  shows "|R\<rangle>p = \<wrong> |R]](\<wrong> p)"
  by (metis (no_types, lifting) adia assms d_complement_ad ebox test_double_complement)

lemma ebox_adia:
  assumes "test p"
  shows "|R]]p = \<wrong> |R\<rangle>(\<wrong> p)"
  by (simp add: adia assms ebox)

lemma abox_down:
  assumes "test p"
  shows "|R]p = |R\<down>]p"
  by (simp add: abox assms)

lemma edia_down:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p = |R\<down>\<rangle>\<rangle>p"
  by (simp add: assms edia)

lemma fusion_oi_complement_top_test_up:
  "test p \<Longrightarrow> fus R \<inter> -(U * p) \<subseteq> (R \<inter> -(U * p))\<up>"
  apply (unfold top_test)
  apply (clarsimp simp: mr_simp)
  by blast

lemma adia_left_isotone:
  "test p \<Longrightarrow> R \<subseteq> S \<Longrightarrow> |R\<rangle>p \<subseteq> |S\<rangle>p"
  by (metis adia d_isotone inf.absorb_iff1 sp_test_dist_oi)

lemma adia_right_isotone:
  "test p \<Longrightarrow> test q \<Longrightarrow> p \<subseteq> q \<Longrightarrow> |R\<rangle>p \<subseteq> |R\<rangle>q"
  by (metis (no_types, opaque_lifting) adia d_isotone inf.orderE inf_commute inf_le1 sp_test test_assoc3 test_s_prod_is_meet)

lemma abox_left_antitone:
  "test p \<Longrightarrow> R \<subseteq> S \<Longrightarrow> |S]p \<subseteq> |R]p"
  apply (clarsimp simp: mr_simp) by force

lemma abox_right_isotone:
  "test p \<Longrightarrow> test q \<Longrightarrow> p \<subseteq> q \<Longrightarrow> |R]p \<subseteq> |R]q"
  by (smt (verit, ccfv_threshold) IntE abox_def inf.orderE mem_Collect_eq subsetI)

lemma edia_left_isotone:
  "test p \<Longrightarrow> R \<subseteq> S \<Longrightarrow> |R\<rangle>\<rangle>p \<subseteq> |S\<rangle>\<rangle>p"
  by (metis Int_mono adia_left_isotone down_isotone edia_adia order_refl)

lemma edia_right_isotone:
  "test p \<Longrightarrow> test q \<Longrightarrow> p \<subseteq> q \<Longrightarrow> |R\<rangle>\<rangle>p \<subseteq> |R\<rangle>\<rangle>q"
  by (simp add: adia_right_isotone edia_adia)

lemma ebox_left_antitone:
  "test p \<Longrightarrow> R \<subseteq> S \<Longrightarrow> |S]]p \<subseteq> |R]]p"
  by (metis (no_types, lifting) adia_ebox adia_left_isotone ebox_adia test_complement_antitone test_double_complement)

lemma ebox_right_isotone:
  "test p \<Longrightarrow> test q \<Longrightarrow> p \<subseteq> q \<Longrightarrow> |R]]p \<subseteq> |R]]q"
  by (smt (verit, ccfv_SIG) adia_ebox adia_right_isotone ebox inf_le2 test_complement_antitone test_double_complement)

lemma edia_fusion:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p = |fus R\<rangle>\<rangle>p"
proof
  have "|fus R\<rangle>\<rangle>p = Dom (fus R \<inter> -(U * \<wrong> p))"
    using assms edia_1 by blast
  also have "... \<subseteq> Dom (R \<inter> -(U * \<wrong> p))"
    by (metis fusion_oi_complement_top_test_up d_isotone d_up semilattice_inf_class.inf_le2)
  also have "... = |R\<rangle>\<rangle>p"
    using assms edia_1 by blast
  finally show "|fus R\<rangle>\<rangle>p \<subseteq> |R\<rangle>\<rangle>p"
    .
next
  have "|R\<rangle>\<rangle>p \<subseteq> |(fus R)\<down>\<rangle>\<rangle>p"
    by (simp add: assms edia_left_isotone fusion_lower_increasing)
  thus "|R\<rangle>\<rangle>p \<subseteq> |fus R\<rangle>\<rangle>p"
    using assms edia_down by blast
qed

lemma abox_fusion:
  assumes "test p"
  shows "|R]p = |fus R]p"
  by (metis Int_lower2 abox_edia assms edia_fusion)

lemma abox_fission:
  assumes "test p"
  shows "|R]p = |fis R]p"
  by (metis assms abox_fusion fusion_fission)

lemma edia_fission:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p = |fis R\<rangle>\<rangle>p"
  by (metis assms edia_fusion fusion_fission)

lemma fission_below:
  "fis R \<subseteq> S \<longleftrightarrow> (\<forall>a b B . (a,B) \<in> R \<and> b \<in> B \<longrightarrow> (a,{b}) \<in> S)"
  apply standard
   apply (simp add: basic_trans_rules(31) fission_set)
  apply (clarsimp simp: mr_simp)
  by blast

lemma below_fission_up:
  "S \<subseteq> (fis R)\<up> \<longleftrightarrow> (\<forall>a B . (a,B) \<in> S \<longrightarrow> (\<exists>C . (a,C) \<in> R \<and> C \<inter> B \<noteq> {}))"
proof
  assume "S \<subseteq> (fis R)\<up>"
  thus "\<forall>a B . (a,B) \<in> S \<longrightarrow> (\<exists>C . (a,C) \<in> R \<and> C \<inter> B \<noteq> {})"
    apply (clarsimp simp: mr_simp)
    by fastforce
next
  assume 1: "\<forall>a B . (a,B) \<in> S \<longrightarrow> (\<exists>C . (a,C) \<in> R \<and> C \<inter> B \<noteq> {})"
  show "S \<subseteq> (fis R)\<up>"
  proof
    fix x
    assume "x \<in> S"
    from this obtain a B where 2: "x = (a,B) \<and> (a,B) \<in> S"
      by (metis surj_pair)
    hence "\<exists>C . (a,C) \<in> R \<and> C \<inter> B \<noteq> {}"
      using 1 by simp
    from this obtain C b where 3: "(a,C) \<in> R \<and> b \<in> C \<and> b \<in> B"
      by auto
    hence "(a,{b}) \<in> fis R"
      using fission_set by blast
    thus "x \<in> (fis R)\<up>"
      using 2 3 U_par_st by fastforce
  qed
qed

lemma ebox_below_abox:
  assumes "test p"
    and "fis R \<subseteq> S"
  shows "|S]]p \<subseteq> |R]p"
  by (metis abox_ebox abox_fission assms ebox_left_antitone fission_down_ne_fixpoint)

lemma abox_below_ebox:
  assumes "test p"
    and "S \<subseteq> (fis R)\<up>"
  shows "|R]p \<subseteq> |S]]p"
  by (metis abox_ebox abox_fission assms ebox_left_antitone ebox_up fission_down_ne_fixpoint)

lemma abox_eq_ebox:
  assumes "test p"
    and "fis R \<subseteq> S"
    and "S \<subseteq> (fis R)\<up>"
  shows "|R]p = |S]]p"
  by (simp add: abox_below_ebox assms ebox_below_abox subset_antisym)

lemma abox_eq_ebox_sufficient:
  "S = fis R \<or> S = ne (R\<down>) \<or> S = (ne (R\<down>))\<up> \<longrightarrow> fis R \<subseteq> S \<and> S \<subseteq> (fis R)\<up>"
  apply (unfold imp_disjL)
  apply (intro conjI)
    apply (simp add: convex_reflexive)
   apply (simp add: fission_inner_deterministic fission_up_ne_down_up oi_subset_upper_right_antitone same_fusion_fission_lower)
  by (metis convex_reflexive fission_up_ne_down_up order_refl)

lemma ebox_fission_abox:
  "test p \<Longrightarrow> |R]p = |fis R]]p"
  by (metis abox abox_fission ebox fission_down_ne_fixpoint)

lemma ebox_down_ne_up_abox:
  "test p \<Longrightarrow> |R]p = |(ne (R\<down>))\<up>]]p"
  using abox_ebox ebox_up by blast

lemma same_fusion:
  assumes "fis R \<sqsubseteq>\<down> S"
    and "S \<sqsubseteq>\<down> fus R"
  shows "fis R = fis S"
  by (metis assms fission_down fission_fusion fission_fusion_galois subset_antisym)

lemma same_abox:
  assumes "fis R \<sqsubseteq>\<down> S"
    and "S \<sqsubseteq>\<down> fus R"
    and "test p"
  shows "|R]p = |S]p"
  by (metis assms ebox_fission_abox same_fusion)

lemma abox_ebox_inner_deterministic:
  assumes "test p"
    and "inner_deterministic R"
  shows "|R]p = |R]]p"
  apply (rule abox_eq_ebox)
    apply (simp add: assms(1))
  using assms(2) fission_inner_deterministic_fixpoint apply blast
  by (metis assms(2) convex_reflexive fission_inner_deterministic_fixpoint)

lemma adia_edia_inner_deterministic:
  assumes "test p"
    and "inner_deterministic R"
  shows "|R\<rangle>p = |R\<rangle>\<rangle>p"
  by (metis assms edia_adia fission_down_ne_fixpoint fission_inner_deterministic_fixpoint)

lemma abox_adia_deterministic:
  assumes "test p"
    and "deterministic R"
  shows "|R]p = |R\<rangle>p"
proof
  show "|R]p \<subseteq> |R\<rangle>p"
  proof
    fix x
    assume "x \<in> |R]p"
    from this obtain a where 1: "x = (a,{a}) \<and> (\<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>b\<in>B . (b,{b}) \<in> p))"
      using abox_def by force
    from assms(2) obtain B where "(a,B) \<in> R"
      by (meson deterministic_set)
    thus "x \<in> |R\<rangle>p"
      using 1 adia_def by fastforce
  qed
next
  show "|R\<rangle>p \<subseteq> |R]p"
  proof
    fix x
    assume "x \<in> |R\<rangle>p"
    from this obtain a B where 2: "x = (a,{a}) \<and> (a,B) \<in> R \<and> (\<forall>b\<in>B . (b,{b}) \<in> p)"
      by (smt adia_def mem_Collect_eq)
    have "\<forall>C . (a,C) \<in> R \<longrightarrow> (\<forall>b\<in>C . (b,{b}) \<in> p)"
    proof (rule allI, rule impI)
      fix C
      assume "(a,C) \<in> R"
      hence "B = C"
        using 2 by (metis assms(2) deterministic_set)
      thus "\<forall>b\<in>C . (b,{b}) \<in> p"
        using 2 by simp
    qed
    thus "x \<in> |R]p"
      using 2 abox_def by blast
  qed
qed

lemma ebox_edia_deterministic:
  assumes "test p"
    and "deterministic R"
  shows "|R]]p = |R\<rangle>\<rangle>p"
  by (simp add: assms abox_adia_deterministic ebox_adia edia_abox)

lemma abox_ebox_fusion:
  assumes "test p"
  shows "|fis R]p = |fis R]]p"
  by (metis abox_fission assms ebox_fission_abox)

lemma abox_fission_edia_fusion:
  assumes "test p"
  shows "|fis R]p = |fus R\<rangle>p"
  by (simp add: abox_adia_deterministic abox_fusion assms fusion_deterministic fusion_fission)

lemma abox_adia_fusion:
  assumes "test p"
  shows "|fus R]p = |fus R\<rangle>p"
  by (simp add: abox_adia_deterministic assms fusion_deterministic)

subsection \<open>Goldblatt's axioms without star\<close>

lemma abox_sp_unit:
  "|R]1 = 1"
  apply (clarsimp simp: mr_simp) by force

lemma ou_unit_abox:
  "test p \<Longrightarrow> |{}]p = 1"
  by (metis abox_1 abox_sp_unit disjoint_eq_subset_Compl empty_subsetI inf.absorb_iff2 test_complement_closed)

lemma ou_unit_test_implication:
  "test p \<Longrightarrow> {} \<rightarrow> p = 1"
  by blast

lemma sp_unit_abox:
  "test p \<Longrightarrow> |1]p = p"
  by (smt (verit) Int_left_commute abox_1 c1 cl8_var convex_reflexive d_ne_down_dp_complement_test fission_down_ne_fixpoint fission_inner_deterministic_fixpoint inf.absorb_iff2 inf_commute inner_deterministic_sp_unit s_subid_iff2 test_double_complement test_sp)

lemma sp_unit_test_implication:
  "test p \<Longrightarrow> 1 \<rightarrow> p = p"
  by simp

lemma test_abox_ebox:
  "test p \<Longrightarrow> test q \<Longrightarrow> |q]p = |q]]p"
  apply (rule antisym)
   apply (metis abox_ebox_inner_deterministic dual_order.trans inner_deterministic_sp_unit subset_refl)
  by (metis abox_ebox_inner_deterministic dual_order.eq_iff inner_deterministic_sp_unit inner_univalent_down_closed ne_equality test_ne)

lemma test_abox:
  "test p \<Longrightarrow> test q \<Longrightarrow> |q]p = q \<rightarrow> p"
  by (smt Int_commute Int_lower2 abox cl9_var compl_sup d_complement_ad d_ne_down_dp_complement_test lattice_class.inf_sup_aci(2) sp_unit_abox test_ou_closed)

lemma abox_ou_adia_sp_unit:
  assumes "test p"
  shows "|R]p \<union> |R\<rangle>1 = 1"
  apply (rule antisym)
   apply (simp add: assms abox adia_ebox)
  by (clarsimp simp: mr_simp)

lemma d_test_sp:
  "test p \<Longrightarrow> Dom (p * R) = p * Dom R"
  by (simp add: c4 d_def_expl test_sp_left_dist_iu_1)

lemma ad_test_sp:
  "test p \<Longrightarrow> aDom (p * R) = \<wrong> p \<union> aDom R"
  by (metis (no_types, opaque_lifting) Int_commute boolean_algebra.conj_disj_distrib boolean_algebra.de_Morgan_conj d_s_id_inter d_test_sp s_subid_iff2 test_fix)

lemma adia_test_sp:
  "test p \<Longrightarrow> test q \<Longrightarrow> |p * R\<rangle>q = p * |R\<rangle>q"
  by (metis (no_types, lifting) adia d_test_sp test_assoc3 test_double_complement)

lemma ebox_test_sp:
  "test p \<Longrightarrow> test q \<Longrightarrow> |p * R]]q = \<wrong> p \<union> |R]]q"
  by (simp add: ad_test_sp ebox test_assoc3)

lemma abox_test_sp:
  assumes "test p"
    and "test q"
  shows "|p * R]q = \<wrong> p \<union> |R]q"
proof -
  have "|p * R]q = aDom ((p * R) \<inter> -(U * q))"
    by (simp add: abox_1 assms(2))
  also have "... = aDom (p * (R \<inter> -(U * q)))"
    by (metis Int_assoc assms(1) test_sp)
  also have "... = \<wrong> p \<union> |R]q"
    by (simp add: abox_1 ad_test_sp assms)
  finally show ?thesis
    .
qed

lemma abox_test_sp_2:
  "test p \<Longrightarrow> test q \<Longrightarrow> p \<union> |R]q = |\<wrong> p * R]q"
  by (simp add: abox_test_sp test_double_complement)

lemma abox_test_sp_3:
  "test p \<Longrightarrow> test q \<Longrightarrow> p \<rightarrow> |R]q = |p * R]q"
  by (simp add: abox_test_sp)

lemma fission_sp_dist:
  "fis (R * S) = fis (R * Dom S) * fis S"
proof -
  have "S = Dom S * (S \<union> aDom S * 1\<^sub>\<union>\<^sub>\<union>)"
    by (auto simp: mr_simp)
  hence "fis (R * S) = fis (R * Dom S * (S \<union> aDom S * 1\<^sub>\<union>\<^sub>\<union>))"
    by (metis d_s_id_ax sp_test_sp_oi_right test_sp)
  also have "... = fis (R * Dom S) * fis (S \<union> aDom S * 1\<^sub>\<union>\<^sub>\<union>)"
    apply (rule fission_sp_total_dist)
    by (smt (verit) total_dom Compl_disjoint ad_sp_bot ad_test_sp c6 compl_inf_bot d_complement_ad d_dist_ou inf_le2 iu_unit_down subset_Un_eq sup_ge2 sup_inf_absorb total_lower)
  also have "... = fis (R * Dom S) * (fis S \<union> fis (aDom S * 1\<^sub>\<union>\<^sub>\<union>))"
    by (simp add: fission_dist_ou)
  also have "... = fis (R * Dom S) * fis S"
    by (simp add: fission_sp_iu_unit)
  finally show ?thesis
    .
qed

lemma abox_test:
  "test p \<Longrightarrow> test ( |R]p )"
  by (simp add: abox)

lemma adia_test:
  "test p \<Longrightarrow> test ( |R\<rangle>p )"
  by (simp add: adia d_test)

lemma ebox_test:
  "test p \<Longrightarrow> test ( |R]]p )"
  by (simp add: ebox)

lemma edia_test:
  "test p \<Longrightarrow> test ( |R\<rangle>\<rangle>p )"
  by (simp add: edia d_test)

lemma abox_sp:
  assumes "test p"
    and "test q"
  shows "|R](p * q) = |R]p * |R]q"
proof -
  have "|R](p * q) = aDom (ne (R\<down>) * (\<wrong> p \<union> \<wrong> q))"
    by (metis (no_types, lifting) abox_1 ad_test_sp assms cl9_var d_ne_down_dp_complement_test sp_test test_double_complement test_oi_closed)
  also have "... = aDom (ne (R\<down>) * \<wrong> p) * aDom (ne (R\<down>) * \<wrong> q)"
    by (smt ad_test_sp cl9_var d_complement_ad d_dist_ou d_test_sp semilattice_inf_class.inf_le2 split_sp_test_7)
  also have "... = |R]p * |R]q"
    by (simp add: abox assms)
  finally show ?thesis
    .
qed

lemma adia_ou_below_ne_down:
  assumes "test p"
  shows "|R\<rangle>(p \<union> \<wrong> q) \<subseteq> |R\<rangle>p \<union> |ne (R\<down>)\<rangle>(\<wrong> q)"
  by (metis adia assms d_dist_ou split_sp_test_6 test_complement_closed test_ou_closed)

lemma abox_adia_mp:
  assumes "test p"
    and "test q"
  shows "|R\<rangle>(p \<rightarrow> q) * |R]p \<subseteq> |R\<rangle>q"
  by (smt adia_ou_below_ne_down test_shunting abox adia assms d_complement_ad sup_commute test_complement_closed test_implication_closed)

lemma adia_abox_mp:
  assumes "test p"
    and "test q"
  shows "|R\<rangle>p * |R](p \<rightarrow> q) \<subseteq> |R\<rangle>q"
proof -
  have "p \<subseteq> p \<rightarrow> q \<rightarrow> q"
    using assms(1) by blast
  hence "|R\<rangle>p \<subseteq> |R\<rangle>((p \<rightarrow> q) \<rightarrow> q)"
    by (simp add: adia_right_isotone assms)
  thus ?thesis
    by (smt abox_adia_mp abox_test adia_test assms(2) semilattice_inf_class.inf.orderE semilattice_inf_class.le_infI2 test_implication_closed test_shunting)
qed

lemma abox_implication_adia:
  assumes "test p"
    and "test q"
  shows "|R](p \<rightarrow> q) \<subseteq> |R\<rangle>p \<rightarrow> |R\<rangle>q"
  by (metis adia_abox_mp test_shunting test_sp_commute Int_lower2 Un_commute abox_test adia_test assms test_ou_closed)

lemma abox_adia_implication:
  assumes "test p"
    and "test q"
  shows "|R]p \<subseteq> |R\<rangle>q \<rightarrow> |R\<rangle>(p * q)"
proof -
  have "p \<subseteq> q \<rightarrow> p * q"
    by (metis assms subset_refl test_galois_1 test_sp_commute)
  hence "|R]p \<subseteq> |R](q \<rightarrow> p * q)"
    by (simp add: abox_right_isotone assms test_galois_1)
  thus ?thesis
    by (metis (no_types, lifting) Int_Un_eq(2) abox_implication_adia assms le_sup_iff subset_Un_eq test_galois_1)
qed

lemma abox_mp:
  assumes "test p"
    and "test q"
  shows "|R]p * |R](p \<rightarrow> q) \<subseteq> |R]q"
  by (metis (no_types, lifting) abox_right_isotone abox_sp assms semilattice_inf_class.inf.absorb_iff1 sp_test_dist_oi_left subset_refl sup_commute test_implication_closed test_shunting test_sp_commute)

lemma abox_implication:
  assumes "test p"
    and "test q"
  shows "|R](p \<rightarrow> q) \<subseteq> |R]p \<rightarrow> |R]q"
  by (metis abox_mp test_shunting test_sp_commute abox_test assms sup_commute test_implication_closed)

lemma ebox_left_dist_ou:
  assumes "test p"
  shows "|R \<union> S]]p = |R]]p * |S]]p"
  by (auto simp: mr_simp)

lemma abox_left_dist_ou:
  assumes "test p"
  shows "|R \<union> S]p = |R]p * |S]p"
  by (simp add: abox_ebox assms ebox_left_dist_ou ii_right_dist_ou ne_dist_ou)

lemma adia_left_dist_ou:
  assumes "test p"
  shows "|R \<union> S\<rangle>p = |R\<rangle>p \<union> |S\<rangle>p"
  by (auto simp: mr_simp)

lemma edia_left_dist_ou:
  assumes "test p"
  shows "|R \<union> S\<rangle>\<rangle>p = |R\<rangle>\<rangle>p \<union> |S\<rangle>\<rangle>p"
  by (simp add: assms boolean_algebra.conj_disj_distrib2 d_dist_ou edia_1)

lemma abox_dist_iu_1:
  assumes "test p"
  shows "|R \<union>\<union> S]p = |Dom R * ne (S\<down>)]]p * |Dom S * ne (R\<down>)]]p"
proof
  have 1: "|R \<union>\<union> S]p \<subseteq> |Dom R * ne (S\<down>)]]p"
    by (metis abox_ebox assms d_sp_ne_down_below_ne_iu_down ebox_left_antitone)
  have "|R \<union>\<union> S]p \<subseteq> |Dom S * ne (R\<down>)]]p"
    by (metis abox_ebox assms d_sp_ne_down_below_ne_iu_down ebox_left_antitone iu_commute)
  thus "|R \<union>\<union> S]p \<subseteq> |Dom R * ne (S\<down>)]]p * |Dom S * ne (R\<down>)]]p"
    using 1 by (simp add: assms ebox)
next
  have "|Dom R * ne (S\<down>)]]p * |Dom S * ne (R\<down>)]]p \<subseteq> |Dom R * Dom S * ne (S\<down>)]]p * |Dom S * ne (R\<down>)]]p"
    apply (clarsimp simp: mr_simp)
    by (metis UN_I singletonI)
  also have "... \<subseteq> |Dom R * Dom S * ne (S\<down>)]]p * |Dom R * Dom S * ne (R\<down>)]]p"
    by (simp add: assms d_lb2 ebox_left_antitone s_prod_isol s_prod_isor)
  also have "... = |Dom R * Dom S * ne (S\<down>) \<union> Dom R * Dom S * ne (R\<down>)]]p"
    using assms ebox_left_dist_ou by blast
  also have "... = |ne (Dom R * Dom S * S\<down>) \<union> ne (Dom R * Dom S * R\<down>)]]p"
    by (metis d_dist_ii d_test test_sp_ne)
  also have "... = |ne ((Dom R * Dom S * S)\<down>) \<union> ne ((Dom R * Dom S * R)\<down>)]]p"
    by (simp add: down_dist_sp)
  also have "... = aDom ((ne ((Dom R * Dom S * S)\<down>) \<union> ne ((Dom R * Dom S * R)\<down>)) * \<wrong> p)"
    using assms ebox by blast
  also have "... \<subseteq> aDom ((ne ((Dom R * Dom S * S \<union>\<union> Dom R * Dom S * R)\<down>)) * \<wrong> p)"
    using d_ne_iu_down_sp_test_ou by blast
  also have "... = |Dom R * Dom S * S \<union>\<union> Dom R * Dom S * R]p"
    using abox assms by blast
  also have "... = |Dom R * Dom S * (R \<union>\<union> S)]p"
    by (metis d_assoc1 d_inter_r p_prod_comm)
  also have "... = |R \<union>\<union> S]p"
    by (metis c1 cl8_var d_dist_iu)
  finally show "|Dom R * ne (S\<down>)]]p * |Dom S * ne (R\<down>)]]p \<subseteq> |R \<union>\<union> S]p"
    .
qed

lemma abox_dist_iu_2:
  assumes "test p"
  shows "|R \<union>\<union> S]p = |Dom R * S]p * |Dom S * R]p"
proof -
  have "|Dom R * ne (S\<down>)]]p * |Dom S * ne (R\<down>)]]p = |ne ((Dom R * S)\<down>)]]p * |ne ((Dom S * R)\<down>)]]p"
    by (simp add: d_test down_dist_sp test_sp_ne)
  also have "... = |Dom R * S]p * |Dom S * R]p"
    by (simp add: abox_ebox assms)
  finally show ?thesis
    using assms abox_dist_iu_1 by blast
qed

lemma abox_dist_iu_3:
  assumes "test p"
  shows "|R \<union>\<union> S]p = ( |R\<rangle>1 \<rightarrow> |S]p ) * ( |S\<rangle>1 \<rightarrow> |R]p )"
  by (metis abox_dist_iu_2 adia assms abox_test_sp d_test s_prod_idr subset_refl)

lemma abox_adia_sp_one_set:
  "|R]|S\<rangle>1 = { (a,{a}) | a . \<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>b\<in>B . \<exists>D . (b,D) \<in> S) }"
  by (auto simp: abox_def Dom_def adia)

lemma abox_abox_set:
  "|R]|S]p = { (a,{a}) | a . \<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>C . (\<exists>b\<in>B . (b,C) \<in> S) \<longrightarrow> (\<forall>c\<in>C . (c,{c}) \<in> p)) }"
  by (auto simp: abox_def)

lemma sp_abox_set:
  "|R * S]p = { (a,{a}) | a . \<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>C . (\<exists>f . (\<forall>b\<in>B . (b,f b) \<in> S) \<and> C = \<Union>{ f b | b . b \<in> B }) \<longrightarrow> (\<forall>c\<in>C . (c,{c}) \<in> p)) }"
  apply (unfold abox_def s_prod_def)
  by blast

lemma abox_sp_1:
  assumes "test p"
  shows "|R]|S\<rangle>1 * |R * S]p \<subseteq> |R]|S]p"
proof -
  have "|R]|S\<rangle>1 * |R * S]p = |R]|S\<rangle>1 \<inter> |R * S]p"
    by (smt (verit, ccfv_SIG) abox_test adia_test assms convex_increasing inf.orderE inf_assoc sp_unit_convex test_s_prod_is_meet)
  also have "... \<subseteq> |R]|S]p"
  proof
    fix x
    assume "x \<in> |R]|S\<rangle>1 \<inter> |R * S]p"
    from this obtain a where 1: "x = (a,{a}) \<and> x \<in> |R]|S\<rangle>1 \<and> x \<in> |R * S]p"
      by (metis Int_iff abox_test adia_test order_refl subid_aux2 subsetD surj_pair)
    hence 2: "\<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>b\<in>B . \<exists>D . (b,D) \<in> S)"
      by (smt abox_adia_sp_one_set mem_Collect_eq old.prod.inject)
    have 3: "\<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>C . (\<exists>f . (\<forall>b\<in>B . (b,f b) \<in> S) \<and> C = \<Union>{ f b | b . b \<in> B }) \<longrightarrow> (\<forall>c\<in>C . (c,{c}) \<in> p))"
      using 1 by (smt sp_abox_set mem_Collect_eq old.prod.inject)
    have "\<forall>B . (a,B) \<in> R \<longrightarrow> (\<forall>C . (\<exists>b\<in>B . (b,C) \<in> S) \<longrightarrow> (\<forall>c\<in>C . (c,{c}) \<in> p))"
    proof (rule allI, rule impI)
      fix B
      assume 4: "(a,B) \<in> R"
      hence "\<exists>DD . \<forall>b\<in>B . (b,DD b) \<in> S"
        using 2 by (auto intro: bchoice)
      from this obtain DD where 5: "\<forall>b\<in>B . (b,DD b) \<in> S"
        by auto
      show "\<forall>C . (\<exists>b\<in>B . (b,C) \<in> S) \<longrightarrow> (\<forall>c\<in>C . (c,{c}) \<in> p)"
      proof (rule allI, rule impI)
        fix C
        assume "\<exists>b\<in>B . (b,C) \<in> S"
        from this obtain b where 6: "b \<in> B \<and> (b,C) \<in> S"
          by auto
        let ?f = "\<lambda>x . if x = b then C else DD x"
        let ?C = "C \<union> \<Union>{ ?f x | x . x \<in> B \<and> x \<noteq> b }"
        have "\<exists>f . (\<forall>b\<in>B . (b,f b) \<in> S) \<and> ?C = \<Union>{ f b | b . b \<in> B }"
          apply (rule exI[where ?x="?f"])
          using 5 6 by auto
        hence "\<forall>c\<in>?C . (c,{c}) \<in> p"
          using 3 4 by auto
        thus "\<forall>c\<in>C . (c,{c}) \<in> p"
          by blast
      qed
    qed
    thus "x \<in> |R]|S]p"
      using 1 abox_abox_set by blast
  qed
  finally show ?thesis
    .
qed

lemma abox_sp_2:
  assumes "test p"
  shows "|R]|S]p = |R\<down> * S]p"
proof -
  have "|R]|S]p = aDom (ne (R\<down>) * Dom (ne (S\<down>) * \<wrong> p))"
    by (metis abox abox_test assms d_complement_ad)
  also have "... = aDom (ne (R\<down>) * ne (S\<down>) * \<wrong> p)"
    by (simp add: test_assoc3)
  also have "... = aDom (ne ((R\<down> * S)\<down>) * \<wrong> p)"
    by (simp add: down_dist_sp ne_dist_down_sp)
  also have "... = |R\<down> * S]p"
    by (simp add: abox assms)
  finally show ?thesis
    .
qed

lemma abox_sp_3:
  assumes "test p"
  shows "|R]|S]p \<subseteq> |R * S]p"
  by (clarsimp simp: mr_simp) auto

lemma abox_sp_4:
  assumes "test p"
  shows "|R * S]p \<subseteq> |R]|S\<rangle>1 \<rightarrow> |R]|S]p"
proof -
  have "|R]|S\<rangle>1 * |R * S]p \<subseteq> |R]|S]p"
    by (auto simp: assms abox_sp_1)
  hence "|R]|S\<rangle>1 \<inter> |R * S]p \<subseteq> |R]|S]p"
    by (smt (verit) abox_test adia_test assms convex_increasing inf.orderE sp_unit_convex test_oi_closed test_s_prod_is_meet)
  thus ?thesis
    using abox_test assms by blast
qed

lemma abox_sp_5:
  assumes "test p"
  shows "|R]|S\<rangle>1 * |R * S]p = |R]|S\<rangle>1 * |R]|S]p"
proof (rule antisym)
  have "|R * S]p \<subseteq> |R]|S\<rangle>1 \<rightarrow> |R]|S]p"
    by (simp add: abox_sp_4 assms)
  hence "|R]|S\<rangle>1 \<inter> |R * S]p \<subseteq> |R]|S]p"
    by blast
  hence "|R]|S\<rangle>1 \<inter> |R * S]p \<subseteq> |R]|S\<rangle>1 \<inter> |R]|S]p"
    by blast
  thus "|R]|S\<rangle>1 * |R * S]p \<subseteq> |R]|S\<rangle>1 * |R]|S]p"
    by (smt (verit, del_insts) abox_test adia_test assms convex_increasing inf.orderE sp_unit_convex test_oi_closed test_s_prod_is_meet)
  show "|R]|S\<rangle>1 * |R]|S]p \<subseteq> |R]|S\<rangle>1 * |R * S]p"
    by (simp add: abox_sp_3 assms s_prod_isor)
qed

lemma abox_sp_6:
  assumes "test p"
  shows "|R]|S\<rangle>1 \<rightarrow> |R * S]p = |R]|S\<rangle>1 \<rightarrow> |R]|S]p"
  by (smt Int_commute abox_sp_3 abox_sp_4 assms inf_sup_distrib2 lattice_class.inf_sup_absorb semilattice_inf_class.inf.absorb_iff2 sup_commute)

lemma abox_sp_7:
  assumes "test p"
    and "total S"
  shows "|R * S]p = |R]|S]p"
  by (metis (no_types, lifting) abox_ebox abox_sp_2 assms down_dist_sp total_down_dist_sp)

lemma adia_sp_associative:
  assumes "test p"
  shows "|Q * (R * S)\<rangle>p = |(Q * R) * S\<rangle>p"
proof -
  have "|Q * (R * S)\<rangle>p = |Q\<rangle>( |R\<rangle>( |S\<rangle>p))"
    by (metis (no_types, lifting) adia adia_test assms d_loc_ax inf.orderE test_assoc3)
  also have "\<dots> = |(Q * R) * S\<rangle>p"
    by (smt (verit, best) adia adia_test assms d_loc test_assoc3 test_double_complement)
  finally show "|Q * (R * S)\<rangle>p = |(Q * R) * S\<rangle>p"
    .
qed

lemma ebox_sp_associative:
  assumes "test p"
  shows "|Q * (R * S)]]p = |(Q * R) * S]]p"
  by (simp add: adia_sp_associative assms ebox_adia)

lemma edia_sp_associative:
  assumes "test p"
  shows "|Q * (R * S)\<rangle>\<rangle>p = |(Q * R) * S\<rangle>\<rangle>p"
proof -
  have "|fis (Q * (R * S))\<rangle>\<rangle>p = |fis (Q * Dom (R * S)) * (fis (R * Dom S) * fis S)\<rangle>\<rangle>p"
    by (metis fission_sp_dist)
  also have "... = |(fis (Q * Dom (R * S)) * fis (R * Dom S)) * fis S\<rangle>\<rangle>p"
    by (simp add: inner_deterministic_sp_assoc semilattice_inf_class.inf_commute semilattice_inf_class.le_infI1 fission_var)
  also have "... = |fis (Q * Dom (R * Dom S)) * fis (R * Dom S) * fis S\<rangle>\<rangle>p"
    by simp
  also have "... = |fis (Q * (R * Dom S)) * fis S\<rangle>\<rangle>p"
    by (metis fission_sp_dist)
  also have "... = |fis ((Q * R) * Dom S) * fis S\<rangle>\<rangle>p"
    by (metis d_complement_ad test_assoc3)
  also have "... = |fis ((Q * R) * S)\<rangle>\<rangle>p"
    by (metis fission_sp_dist)
  finally show ?thesis
    using assms edia_fission by blast
qed

lemma abox_sp_associative:
  assumes "test p"
  shows "|Q * (R * S)]p = |(Q * R) * S]p"
  by (simp add: edia_sp_associative assms abox_edia)

lemma abox_oI:
  assumes "X \<noteq> {}"
  shows "|R]\<Inter>X = (\<Inter>p\<in>X . |R]p)"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
  apply (clarsimp simp: mr_simp)
  using assms by blast

lemma ebox_left_dist_oU:
  assumes "X \<noteq> {}"
  shows "|\<Union>X]]p = (\<Inter>R\<in>X . |R]]p)"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply blast
  apply (clarsimp simp: mr_simp)
  using assms by blast

lemma abox_left_dist_oU:
  assumes "X \<noteq> {}"
  shows "|\<Union>X]p = (\<Inter>R\<in>X . |R]p)"
  apply (rule antisym)
   apply (clarsimp simp: mr_simp)
   apply blast
  apply (clarsimp simp: mr_simp)
  using assms by blast

lemma adia_left_dist_oU:
  "|\<Union>X\<rangle>p = (\<Union>R\<in>X . |R\<rangle>p)"
  apply (clarsimp simp: mr_simp)
  by blast

lemma edia_left_dist_oU:
  "|\<Union>X\<rangle>\<rangle>p = (\<Union>R\<in>X . |R\<rangle>\<rangle>p)"
  apply (clarsimp simp: mr_simp)
  by blast

subsection \<open>Goldblatt's axioms with star\<close>

no_notation rtrancl ("(_\<^sup>*)" [1000] 999)
notation star ("_\<^sup>*" [1000] 999)

lemma star_induct_1:
  assumes "1 \<subseteq> X"
    and "R * X \<subseteq> X"
  shows "R\<^sup>* \<subseteq> X"
  apply (unfold star_def)
  apply (rule lfp_lowerbound)
  by (simp add: assms)

lemma star_induct:
  assumes "S \<subseteq> 1 \<union> 1\<^sub>\<union>\<^sub>\<union>"
    and "S \<subseteq> X"
    and "R * X \<subseteq> X"
  shows "R\<^sup>* * S \<subseteq> X"
proof -
  have "R\<^sup>* \<subseteq> X \<oslash> S"
  proof (rule star_induct_1)
    show "1 \<subseteq> X \<oslash> S"
      by (metis (no_types, opaque_lifting) Int_subset_iff assms(2) dual_order.eq_iff sp_lres_galois test_sp)
  next
    have "(X \<oslash> S) * S \<subseteq> X"
      by (simp add: sp_lres_sp_below)
    hence "R * (X \<oslash> S) * S \<subseteq> R * X"
      by (metis assms(1) s_prod_isor test_iu_test_sp_assoc_5)
    also have "... \<subseteq> X"
      by (simp add: assms(3))
    finally show "R * (X \<oslash> S) \<subseteq> X \<oslash> S"
      by (simp add: sp_lres_galois)
  qed
  thus ?thesis
    by (simp add: sp_lres_galois)
qed

lemma star_total:
  "total (R\<^sup>*)"
  by (metis s_prod_idl s_prod_isol star_refl total_4)

lemma star_down:
  "R\<^sup>*\<down> = (R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>"
proof
  have "R\<^sup>* * (1 \<union> 1\<^sub>\<union>\<^sub>\<union>) \<subseteq> (R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>"
  proof (rule star_induct)
    show "1 \<union> 1\<^sub>\<union>\<^sub>\<union> \<subseteq> 1 \<union> 1\<^sub>\<union>\<^sub>\<union>"
      by simp
  next
    show "1 \<union> 1\<^sub>\<union>\<^sub>\<union> \<subseteq> (R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>"
      using star_refl by auto
  next
    have "ne (R * ((R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>)) \<subseteq> ne (R\<down> * ((R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>))"
      by (simp add: down_sp_sp sup_commute)
    also have "... = ne (R\<down>) * ne ((R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>)"
      by (simp add: ne_dist_down_sp)
    also have "... = ne (R\<down>) * ne ((R\<down>)\<^sup>*)"
      by (metis down_idempotent down_sp_sp ne_dist_down_sp sup_commute)
    also have "... \<subseteq> R\<down> * (R\<down>)\<^sup>*"
      using sp_oi_subdist by blast
    also have "... \<subseteq> (R\<down>)\<^sup>*"
      using star_unfold_eq by blast
    finally show "R * ((R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>) \<subseteq> (R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>"
      by blast
  qed
  thus "R\<^sup>*\<down> \<subseteq> (R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>"
    by (simp add: down_sp sup_commute)
next
  have "(R\<down>)\<^sup>* \<subseteq> R\<^sup>*\<down>"
  proof (rule star_induct_1)
    show "1 \<subseteq> R\<^sup>*\<down>"
      by (simp add: star_refl subset_lower)
  next
    show "R\<down> * R\<^sup>*\<down> \<subseteq> R\<^sup>*\<down>"
      by (metis total_dom Un_Int_eq(1) d_isotone d_test ii_right_dist_ou inf_le2 le_sup_iff s_subid_iff2 star_unfold_eq subset_antisym total_down_dist_sp)
  qed
  thus "(R\<down>)\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union> \<subseteq> R\<^sup>*\<down>"
    using star_total total_lower by blast
qed

lemma ne_star_down:
  "ne (R\<^sup>*\<down>) = ne ((R\<down>)\<^sup>*)"
  by (simp add: ne_dist_ou star_down)

lemma ne_down_star:
  "ne ((R\<down>)\<^sup>*) = (ne (R\<down>))\<^sup>*"
proof
  have "(R\<down>)\<^sup>* \<subseteq> (ne (R\<down>))\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>"
  proof (rule star_induct_1)
    show "1 \<subseteq> (ne (R\<down>))\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>"
      by (simp add: le_supI1 star_refl)
  next
    have "ne (R\<down> * ((ne (R\<down>))\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>)) = ne (R\<down>) * ne ((ne (R\<down>))\<^sup>*)"
      by (metis down_idempotent down_sp_sp ne_dist_down_sp sup_commute)
    also have "... \<subseteq> (ne (R\<down>))\<^sup>*"
      by (metis (no_types, lifting) IntE UnCI inf.absorb_iff2 sp_oi_subdist star_unfold_eq subsetI)
    finally show "R\<down> * ((ne (R\<down>))\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>) \<subseteq> ((ne (R\<down>))\<^sup>* \<union> 1\<^sub>\<union>\<^sub>\<union>)"
      by blast
  qed
  thus "ne ((R\<down>)\<^sup>*) \<subseteq> (ne (R\<down>))\<^sup>*"
    by (smt Compl_disjoint2 Int_commute Int_left_commute ne_dist_ou semilattice_inf_class.le_iff_inf sup_bot.right_neutral)
next
  show "(ne (R\<down>))\<^sup>* \<subseteq> ne ((R\<down>)\<^sup>*)"
  proof (rule star_induct_1)
    show "1 \<subseteq> ne ((R\<down>)\<^sup>*)"
      using star_refl test_ne by auto
  next
    show "ne (R\<down>) * ne ((R\<down>)\<^sup>*) \<subseteq> ne ((R\<down>)\<^sup>*)"
      by (metis IntE IntI UnCI ne_dist_down_sp star_unfold_eq subsetI)
  qed
qed

lemma abox_star_unfold:
  "test p \<Longrightarrow> |R\<^sup>*]p = p * |R]|R\<^sup>*]p"
  by (metis abox_left_dist_ou abox_sp_7 sp_unit_abox star_total star_unfold_eq)

lemma star_sp_test_commute:
  assumes "S \<subseteq> 1 \<union> 1\<^sub>\<union>\<^sub>\<union>"
    and "Q * S \<subseteq> S * R"
  shows "Q\<^sup>* * S \<subseteq> S * R\<^sup>*"
proof (rule star_induct)
  show "S \<subseteq> 1 \<union> 1\<^sub>\<union>\<^sub>\<union>"
    by (simp add: assms(1))
next
  show "S \<subseteq> S * R\<^sup>*"
    by (metis s_prod_idr s_prod_isor star_refl)
next
  have "Q * (S * R\<^sup>*) \<subseteq> S * R * R\<^sup>*"
    by (metis (no_types, lifting) assms s_prod_distr subset_Un_eq test_iu_test_sp_assoc_3)
  thus "Q * (S * R\<^sup>*) \<subseteq> S * R\<^sup>*"
    by (metis (no_types, lifting) UnCI dual_order.trans s_prod_assoc1 s_prod_isor star_unfold subset_eq)
qed

lemma adia_star_induct:
  assumes "test p"
  shows "|R\<rangle>p \<subseteq> p \<longleftrightarrow> |R\<^sup>*\<rangle>p \<subseteq> p"
proof
  assume "|R\<rangle>p \<subseteq> p"
  hence "\<wrong> p * Dom (R * p) = {}"
    by (metis adia assms d_idem2 s_prod_isol subset_empty test_sp_shunting)
  hence "R * p \<subseteq> p * (R * p)"
    by (metis assms d_sp_strict subset_refl test_sp_shunting)
  hence "R * p \<subseteq> p * R"
    by (metis assms inf.absorb_iff2 inf_commute sp_test_dist_oi_right test_assoc3 test_sp_idempotent)
  hence "R\<^sup>* * p \<subseteq> p * R\<^sup>*"
    by (simp add: assms le_supI1 star_sp_test_commute)
  hence "R\<^sup>* * p \<subseteq> p * (R\<^sup>* * p)"
    by (metis assms inf.absorb_iff2 inf.orderE sp_oi_subdist test_assoc3 test_sp_idempotent)
  hence "\<wrong> p * (R\<^sup>* * p) = {}"
    by (meson assms subset_empty test_sp_shunting)
  hence "\<wrong> p * Dom (R\<^sup>* * p) = {}"
    using d_sp_strict by blast
  thus "|R\<^sup>*\<rangle>p \<subseteq> p"
    by (metis adia assms d_test empty_subsetI semilattice_inf_class.le_inf_iff sp_test test_sp_shunting)
next
  assume "|R\<^sup>*\<rangle>p \<subseteq> p"
  thus "|R\<rangle>p \<subseteq> p"
    by (metis adia_left_isotone assms dual_order.trans s_prod_idr s_prod_isor star_refl star_unfold sup.coboundedI2)
qed

lemma ebox_star_induct:
  assumes "test p"
  shows "p \<subseteq> |R]]p \<longleftrightarrow> p \<subseteq> |R\<^sup>*]]p"
  by (smt (verit, best) adia adia_star_induct assms d_complement_ad ebox_adia test_complement_antitone test_double_complement)

lemma abox_star_induct:
  assumes "test p"
  shows "p \<subseteq> |R]p \<longleftrightarrow> p \<subseteq> |R\<^sup>*]p"
proof -
  have "p \<subseteq> |ne (R\<down>)]]p \<longleftrightarrow> p \<subseteq> |ne (R\<^sup>*\<down>)]]p"
    by (metis assms ebox_star_induct ne_down_star ne_star_down)
  thus ?thesis
    by (metis abox_ebox assms)
qed

lemma edia_star_induct:
  assumes "test p"
  shows "|R\<rangle>\<rangle>p \<subseteq> p \<longleftrightarrow> |R\<^sup>*\<rangle>\<rangle>p \<subseteq> p"
  by (metis adia_star_induct assms edia_adia ne_down_star ne_star_down)

lemma abox_star_induct_1:
  assumes "test p"
    and "test q"
    and "q \<subseteq> p * |R]q"
  shows "q \<subseteq> |R\<^sup>*]p"
proof -
  have "q \<subseteq> p \<and> q \<subseteq> |R\<^sup>*]q"
    by (metis Int_subset_iff abox_star_induct abox_test assms test_sp test_sp_commute)
  thus ?thesis
    using abox_right_isotone assms(1,2) by blast
qed

lemma adia_star_induct_1:
  assumes "test p"
    and "test q"
    and "p \<union> |R\<rangle>q \<subseteq> q"
  shows "|R\<^sup>*\<rangle>p \<subseteq> q"
  by (meson adia_right_isotone adia_star_induct assms order.trans sup.bounded_iff)

lemma abox_segerberg:
  assumes "test p"
  shows "|R\<^sup>*](p \<rightarrow> |R]p) \<subseteq> p \<rightarrow> |R\<^sup>*]p"
proof -
  have "p * |R\<^sup>*](p \<rightarrow> |R]p) \<subseteq> |R\<^sup>*]p"
  proof (rule abox_star_induct_1)
    show "test p"
      by (simp add: assms)
  next
    show "test (p * |R\<^sup>*](p \<rightarrow> |R]p))"
      by (simp add: abox_test assms test_galois_1)
  next
    have "p * |R\<^sup>*](p \<rightarrow> |R]p) = p * (p \<rightarrow> |R]p) * |R]|R\<^sup>*](p \<rightarrow> |R]p)"
      by (metis abox_star_unfold abox_test assms inf_le2 le_infE sp_unit_convex sp_unit_down test_iu_test_sp_assoc_1 test_ou_closed)
    also have "... = p * |R]p * |R]|R\<^sup>*](p \<rightarrow> |R]p)"
      by (smt (verit, best) Un_Int_eq(4) abox_left_dist_ou abox_test assms equalityD1 le_infE s_prod_isol sp_unit_abox sp_unit_convex sp_unit_down subset_Un_eq subset_antisym test_galois_1 test_iu_test_sp_assoc_1 test_ou_closed test_sp_commute)
    also have "... = p * |R](p * |R\<^sup>*](p \<rightarrow> |R]p))"
      by (metis (no_types, lifting) abox_sp abox_test abox_test_sp_3 assms test_assoc2 test_double_complement)
    finally show "p * |R\<^sup>*](p \<rightarrow> |R]p) \<subseteq> p * |R](p * |R\<^sup>*](p \<rightarrow> |R]p))"
      by simp
  qed
  thus ?thesis
    by (meson abox_test assms test_galois_1 test_implication_closed)
qed

lemma abox_segerberg_adia:
  assumes "test p"
  shows "|R\<^sup>*]( |R\<rangle>p \<rightarrow> p ) \<subseteq> |R\<^sup>*\<rangle>p \<rightarrow> p"
proof -
  let ?q = "|R\<^sup>*]( |R\<rangle>p \<rightarrow> p )"
  have "|R\<^sup>*\<rangle>p \<subseteq> ?q \<rightarrow> p"
  proof (rule adia_star_induct_1)
    show "test p"
      by (simp add: assms)
  next
    show "test ( ?q \<rightarrow> p )"
      by (simp add: assms)
  next
    have "|R\<rangle>(?q \<rightarrow> p) * |R]?q * ( |R\<rangle>p \<rightarrow> p ) \<subseteq> |R\<rangle>p * ( |R\<rangle>p \<rightarrow> p )"
      by (metis (no_types, lifting) abox_adia_mp abox_test assms inf.absorb_iff2 sp_test_dist_oi test_implication_closed)
    also have "... \<subseteq> p"
      by (meson adia_test assms equalityD2 test_galois_1 test_implication_closed)
    finally have "|R\<rangle>(?q \<rightarrow> p) \<subseteq> ( |R\<rangle>p \<rightarrow> p ) * |R]?q \<rightarrow> p"
      by (smt (verit) abox_star_unfold abox_test adia assms d_complement_ad test_assoc3 test_double_complement test_galois_1 test_implication_closed test_sp_commute)
    also have "... = ?q \<rightarrow> p"
      by (metis abox_star_unfold assms test_implication_closed)
    finally show "p \<union> |R\<rangle>( ?q \<rightarrow> p ) \<subseteq> ?q \<rightarrow> p"
      by (metis le_sup_iff order_refl)
  qed
  thus ?thesis
    by (smt abox_test adia_test assms sup_commute test_galois_1 test_implication_closed test_shunting)
qed

lemma "(s_id \<union> p_id) * R = R \<union> p_id"
  by (simp add: s_prod_distr)

section \<open>Counterexamples\<close>

locale counterexamples 
begin

lemma counter_01:
  "\<not> ((U::('a,'b) mrel) * -((U::('b,'c) mrel) * (R::('c,'d) mrel)) \<subseteq> -(U * R))"
  by (metis UNIV_I U_par_zero disjoint_eq_subset_Compl emptyE iu_unit_below_top_sp_test iu_unit_up le_inf_iff s_prod_zerol subset_empty top_upper_least)

abbreviation "a_1 \<equiv> finite_1.a\<^sub>1"

lemma counter_02:
  "\<exists>R::(Enum.finite_1,Enum.finite_1) mrel . \<exists>p . \<not> (test p \<longrightarrow> (R \<inter> -(U * p)) * U = R * -(p * U))"
  apply (rule exI[where ?x="{(a_1,{})}"])
  apply (rule exI[where ?x="{}"])
  apply (clarsimp simp: s_id_def)
  by (smt (verit, ccfv_SIG) Compl_empty_eq Diff_eq Int_insert_left_if0 U_par_p_id cl8_var complement_test_sp_top d_U d_sp_strict dc empty_subsetI inf_le2 inf_top_left inner_total_2 insert_not_empty s_prod_zerol x_split_var x_y_split zero_nc)

lemma counter_03:
  "\<exists>R::(Enum.finite_1,Enum.finite_1) mrel . \<exists>p . \<not> (test p \<longrightarrow> (R \<inter> -(U * p)) * 1\<^sub>\<union>\<^sub>\<union> = R * (-(p * U) \<inter> 1\<^sub>\<union>\<^sub>\<union>))"
  apply (rule exI[where ?x="{(a_1,{})}"])
  apply (rule exI[where ?x="{}"])
  apply (clarsimp simp: s_id_def)
  by (smt (z3) Int_Un_eq(3) Int_absorb2 U_c ad_sp_bot cd_iso dc_prop1 disjoint_eq_subset_Compl inf_compl_bot_right inner_total_2 insertI1 p_id_zero singleton_Un_iff sp_oi_subdist)

abbreviation "b_1 \<equiv> finite_2.a\<^sub>1"
abbreviation "b_2 \<equiv> finite_2.a\<^sub>2"
abbreviation "b_1_0 \<equiv> (b_1,{})"
abbreviation "b_1_1 \<equiv> (b_1,{b_1})"
abbreviation "b_1_2 \<equiv> (b_1,{b_2})"
abbreviation "b_1_3 \<equiv> (b_1,{b_1,b_2})"
abbreviation "b_2_0 \<equiv> (b_2,{})"
abbreviation "b_2_1 \<equiv> (b_2,{b_1})"
abbreviation "b_2_2 \<equiv> (b_2,{b_2})"
abbreviation "b_2_3 \<equiv> (b_2,{b_1,b_2})"

lemma counter_04:
  "\<exists>R::(Enum.finite_2,Enum.finite_2) mrel . \<exists>p q . \<not> (test p \<longrightarrow> test q \<longrightarrow> |R * p]q = |R]|p]q)"
  apply (rule exI[where ?x="{b_1_3}"])
  apply (rule exI[where ?x="{b_1_1}"])
  apply (rule exI[where ?x="{}"])
  apply (subst sp_test)
   apply (clarsimp simp: s_id_def)
  apply (subst top_test)
   apply (clarsimp simp: s_id_def)
  apply (unfold abox_def)
  apply (clarsimp simp: s_id_def)
  by blast

lemma counter_05:
  "\<not> (\<exists>f . \<forall>R p . test p \<longrightarrow> |R\<rangle>p = |f R]p)"
  by (smt (verit, ccfv_threshold) Int_lower1 Int_lower2 abox_sp_unit adia_test_sp counter_01 iu_test_sp_left_zero s_prod_idl subset_refl)

lemma counter_06:
  "\<not> (\<exists>f . \<forall>R p . test p \<longrightarrow> |R]]p = |f R]p)"
  by (metis abox_adia_fusion abox_fusion abox_sp_unit adia counter_05 d_complement_ad disjoint_eq_subset_Compl ebox_adia empty_subsetI s_prod_idr order_refl)

lemma counter_07:
  "\<not> (\<exists>f . mono f \<and> (\<forall>R . fus R = lfp (\<lambda>X . f R X)))"
proof
  assume "\<exists>f::('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> ('a,'b) mrel . mono f \<and> (\<forall>R . fus R = lfp (\<lambda>X . f R X))"
  from this obtain f :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> ('a,'b) mrel" where "mono f \<and> (\<forall>R . fus R = lfp (\<lambda>X . f R X))"
    by auto
  hence "fus {} \<subseteq> fus (U::('a,'b) mrel)"
    by (simp add: le_fun_def mono_def lfp_mono)
  thus False
    by (auto simp: mr_simp)
qed

abbreviation "c_1 \<equiv> finite_3.a\<^sub>1"
abbreviation "c_2 \<equiv> finite_3.a\<^sub>2"
abbreviation "c_3 \<equiv> finite_3.a\<^sub>3"

lemma counter_08:
  "\<not> (\<sim>(1::(Enum.finite_3,Enum.finite_3) mrel) * \<sim>1 \<in> {1, \<sim>1})"
proof -
  let ?c = "(c_1,{c_1,c_2,c_3})"
  have 1: "?c \<in> \<sim>1 * \<sim>1"
    apply (clarsimp simp: mr_simp)
    apply (rule exI[where ?x="{c_2,c_3}"])
    using UNIV_finite_3 by auto
  have "?c \<notin> 1 \<and> ?c \<notin> \<sim>1"
    by (auto simp: mr_simp)
  thus ?thesis
    using 1 by auto
qed

lemma counter_09:
  "\<not> (\<sim>(1::(Enum.finite_3,Enum.finite_3) mrel) \<odot> 1 \<in> {1, \<sim>1})"
  by (metis counter_08 co_prod empty_iff ic_involutive insert_iff)

lemma ex_2_cases:
  "\<exists>b. b = b_1 \<or> b = b_2"
  by auto

lemma all_2_cases:
  "(\<forall>b. b = b_2 \<and> b = b_1) = False"
  by auto

lemma impl_2_cases:
  "\<Union>{ X . \<exists>b. (b = b_1 \<longrightarrow> X = Y) \<and> (b = b_2 \<longrightarrow> X = Z)} = Y \<union> Z"
  by auto

lemma ex_2_set_cases:
  "(\<exists>B::Enum.finite_2 set . P B) \<longleftrightarrow> P {} \<or> P {b_1} \<or> P {b_2} \<or> P {b_1,b_2}"
proof -
  let ?U = "UNIV::Enum.finite_2 set set"
  have "?U \<subseteq> {{},{b_1},{b_2},{b_1,b_2}}"
  proof
    fix x
    have "x \<subseteq> {b_1,b_2}"
      by auto
    thus "x \<in> {{},{b_1},{b_2},{b_1,b_2}}"
      by auto
  qed
  hence "?U = {{},{b_1},{b_2},{b_1,b_2}}"
    by auto
  thus ?thesis
    by (metis UNIV_I empty_iff insertE)
qed

abbreviation "B_0 \<equiv> {}::Enum.finite_2 set"
abbreviation "B_1 \<equiv> {b_1}"
abbreviation "B_2 \<equiv> {b_2}"
abbreviation "B_3 \<equiv> {b_1,b_2}"
abbreviation "mkf x y \<equiv> \<lambda>z . if z = b_1 then x else y"

lemma mkf:
  "f = mkf (f b_1) (f b_2)"
  by auto

lemma mkf2:
  "f b_1 = X \<and> f b_2 = Y \<Longrightarrow> f = mkf X Y"
  by auto

lemma ex_2_mrel_cases:
  "(\<exists>f::Enum.finite_2 \<Rightarrow> Enum.finite_2 set . P f) \<longleftrightarrow>
    P (mkf B_0 B_0) \<or> P (mkf B_0 B_1) \<or> P (mkf B_0 B_2) \<or> P (mkf B_0 B_3) \<or>
    P (mkf B_1 B_0) \<or> P (mkf B_1 B_1) \<or> P (mkf B_1 B_2) \<or> P (mkf B_1 B_3) \<or>
    P (mkf B_2 B_0) \<or> P (mkf B_2 B_1) \<or> P (mkf B_2 B_2) \<or> P (mkf B_2 B_3) \<or>
    P (mkf B_3 B_0) \<or> P (mkf B_3 B_1) \<or> P (mkf B_3 B_2) \<or> P (mkf B_3 B_3)"
proof
  assume "\<exists>f::Enum.finite_2 \<Rightarrow> Enum.finite_2 set . P f"
  from this obtain f where 1: "P f"
    by auto
  have "\<And>x . f x \<subseteq> B_3"
    by auto
  hence 2: "\<And>x . f x = B_0 \<or> f x = B_1 \<or> f x = B_2 \<or> f x = B_3"
    by auto
  have "f = mkf B_0 B_0 \<or> f = mkf B_0 B_1 \<or> f = mkf B_0 B_2 \<or> f = mkf B_0 B_3 \<or>
        f = mkf B_1 B_0 \<or> f = mkf B_1 B_1 \<or> f = mkf B_1 B_2 \<or> f = mkf B_1 B_3 \<or>
        f = mkf B_2 B_0 \<or> f = mkf B_2 B_1 \<or> f = mkf B_2 B_2 \<or> f = mkf B_2 B_3 \<or>
        f = mkf B_3 B_0 \<or> f = mkf B_3 B_1 \<or> f = mkf B_3 B_2 \<or> f = mkf B_3 B_3"
    using 2[of b_1] 2[of b_2] mkf2[of f] by blast
  thus "P (mkf B_0 B_0) \<or> P (mkf B_0 B_1) \<or> P (mkf B_0 B_2) \<or> P (mkf B_0 B_3) \<or>
        P (mkf B_1 B_0) \<or> P (mkf B_1 B_1) \<or> P (mkf B_1 B_2) \<or> P (mkf B_1 B_3) \<or>
        P (mkf B_2 B_0) \<or> P (mkf B_2 B_1) \<or> P (mkf B_2 B_2) \<or> P (mkf B_2 B_3) \<or>
        P (mkf B_3 B_0) \<or> P (mkf B_3 B_1) \<or> P (mkf B_3 B_2) \<or> P (mkf B_3 B_3)"
    using 1 by auto
next
  assume "P (mkf B_0 B_0) \<or> P (mkf B_0 B_1) \<or> P (mkf B_0 B_2) \<or> P (mkf B_0 B_3) \<or>
          P (mkf B_1 B_0) \<or> P (mkf B_1 B_1) \<or> P (mkf B_1 B_2) \<or> P (mkf B_1 B_3) \<or>
          P (mkf B_2 B_0) \<or> P (mkf B_2 B_1) \<or> P (mkf B_2 B_2) \<or> P (mkf B_2 B_3) \<or>
          P (mkf B_3 B_0) \<or> P (mkf B_3 B_1) \<or> P (mkf B_3 B_2) \<or> P (mkf B_3 B_3)"
  thus "\<exists>f::Enum.finite_2 \<Rightarrow> Enum.finite_2 set . P f"
    by auto
qed

lemma counter_10:
  "\<exists>R::(Enum.finite_2,Enum.finite_2) mrel . \<not> (U::(Enum.finite_2,Enum.finite_2) mrel) * (U * R) \<subseteq> U * R"
  apply (rule exI[where ?x="{b_1_1,b_1_2}"])
  apply (unfold s_prod_def)
  apply (unfold ex_2_set_cases)
  apply (unfold ex_2_mrel_cases)
  apply (clarsimp simp: mr_simp ex_2_cases all_2_cases impl_2_cases)
  by auto

lemma counter_11:
  "\<exists>(R::(Enum.finite_2,Enum.finite_2) mrel) (s::(Enum.finite_2,Enum.finite_2) mrel) (t::(Enum.finite_2,Enum.finite_2) mrel) . \<not> (inner_univalent s \<and> inner_univalent t \<longrightarrow> R * (s * t) = (R * s) * t)"
  apply (rule exI[where ?x="{b_1_3}"])
  apply (rule exI[where ?x="{b_1_1,b_2_1}"])
  apply (rule exI[where ?x="{b_1_1,b_1_2}"])
  apply (unfold s_prod_def)
  apply (unfold ex_2_set_cases)
  apply (unfold ex_2_mrel_cases)
  apply (clarsimp simp: mr_simp ex_2_cases all_2_cases impl_2_cases)
  by (auto simp: times_eq_iff)

lemma counter_12:
  "\<not>(\<exists>S . 1\<^sub>\<union>\<^sub>\<union> \<odot> S = 1\<^sub>\<union>\<^sub>\<union>)"
  by (metis Int_absorb2 UNIV_I U_U cl9 co_prod cp_ii_unit_upper disjoint_iff_not_equal ic_antidist_ii ic_iu_unit ic_top iu_unit_down p_prod_comm p_prod_ild s_prod_idl s_prod_p_idl)

lemma counter_13:
  "\<not>(\<exists>S . \<forall>R . R \<odot> S = R)"
  by (meson counter_12)
end

end
