section \<open>Library Material for Extremal Graph Theory\<close>

theory Roth_Library
  imports Complex_Main "HOL-Library.Disjoint_Sets" "HOL-Library.FuncSet" "HOL-Library.Countable_Set"

(*MATERIAL INSTALLED IN DEVELOPMENT VERSION OF ISABELLE in 2021: To delete in 2022*)
begin

subsection \<open>Sets, Cardinalities, etc.\<close>

lemma card_Diff1_le: "card (A - {x}) \<le> card A"
  by (metis card.infinite card_Diff1_le eq_refl infinite_remove)

lemma partition_on_insert:
  assumes "disjnt p (\<Union>P)"
  shows "partition_on A (insert p P) \<longleftrightarrow> partition_on (A-p) P \<and> p \<subseteq> A \<and> p \<noteq> {}"
  using assms
  by (auto simp: partition_on_def disjnt_iff pairwise_insert)

(*moved from Analysis/Measure_Space to Library/Disjoint_Sets*)
lemma disjoint_family_on_insert:
  "i \<notin> I \<Longrightarrow> disjoint_family_on A (insert i I) \<longleftrightarrow> A i \<inter> (\<Union>i\<in>I. A i) = {} \<and> disjoint_family_on A I"
  by (fastforce simp: disjoint_family_on_def)

(*moved from Analysis/Ball_Volume to Nthroot*)
lemma power2_le_iff_abs_le: 
  fixes x::"'a::linordered_idom"
  shows "y \<ge> 0 \<Longrightarrow> x\<^sup>2 \<le> y\<^sup>2 \<longleftrightarrow> \<bar>x\<bar> \<le> y"
  by (metis abs_le_square_iff abs_of_nonneg)

lemma finite_inverse_image_gen:
  assumes "finite A" "inj_on f D"
  shows "finite {j\<in>D. f j \<in> A}"
  using finite_vimage_IntI [OF assms]
  by (simp add: Collect_conj_eq inf_commute vimage_def)

lemma finite_inverse_image:
  assumes "finite A" "inj f"
  shows "finite {j. f j \<in> A}"
  by (metis assms finite_vimageI vimage_def)

lemma prod_le_power:
  fixes n :: "'a::linordered_semidom"
  assumes A: "\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i \<and> f i \<le> n" "card A \<le> k" and "n \<ge> 1"
  shows "prod f A \<le> n ^ k"
  using A
proof (induction A arbitrary: k rule: infinite_finite_induct)
  case (insert i A)
  then obtain k' where k': "card A \<le> k'" "k = Suc k'"
    using Suc_le_D by force
  have "f i * prod f A \<le> n * n ^ k'"
    using insert \<open>n \<ge> 1\<close> k' by (intro prod_nonneg mult_mono; force)
  then show ?case 
    by (auto simp: \<open>k = Suc k'\<close> insert.hyps)
qed (use \<open>n \<ge> 1\<close> in auto)

lemma card_UN_disjoint':
  assumes "disjoint_family_on C I" "\<And>i. i \<in> I \<Longrightarrow> finite (C i)" "finite I"
  shows "card (\<Union>i\<in>I. C i) = (\<Sum>i\<in>I. card (C i))"
  using assms   by (simp add: card_UN_disjoint disjoint_family_on_def)

lemma product_partition:
  assumes "partition_on X R" and "\<And>U. U \<in> R \<Longrightarrow> finite U" 
  shows "card X = (\<Sum>U\<in>R. card U)"
  using assms unfolding partition_on_def
  by (meson card_Union_disjoint)

context comm_monoid_set
begin

lemma UNION_disjoint_family:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
    and "disjoint_family_on A I"
  shows "F g (\<Union>(A ` I)) = F (\<lambda>x. F g (A x)) I"
  using assms unfolding disjoint_family_on_def
  by (rule UNION_disjoint)

lemma Union_disjoint_sets:
  assumes "\<forall>A\<in>C. finite A" and "disjoint C"
  shows "F g (\<Union>C) = (F \<circ> F) g C"
  using assms unfolding disjoint_def
  by (rule Union_disjoint)

lemma card_from_nat_into:
  "F (\<lambda>i. h (from_nat_into A i)) {..<card A} = F h A"
proof (cases "finite A")
  case True
  have "F (\<lambda>i. h (from_nat_into A i)) {..<card A} = F h (from_nat_into A ` {..<card A})"
    by (metis True bij_betw_def bij_betw_from_nat_into_finite reindex_cong)
  also have "... = F h A"
    by (metis True bij_betw_def bij_betw_from_nat_into_finite)
  finally show ?thesis .
qed auto

end

lemma disjoint_family_on_iff_disjoint_image:
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<noteq> {}"
  shows "disjoint_family_on A I \<longleftrightarrow> disjoint (A ` I) \<and> inj_on A I"
proof
  assume "disjoint_family_on A I"
  then show "disjoint (A ` I) \<and> inj_on A I"
    by (metis (mono_tags, lifting) assms disjoint_family_onD disjoint_family_on_disjoint_image inf.idem inj_onI)
qed (use disjoint_image_disjoint_family_on in metis)

subsection \<open>Refinement of Partitions\<close>

definition refines :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "refines A P Q \<equiv>
        partition_on A P \<and> partition_on A Q \<and> (\<forall>X\<in>P. \<exists>Y\<in>Q. X \<subseteq> Y)" 

lemma refines_refl: "partition_on A P \<Longrightarrow> refines A P P"
  using refines_def by blast

lemma refines_asym1:
  assumes "refines A P Q" "refines A Q P"
  shows "P \<subseteq> Q"
proof 
  fix X
  assume "X \<in> P"
  then obtain Y X' where "Y \<in> Q" "X \<subseteq> Y" "X' \<in> P" "Y \<subseteq> X'"
    by (meson assms refines_def)
  then have "X' = X"
    using assms(2) unfolding partition_on_def refines_def
    by (metis \<open>X \<in> P\<close> \<open>X \<subseteq> Y\<close> disjnt_self_iff_empty disjnt_subset1 pairwiseD)
  then show "X \<in> Q"
    using \<open>X \<subseteq> Y\<close> \<open>Y \<in> Q\<close> \<open>Y \<subseteq> X'\<close> by force
qed

lemma refines_asym: "\<lbrakk>refines A P Q; refines A Q P\<rbrakk> \<Longrightarrow> P=Q"
  by (meson antisym_conv refines_asym1)

lemma refines_trans: "\<lbrakk>refines A P Q; refines A Q R\<rbrakk> \<Longrightarrow> refines A P R"
  by (meson order.trans refines_def)

lemma refines_obtains_subset:
  assumes "refines A P Q" "q \<in> Q"
  shows "partition_on q {p \<in> P. p \<subseteq> q}"
proof -
  have "p \<subseteq> q \<or> disjnt p q" if "p \<in> P" for p
    using that assms unfolding refines_def partition_on_def disjoint_def
    by (metis disjnt_def disjnt_subset1)
  with assms have "q \<subseteq> Union {p \<in> P. p \<subseteq> q}"
    using assms 
   by (clarsimp simp: refines_def disjnt_iff partition_on_def) (metis Union_iff)
  with assms have "q = Union {p \<in> P. p \<subseteq> q}"
    by auto
  then show ?thesis
    using assms by (auto simp: refines_def disjoint_def partition_on_def)
qed 

subsection \<open>Common Refinement of a Set of Partitions\<close>

definition common_refinement :: "'a set set set \<Rightarrow> 'a set set"
  where "common_refinement \<P> \<equiv> (\<Union>f \<in> (\<Pi>\<^sub>E P\<in>\<P>. P). {\<Inter> (f ` \<P>)}) - {{}}" 

text \<open>With non-extensional function space\<close>
lemma common_refinement: "common_refinement \<P> = (\<Union>f \<in> (\<Pi> P\<in>\<P>. P). {\<Inter> (f ` \<P>)}) - {{}}" 
  (is "?lhs = ?rhs")
proof
  show "?rhs \<subseteq> ?lhs"
    apply (clarsimp simp add: common_refinement_def PiE_def Ball_def)
    by (metis restrict_Pi_cancel image_restrict_eq restrict_extensional)
qed (auto simp add: common_refinement_def PiE_def)

lemma common_refinement_exists: "\<lbrakk>X \<in> common_refinement \<P>; P \<in> \<P>\<rbrakk> \<Longrightarrow> \<exists>R\<in>P. X \<subseteq> R"
  by (auto simp add: common_refinement)

lemma Union_common_refinement: "\<Union> (common_refinement \<P>) = (\<Inter> P\<in>\<P>. \<Union>P)"
proof
  show "(\<Inter> P\<in>\<P>. \<Union>P) \<subseteq> \<Union> (common_refinement \<P>)"
  proof (clarsimp simp: common_refinement)
    fix x
    assume "\<forall>P\<in>\<P>. \<exists>X\<in>P. x \<in> X"
    then obtain F where F: "\<And>P. P\<in>\<P> \<Longrightarrow> F P \<in> P \<and> x \<in> F P"
      by metis
    then have "x \<in> \<Inter> (F ` \<P>)"
      by force
    with F show "\<exists>X\<in>(\<Union>x\<in>\<Pi> P\<in>\<P>. P. {\<Inter> (x ` \<P>)}) - {{}}. x \<in> X"
      by (auto simp add: Pi_iff Bex_def)
  qed
qed (auto simp: common_refinement_def)

lemma partition_on_common_refinement:
  assumes A: "\<And>P. P \<in> \<P> \<Longrightarrow> partition_on A P" and "\<P> \<noteq> {}"
  shows "partition_on A (common_refinement \<P>)"
proof (rule partition_onI)
  show "\<Union> (common_refinement \<P>) = A"
    using assms by (simp add: partition_on_def Union_common_refinement)
  fix P Q
  assume "P \<in> common_refinement \<P>" and "Q \<in> common_refinement \<P>" and "P \<noteq> Q"
  then obtain f g where f: "f \<in> (\<Pi>\<^sub>E P\<in>\<P>. P)" and P: "P = \<Inter> (f ` \<P>)" and "P \<noteq> {}"
                  and   g: "g \<in> (\<Pi>\<^sub>E P\<in>\<P>. P)" and Q: "Q = \<Inter> (g ` \<P>)" and "Q \<noteq> {}"
    by (auto simp add: common_refinement_def)
  have "f=g" if "x \<in> P" "x \<in> Q" for x
  proof (rule extensionalityI [of _ \<P>])
    fix R
    assume "R \<in> \<P>"
    with that P Q f g A [unfolded partition_on_def, OF \<open>R \<in> \<P>\<close>]
    show "f R = g R"
      by (metis INT_E Int_iff PiE_iff disjointD emptyE)
  qed (use PiE_iff f g in auto)
  then show "disjnt P Q"
    by (metis P Q \<open>P \<noteq> Q\<close> disjnt_iff) 
qed (simp add: common_refinement_def)

lemma refines_common_refinement:
  assumes "\<And>P. P \<in> \<P> \<Longrightarrow> partition_on A P" "P \<in> \<P>"
  shows "refines A (common_refinement \<P>) P"
  unfolding refines_def
proof (intro conjI strip)
  fix X
  assume "X \<in> common_refinement \<P>"
  with assms show "\<exists>Y\<in>P. X \<subseteq> Y"
    by (auto simp: common_refinement_def)
qed (use assms partition_on_common_refinement in auto)

text \<open>The common refinement is itself refined by any other\<close>
lemma common_refinement_coarsest:
  assumes "\<And>P. P \<in> \<P> \<Longrightarrow> partition_on A P" "partition_on A R" "\<And>P. P \<in> \<P> \<Longrightarrow> refines A R P" "\<P> \<noteq> {}"
  shows "refines A R (common_refinement \<P>)"
  unfolding refines_def
proof (intro conjI ballI partition_on_common_refinement)
  fix X
  assume "X \<in> R"
  have "\<exists>p \<in> P. X \<subseteq> p" if "P \<in> \<P>" for P
    by (meson \<open>X \<in> R\<close> assms(3) refines_def that)
  then obtain F where f: "\<And>P. P \<in> \<P> \<Longrightarrow> F P \<in> P \<and> X \<subseteq> F P"
    by metis
  with \<open>partition_on A R\<close> \<open>X \<in> R\<close> \<open>\<P> \<noteq> {}\<close>
  have "\<Inter> (F ` \<P>) \<in> common_refinement \<P>"
    apply (simp add: partition_on_def common_refinement Pi_iff Bex_def)
    by (metis (no_types, lifting) cINF_greatest subset_empty)
  with f show "\<exists>Y\<in>common_refinement \<P>. X \<subseteq> Y"
    by (metis \<open>\<P> \<noteq> {}\<close> cINF_greatest)
qed (use assms in auto)

lemma finite_common_refinement:
  assumes "finite \<P>" "\<And>P. P \<in> \<P> \<Longrightarrow> finite P"
  shows "finite (common_refinement \<P>)"
proof -
  have "finite (\<Pi>\<^sub>E P\<in>\<P>. P)"
    by (simp add: assms finite_PiE)
  then show ?thesis
    by (auto simp: common_refinement_def)
qed

lemma card_common_refinement:
  assumes "finite \<P>" "\<And>P. P \<in> \<P> \<Longrightarrow> finite P"
  shows "card (common_refinement \<P>) \<le> (\<Prod>P \<in> \<P>. card P)"
proof -
  have "card (common_refinement \<P>) \<le> card (\<Union>f \<in> (\<Pi>\<^sub>E P\<in>\<P>. P). {\<Inter> (f ` \<P>)})"
    unfolding common_refinement_def by (meson card_Diff1_le)
  also have "\<dots> \<le> (\<Sum>f\<in>(\<Pi>\<^sub>E P\<in>\<P>. P). card{\<Inter> (f ` \<P>)})"
    by (metis assms finite_PiE card_UN_le)
  also have "\<dots> = card(\<Pi>\<^sub>E P\<in>\<P>. P)"
    by simp
  also have "\<dots> = (\<Prod>P \<in> \<P>. card P)"
    by (simp add: assms(1) card_PiE dual_order.eq_iff)
  finally show ?thesis .
qed

end
