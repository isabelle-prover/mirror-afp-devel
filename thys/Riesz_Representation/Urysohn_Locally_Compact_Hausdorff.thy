(*  Title:   Urysohn_Locally_Compact_Hausdorff.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>Urysohn's Lemma \<close>
theory Urysohn_Locally_Compact_Hausdorff
  imports "Standard_Borel_Spaces.StandardBorel"
begin

text \<open> We prove Urysohn's lemma for locally compact Hausdorff space (Lemma 2.12~\cite{Rudin}) \<close>

subsection \<open> Lemmas for Upper/Lower Semi-Continuous Functions \<close>
lemma 
  assumes "\<And>x. x \<in> topspace X \<Longrightarrow> f x = g x"
  shows upper_semicontinuous_map_cong:
    "upper_semicontinuous_map X f \<longleftrightarrow> upper_semicontinuous_map X g" (is ?g1)
    and lower_semicontinuous_map_cong:
    "lower_semicontinuous_map X f \<longleftrightarrow> lower_semicontinuous_map X g" (is ?g2)
proof -
  have [simp]:"\<And>a. {x\<in>topspace X. f x < a} = {x\<in>topspace X. g x < a}"
              "\<And>a. {x\<in>topspace X. f x > a} = {x\<in>topspace X. g x > a}"
    using assms by auto
  show ?g1 ?g2
    by(auto simp: upper_semicontinuous_map_def lower_semicontinuous_map_def)
qed

lemma upper_lower_semicontinuous_map_iff_continuous_map:
  "continuous_map X euclidean f \<longleftrightarrow> upper_semicontinuous_map X f \<and> lower_semicontinuous_map X f"
  using continuous_map_upper_lower_semicontinuous_lt
        lower_semicontinuous_map_def upper_semicontinuous_map_def
  by blast

lemma [simp]:
  shows upper_semicontinuous_map_const: "upper_semicontinuous_map X (\<lambda>x. c)"
    and lower_semicontinuous_map_const: "lower_semicontinuous_map X (\<lambda>x. c)"
  using continuous_map_const[of _ euclidean c]
  unfolding upper_lower_semicontinuous_map_iff_continuous_map by auto

(* TODO: generalize the following with type classes *)
lemma upper_semicontinuous_map_c_add_iff:
  fixes c :: real
  shows "upper_semicontinuous_map X (\<lambda>x. c + f x) \<longleftrightarrow> upper_semicontinuous_map X f"
proof -
  have [simp]: "c + f x < a \<longleftrightarrow> f x < a - c" for x a
    by auto
  show ?thesis
    by(simp add: upper_semicontinuous_map_def) (metis add_diff_cancel_left')
qed

corollary upper_semicontinuous_map_add_c_iff:
  fixes c :: real
  shows "upper_semicontinuous_map X (\<lambda>x. f x + c) \<longleftrightarrow> upper_semicontinuous_map X f"
  by(simp add: add.commute upper_semicontinuous_map_c_add_iff)
(* TODO: end *)

lemma upper_semicontinuous_map_posreal_cmult_iff:
  fixes c :: real
  assumes "c > 0"
  shows "upper_semicontinuous_map X (\<lambda>x. c * f x) \<longleftrightarrow> upper_semicontinuous_map X f"
proof -
  have [simp]: "c * f x < a \<longleftrightarrow> f x < a / c" for x a
    using assms by (simp add: less_divide_eq mult.commute)
  thus ?thesis
    by(simp add: upper_semicontinuous_map_def)
      (metis assms less_numeral_extra(3) nonzero_mult_div_cancel_left)
qed

lemma upper_semicontinuous_map_real_cmult:
  fixes c :: real
  assumes "c \<ge> 0" "upper_semicontinuous_map X f"
  shows "upper_semicontinuous_map X (\<lambda>x. c * f x)"
  by(cases "c = 0")
    (use assms upper_semicontinuous_map_posreal_cmult_iff[simplified dual_order.strict_iff_order] in auto)

(* TODO: neg times *)
lemma lower_semicontinuous_map_posreal_cmult_iff:
  fixes c :: real
  assumes "c > 0"
  shows "lower_semicontinuous_map X (\<lambda>x. c * f x) \<longleftrightarrow> lower_semicontinuous_map X f"
proof -
  have [simp]: "c * f x > a \<longleftrightarrow> f x > a / c" for x a
    by (simp add: assms divide_less_eq mult.commute)
  show ?thesis
    by(simp add: lower_semicontinuous_map_def)
      (metis assms less_numeral_extra(3) nonzero_mult_div_cancel_left)
qed

lemma lower_semicontinuous_map_real_cmult:
  fixes c :: real
  assumes "c \<ge> 0" "lower_semicontinuous_map X f"
  shows "lower_semicontinuous_map X (\<lambda>x. c * f x)"
  by(cases "c = 0")
    (use assms lower_semicontinuous_map_posreal_cmult_iff[simplified dual_order.strict_iff_order] in auto)

lemma upper_semicontinuous_map_INF:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> 'a :: {linorder_topology, complete_linorder}"
  assumes "\<And>i. i \<in> I \<Longrightarrow>  upper_semicontinuous_map X (f i)"
  shows "upper_semicontinuous_map X (\<lambda>x. \<Sqinter>i\<in>I. f i x)"
  unfolding upper_semicontinuous_map_def
proof
  fix a
  have "{x \<in> topspace X. (\<Sqinter>i\<in>I. f i x) < a} = (\<Union>i\<in>I. {x\<in>topspace X. f i x < a})"
    by(auto simp: Inf_less_iff)
  also have "openin X ..."
    using assms by(auto simp: upper_semicontinuous_map_def)
  finally show "openin X {x \<in> topspace X. (\<Sqinter>i\<in>I. f i x) < a}" .
qed

lemma upper_semicontinuous_map_cInf:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> 'a :: {linorder_topology, conditionally_complete_linorder}"
  assumes "I \<noteq> {}" "\<And>x. x \<in> topspace X \<Longrightarrow> bdd_below ((\<lambda>i. f i x) ` I)"
      and "\<And>i. i \<in> I \<Longrightarrow>  upper_semicontinuous_map X (f i)"
    shows "upper_semicontinuous_map X (\<lambda>x. \<Sqinter>i\<in>I. f i x)"
  unfolding upper_semicontinuous_map_def
proof
  fix a
  have [simp]:"\<And>x. x \<in> topspace X \<Longrightarrow> (\<Sqinter>i\<in>I. f i x) < a \<longleftrightarrow> (\<exists>x\<in>(\<lambda>i. f i x) ` I. x < a)"
    by(intro cInf_less_iff) (use assms in auto)
  have "{x \<in> topspace X. (\<Sqinter>i\<in>I. f i x) < a} = (\<Union>i\<in>I. {x\<in>topspace X. f i x < a})"
    by auto
  also have "openin X ..."
    using assms by(auto simp: upper_semicontinuous_map_def)
  finally show "openin X {x \<in> topspace X. (\<Sqinter>i\<in>I. f i x) < a}" .
qed

lemma lower_semicontinuous_map_Sup:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> 'a :: {linorder_topology, complete_linorder}"
  assumes "\<And>i. i \<in> I \<Longrightarrow>  lower_semicontinuous_map X (f i)"
  shows "lower_semicontinuous_map X (\<lambda>x. \<Squnion>i\<in>I. f i x)"
  unfolding lower_semicontinuous_map_def
proof
  fix a
  have "{x \<in> topspace X. (\<Squnion>i\<in>I. f i x) > a} = (\<Union>i\<in>I. {x\<in>topspace X. f i x > a})"
    by(auto simp: less_Sup_iff)
  also have "openin X ..."
    using assms by(auto simp: lower_semicontinuous_map_def)
  finally show "openin X {x \<in> topspace X. (\<Squnion>i\<in>I. f i x) > a}" .
qed

lemma indicator_closed_upper_semicontinuous_map:
  assumes "closedin X C"
  shows "upper_semicontinuous_map X (indicator C :: _ \<Rightarrow> 'a :: {zero_less_one, linorder_topology})"
  unfolding upper_semicontinuous_map_def
proof safe
  fix a :: 'a
  consider "a \<le> 0" | "0 < a" "a \<le> 1" | "1 < a"
    by fastforce
  then show "openin X {x \<in> topspace X. indicator C x < a}"
  proof cases
    case 1
    then have [simp]:"{x \<in> topspace X. indicator C x < a} = {}"
      by(simp add: indicator_def) (meson order.strict_iff_not order.trans zero_less_one_class.zero_le_one)
    show ?thesis
      by simp
  next
    case 2
    then have [simp]:"{x \<in> topspace X. indicator C x < a} = topspace X - C"
      by(fastforce simp add: indicator_def)
    show ?thesis
      using assms by auto
  next
    case 3
    then have [simp]: "{x \<in> topspace X. indicator C x < a} = topspace X"
      by (simp add: indicator_def dual_order.strict_trans2)
    show ?thesis
      by simp
  qed
qed

lemma indicator_open_lower_semicontinuous_map:
  assumes "openin X U"
  shows "lower_semicontinuous_map X (indicator U :: _ \<Rightarrow> 'a :: {zero_less_one, linorder_topology})"
  unfolding lower_semicontinuous_map_def
proof safe
  fix a :: 'a
  consider "a < 0" | "0 \<le> a" "a < 1" | "1 \<le> a"
    by fastforce
  then show "openin X {x \<in> topspace X. a < indicator U x}"
  proof cases
    case 1
    then have [simp]: "{x \<in> topspace X. a < indicator U x} = topspace X"
      using order_less_trans by (fastforce simp add: indicator_def )
    show ?thesis
      by simp
  next
    case 2
    then have [simp]:"{x \<in> topspace X. a < indicator U x} = U"
      using openin_subset[OF assms] by(simp add: indicator_def) fastforce
    show ?thesis
      by(simp add: assms)
  next
    case 3
    then have [simp]:"{x \<in> topspace X. a < indicator U x} = {}"
      by(simp add: indicator_def) (meson dual_order.strict_trans leD zero_less_one)
    show ?thesis
      by simp
  qed
qed

lemma lower_semicontinuous_map_cSup:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> 'a :: {linorder_topology, conditionally_complete_linorder}"
  assumes "I \<noteq> {}" "\<And>x. x \<in> topspace X \<Longrightarrow> bdd_above ((\<lambda>i. f i x) ` I)"
      and "\<And>i. i \<in> I \<Longrightarrow>  lower_semicontinuous_map X (f i)"
  shows "lower_semicontinuous_map X (\<lambda>x. \<Squnion>i\<in>I. f i x)"
  unfolding lower_semicontinuous_map_def
proof
  fix a
  have [simp]:"\<And>x. x \<in> topspace X \<Longrightarrow> (\<Squnion>i\<in>I. f i x) > a \<longleftrightarrow> (\<exists>x\<in>(\<lambda>i. f i x) ` I. x > a)"
    by(intro less_cSup_iff) (use assms in auto)
  have "{x \<in> topspace X. (\<Squnion>i\<in>I. f i x) > a} = (\<Union>i\<in>I. {x\<in>topspace X. f i x > a})"
    by(auto simp: less_Sup_iff)
  also have "openin X ..."
    using assms by(auto simp: lower_semicontinuous_map_def)
  finally show "openin X {x \<in> topspace X. (\<Squnion>i\<in>I. f i x) > a}" .
qed

lemma openin_continuous_map_less:
  assumes "continuous_map X (euclidean :: ('a :: {dense_linorder, order_topology}) topology) f"
    and "continuous_map X euclidean g"
  shows "openin X {x\<in>topspace X. f x < g x}"
proof -
  have "{x\<in>topspace X. f x < g x} = {x\<in>topspace X. \<exists>r. f x < r \<and> r < g x}"
    using dense order.strict_trans by blast
  also have "... = (\<Union>r. {x\<in>topspace X. f x < r} \<inter> {x\<in>topspace X. r < g x})"
    by blast
  also have "openin X ..."
    using assms by(fastforce simp: continuous_map_upper_lower_semicontinuous_lt)
  finally show ?thesis .
qed

corollary closedin_continuous_map_eq:
  assumes "continuous_map X (euclidean :: ('a :: {dense_linorder, order_topology}) topology) f"
    and "continuous_map X euclidean g"
  shows "closedin X {x\<in>topspace X. f x = g x}"
proof -
  have "{x\<in>topspace X. f x = g x} = topspace X - ({x\<in>topspace X. f x < g x} \<union> {x\<in>topspace X. f x > g x})"
    by auto
  also have "closedin X ..."
    using openin_continuous_map_less[OF assms] openin_continuous_map_less[OF assms(2,1)]
    by blast
  finally show ?thesis .
qed

subsection  \<open>Urysohn's Lemma \<close>
lemma locally_compact_Hausdorff_compactin_openin_subset:
  assumes "locally_compact_space X" "Hausdorff_space X \<or> regular_space X"
      and "compactin X T" "openin X V" "T \<subseteq> V"
    shows "\<exists>U. openin X U \<and> compactin X (X closure_of U) \<and> T \<subseteq> U \<and> (X closure_of U) \<subseteq> V"
proof -
  have "\<And>x W. openin X W \<Longrightarrow> x \<in> W
               \<Longrightarrow> (\<exists>U V. openin X U \<and> (compactin X V \<and> closedin X V) \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W)"
    using assms(1) by(auto simp: locally_compact_space_neighbourhood_base_closedin[OF assms(2)] neighbourhood_base_of)
  from this[OF assms(4)] have "\<forall>x\<in>T. \<exists>U W. openin X U \<and> (compactin X W \<and> closedin X W) \<and> x \<in> U \<and> U \<subseteq> W \<and> W \<subseteq> V"
    using assms(5) by blast
  then have "\<exists>Ux Wx. \<forall>x\<in>T. openin X (Ux x) \<and> compactin X (Wx x) \<and> closedin X (Wx x) \<and> x \<in> Ux x \<and> Ux x \<subseteq> Wx x \<and> Wx x \<subseteq> V"
    by metis
  then obtain Ux Wx where UW: "\<And>x. x \<in> T \<Longrightarrow> openin X (Ux x)" "\<And>x. x \<in> T \<Longrightarrow> compactin X (Wx x)" "\<And>x. x \<in> T \<Longrightarrow> closedin X (Wx x)"
   "\<And>x. x \<in> T \<Longrightarrow> x \<in> Ux x" "\<And>x. x \<in> T \<Longrightarrow> Ux x \<subseteq> Wx x" "\<And>x. x \<in> T \<Longrightarrow> Wx x \<subseteq> V"
    by blast
  have "T \<subseteq> (\<Union>x\<in>T. Ux x)"
    using UW by blast
  hence "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> Ux ` T \<and> T \<subseteq> \<Union> \<F>"
    using compactinD[OF assms(3),of "Ux ` T"] UW(1) by auto
  then obtain T' where T': "finite T'" "T' \<subseteq> T" "T \<subseteq> (\<Union>x\<in>T'. Ux x)"
    by (metis finite_subset_image)
  have 1:"X closure_of \<Union> (Ux ` T') = (\<Union>x\<in>T'. X closure_of (Ux x))"
    by (simp add: T'(1) closure_of_Union)
  have 2:"\<And>x. x \<in> T' \<Longrightarrow> X closure_of (Ux x) \<subseteq> Wx x"
    by (meson T'(2) UW(3) UW(5) closure_of_minimal subsetD)
  hence "\<And>x. x \<in> T' \<Longrightarrow> compactin X (X closure_of (Ux x))"
    by (meson T'(2) UW(2) closed_compactin closedin_closure_of subsetD)
  then show ?thesis
    using T' 2 UW by(fastforce intro!: exI[where x="\<Union>x\<in>T'. Ux x"] compactin_Union simp: 1)
qed

lemma Urysohn_locally_compact_Hausdorff_closed_compact_support:
  fixes a b :: real and X :: "'a topology"
  assumes "locally_compact_space X" "Hausdorff_space X \<or> regular_space X"
      and "a \<le> b" "closedin X S" "compactin X T" "disjnt S T"
  obtains f where "continuous_map X (subtopology euclidean {a..b}) f" "f ` S \<subseteq> {a}" "f ` T \<subseteq> {b}" "disjnt (X closure_of {x\<in>topspace X. f x \<noteq> a}) S" "compactin X (X closure_of {x\<in>topspace X. f x \<noteq> a})"
proof -
  have "\<exists>f. continuous_map X (subtopology euclidean {0..1::real}) f \<and> f ` S \<subseteq> {0} \<and> f ` T \<subseteq> {1} \<and> disjnt (X closure_of {x\<in>topspace X. f x \<noteq> 0}) S \<and>  compactin X (X closure_of {x\<in>topspace X. f x \<noteq> 0})"
  proof -
    define r :: "nat \<Rightarrow> real" where "r \<equiv> (\<lambda>n. if n = 0 then 0 else if n = 1 then 1 else from_nat_into ({0<..<1} \<inter> \<rat>) (n - 2))"
    have r_01: "r 0 = 0" "r (Suc 0) = 1"
      by(simp_all add: r_def)
    have r_bij: "bij_betw r UNIV ({0..1} \<inter> \<rat>)"
    proof -
      have 1:"bij_betw (from_nat_into ({0<..<1::real} \<inter> \<rat>)) UNIV ({0<..<1} \<inter> \<rat>)"
      proof -
        have [simp]:"infinite ({0<..<1::real} \<inter> \<rat>)"
        proof -
          have "{0<..<1::real} \<inter> \<rat> = of_rat ` {0<..<1::rat}"
            by(auto simp: Rats_def)
          also have "infinite ..."
          proof
            assume "finite (real_of_rat ` {0<..<1})"
            moreover have "finite (real_of_rat ` {0<..<1}) \<longleftrightarrow> finite {0<..<1::rat}"
              by(auto intro!: finite_image_iff inj_onI)
            ultimately show False
              using infinite_Ioo[of 0 "1 :: rat"] by simp
          qed
          finally show ?thesis .
        qed
        show ?thesis
          using countable_rat by(auto intro!: from_nat_into_to_nat_on_product_metric_pair)
      qed
      have 2: "bij_betw r ({2..}) ({0<..<1} \<inter> \<rat>)"
      proof -
        have 3:"bij_betw (\<lambda>n. n - 2) {2::nat..} UNIV"
          by(auto simp: bij_betw_def image_def intro!: inj_onI bexI[where x="_ + 2"])
        have 4:"bij_betw (\<lambda>n. r (n + 2)) UNIV ({0<..<1} \<inter> \<rat>)"
          using 1 by(auto simp: r_def)
        have 5:" bij_betw (\<lambda>n. r (Suc (Suc (n - 2)))) {2..} ({0<..<1} \<inter> \<rat>)"
          using bij_betw_comp_iff[THEN iffD1,OF 3 4] by(auto simp: comp_def)
        show ?thesis
          by(rule bij_betw_cong[THEN iffD1,OF _ 5]) (simp add: Suc_diff_Suc numeral_2_eq_2) 
      qed
      have [simp]: "insert (Suc 0) (insert 0 {2..}) = UNIV" "insert 1 (insert 0 ({0<..<1::real} \<inter> \<rat>)) = {0..1} \<inter> \<rat>"
        by auto
      show ?thesis
        using notIn_Un_bij_betw[of 1,OF _ _ notIn_Un_bij_betw[of 0,OF _ _ 2]] by(auto simp: r_01)
    qed
    have r0_min: "\<And>n. n \<noteq> 0 \<longleftrightarrow> r 0 < r n"
      using r_bij r_01 by (metis (full_types) IntE UNIV_I atLeastAtMost_iff bij_betw_iff_bijections linorder_not_le not_less_iff_gr_or_eq) 
    have r1_max: "\<And>n. n \<noteq> 1 \<longleftrightarrow> r n < r 1"
      using r_bij r_01(2) by (metis (no_types, opaque_lifting) IntD2 One_nat_def UNIV_I atLeastAtMost_iff bij_betw_iff_bijections inf_commute linorder_less_linear linorder_not_le)
    let ?V = "topspace X - S"
    have openinV: "openin X ?V"
      using assms(4) by blast
    have T_sub_V: "T \<subseteq> ?V"
      by(meson DiffI assms(5,6) compactin_subset_topspace disjnt_iff subset_eq)
    obtain V0 where V0: "openin X V0" "compactin X (X closure_of V0)" "T \<subseteq> V0" "X closure_of V0 \<subseteq> ?V"
      using locally_compact_Hausdorff_compactin_openin_subset[OF assms(1,2) assms(5) openinV T_sub_V] by metis
    obtain V1 where V1: "openin X V1" "compactin X (X closure_of V1)" "T \<subseteq> V1" "X closure_of V1 \<subseteq> V0"
      using locally_compact_Hausdorff_compactin_openin_subset[OF assms(1,2) assms(5) V0(1,3)] by metis
    text \<open> arg max \<close>
    have "\<exists>i. i < n \<and> r i < r n \<and> (\<forall>m. m < n \<and> r m < r n \<longrightarrow> r m \<le> r i)" if n: "n \<ge> 2" for n
    proof -
      have 1:"{m. m < n \<and> r m < r n} \<noteq> {}"
      proof -
        have "n \<noteq> 0"
          using n by fastforce
        hence "r n \<noteq> r 0"
          by (metis UNIV_I r_bij bij_betw_iff_bijections)
        hence "r n > r 0"
          by (metis IntE UNIV_I atLeastAtMost_iff bij_betw_iff_bijections order_less_le r_01(1) r_bij)
        hence "0 \<in> {m. m < n \<and> r n > r m}"
          using n by auto
        thus ?thesis
          by auto
      qed
      have 2:"finite {m. m < n \<and> r n > r m}"
        by auto
      define ri where "ri \<equiv> Max (r ` {m. m < n \<and> r n > r m})"
      have ri_1: "ri \<in> r ` {m. m < n \<and> r n > r m}"
        unfolding ri_def using 1 2 by auto
      have ri_2: "\<And>m. m < n \<Longrightarrow> r n > r m \<Longrightarrow> r m \<le> ri"
        unfolding ri_def by(subst Max_ge_iff) (use 1 2 in auto)
      obtain i where i:"ri = r i" "i < n" "r n > r i"
        using ri_1 by auto
      thus ?thesis
        using ri_2 by(auto intro!: exI[where x=i])
    qed
    then obtain i where i: "\<And>n. n \<ge> 2 \<Longrightarrow> i n < n" "\<And>n. n \<ge> 2 \<Longrightarrow> r (i n) < r n"
                           "\<And>n m. n \<ge> 2 \<Longrightarrow> m < n \<Longrightarrow> r m < r n \<Longrightarrow> r m \<le> r (i n)"
      by metis
    text \<open> arg min \<close>
    have "\<exists>j. j < n \<and> r n < r j \<and> (\<forall>m. m < n \<and> r n < r m \<longrightarrow> r j \<le> r m)" if n: "n \<ge> 2" for n
    proof -
      have 1:"{m. m < n \<and> r n < r m} \<noteq> {}"
      proof -
        have "n \<noteq> 1"
          using n by fastforce
        hence "r n \<noteq> r 1"
          by (metis UNIV_I r_bij bij_betw_iff_bijections)
        hence "r n < r 1"
          by (metis IntE One_nat_def UNIV_I atLeastAtMost_iff bij_betw_iff_bijections order_less_le r_01(2) r_bij)
        hence "1 \<in> {m. m < n \<and> r n < r m}"
          using n by auto
        thus ?thesis
          by auto
      qed
      have 2:"finite {m. m < n \<and> r n < r m}"
        by auto
      define rj where "rj \<equiv> Min (r ` {m. m < n \<and> r n < r m})"
      have rj_1: "rj \<in> r ` {m. m < n \<and> r n < r m}"
        unfolding rj_def using 1 2 by auto
      have rj_2: "\<And>m. m < n \<Longrightarrow> r n < r m \<Longrightarrow> rj \<le> r m"
        unfolding rj_def by(subst Min_le_iff) (use 1 2 in auto)
      obtain j where j:"rj = r j" "j < n" "r n < r j"
        using rj_1 by auto
      thus ?thesis
        using rj_2 by(auto intro!: exI[where x=j])
    qed
    then obtain j where j: "\<And>n. n \<ge> 2 \<Longrightarrow> j n < n" "\<And>n. n \<ge> 2 \<Longrightarrow> r (j n) > r n" "\<And>n m. n \<ge> 2 \<Longrightarrow> m < n \<Longrightarrow> r m > r n \<Longrightarrow> r m \<ge> r (j n)"
      by metis
    have i2: "i 2 = 0" 
      by (metis i(1,2) One_nat_def dual_order.refl less_2_cases not_less_iff_gr_or_eq r1_max)
    have j2: "j 2 = 1"
      by (metis j(1,2) One_nat_def dual_order.refl i(2) i2 less_2_cases not_less_iff_gr_or_eq)
    have "\<exists>Vn. \<forall>n. Vn n = (if n = 0 then V0 else if n = 1 then V1
       else (SOME V. openin X V \<and> compactin X (X closure_of V) \<and> X closure_of Vn (j n) \<subseteq> V \<and> X closure_of V \<subseteq> Vn (i n)))"
      (is "\<exists>Vn. \<forall>n. Vn n = ?if n Vn")
    proof(rule dependent_wellorder_choice)
      fix r n and Vn Vn' :: "nat \<Rightarrow> 'a set"
      assume h:"\<And>y::nat. y < n \<Longrightarrow> Vn y = Vn' y"
      consider "n \<ge> 2" | "n = 0" | "n = 1"
        by fastforce
      then show "r = ?if n Vn \<longleftrightarrow> r = ?if n Vn'"
        by cases (use i j h in auto)
    qed auto
    then obtain Vn where Vn_def: "\<And>n. Vn n = (if n = 0 then V0 else if n = 1 then V1
       else (SOME V. openin X V \<and> compactin X (X closure_of V) \<and> X closure_of Vn (j n) \<subseteq> V \<and> X closure_of V \<subseteq> Vn (i n)))"
      by blast
    have Vn_0: "Vn 0 = V0" and Vn_1: "Vn 1 = V1"
      by(auto simp: Vn_def)
    have Vns: "(n \<ge> 2 \<longrightarrow> openin X (Vn n) \<and> compactin X (X closure_of Vn n) \<and>
                X closure_of Vn (j n) \<subseteq> Vn n \<and> X closure_of Vn n \<subseteq> Vn (i n)) \<and>
                (\<forall>k\<le>n. \<forall>l\<le>n. r k < r l \<longrightarrow> X closure_of Vn l \<subseteq> Vn k)" (is "?P1 n \<and> ?P2 n") for n
    proof(rule nat_less_induct[of _ n])
      fix n
      assume h:"\<forall>m<n. ?P1 m \<and> ?P2 m"
      show "?P1 n \<and> ?P2 n"
      proof
        show P1:"?P1 n"
        proof
          assume n: "2 \<le> n"
          then consider "n = 2" | "n > 2"
            by fastforce
          then show "openin X (Vn n) \<and> compactin X (X closure_of Vn n) \<and>
                     X closure_of Vn (j n) \<subseteq> Vn n \<and> X closure_of Vn n \<subseteq> Vn (i n)"
          proof cases
            case 1
            have 2:"Vn 2 = (SOME V. openin X V \<and> compactin X (X closure_of V) \<and>
                    X closure_of Vn 1 \<subseteq> V \<and> X closure_of V \<subseteq> Vn 0)"
              by(simp add: Vn_def i2 j2 1)
            show ?thesis
              unfolding 1 i2 j2 Vn_0 Vn_1 2
              by(rule someI_ex)
                (auto intro!: V0 V1 locally_compact_Hausdorff_compactin_openin_subset[OF assms(1,2)])
          next
            case 2
            then have 1:"Vn n = (SOME V. openin X V \<and> compactin X (X closure_of V) \<and> X closure_of Vn (j n) \<subseteq> V \<and> X closure_of V \<subseteq> Vn (i n))"
              by(auto simp: Vn_def)
            show ?thesis
              unfolding 1
            proof(rule someI_ex)
              have ij:"j n < n" "i n < n" "r (i n) < r (j n)"
                using j[of n] i[of n] order.strict_trans 2 by auto
              hence "max (j n) (i n) < n"
                by auto
              from h[rule_format,OF this] ij(3) have ijsub:"X closure_of Vn (j n) \<subseteq> Vn (i n)"
                by auto
              have jc:"compactin X (X closure_of Vn (j n))"
              proof -
                consider "j n \<ge> 2" | "j n = 0" | "j n = 1"
                  by fastforce
                then show ?thesis
                proof cases
                  case 1
                  then show ?thesis
                    using ij(1) h by auto
                qed(auto simp: Vn_0 Vn_1[simplified] V0 V1)
              qed
              have io:"openin X (Vn (i n))"
              proof -
                consider "i n \<ge> 2" | "i n = 0" | "i n = 1"
                  by fastforce
                then show ?thesis
                proof cases
                  case 1
                  then show ?thesis
                    using ij(2) h by auto
                qed(auto simp: Vn_0 Vn_1[simplified] V0 V1)
              qed
              show "\<exists>x. openin X x \<and> compactin X (X closure_of x) \<and> X closure_of Vn (j n) \<subseteq> x \<and> X closure_of x \<subseteq> Vn (i n)"
                by(rule locally_compact_Hausdorff_compactin_openin_subset[OF assms(1,2) jc io ijsub])
            qed
          qed
        qed
        show "?P2 n"
        proof(intro allI impI)
          fix k l
          assume kl: "k \<le> n" "l \<le> n" "r k < r l"
          then consider "n = 1" | "n \<ge> 2"
            using r_bij order_neq_le_trans by fastforce 
          then show "X closure_of Vn l \<subseteq> Vn k"
          proof cases
            case 1
            then have [simp]: "k = 0" "l = 1"
              using r_01 kl le_Suc_eq by fastforce+ 
            show ?thesis
              using Vn_0 Vn_1 V0 V1 by simp
          next
            case n:2
            consider "k < n" "l < n" | "k = n" "l < n" | "k < n" "l = n"
              using kl order_less_le by auto
            then show ?thesis
            proof cases
              case 1
              with kl(3) h show ?thesis
                by (meson nle_le)
            next
              case k:2
              then have k1:"X closure_of Vn (j k) \<subseteq> Vn k"
                using P1 n by simp
              consider "r (j k) = r l" | "r (j k) < r l"
                using j(3)[OF _ _ kl(3)] k n by fastforce
              then show ?thesis
              proof cases
                case 1
                then have "j k = l"
                  using r_bij by(auto simp: bij_betw_def injD)
                with k1 show ?thesis by simp
              next
                case 2
                then have " X closure_of Vn l \<subseteq> Vn (j k)"
                  using k h by (meson j(1) n nat_le_linear)
                thus ?thesis
                  using k1 closure_of_mono by fastforce
              qed
            next
              case l:3
              consider "r k = r (i l)" | "r k < r (i l)"
                using i(3)[OF _ _ kl(3)] l n by fastforce
              then show ?thesis
              proof cases
                case 1
                then have "k = i l"
                  using r_bij by(auto simp: bij_betw_def injD)
                thus ?thesis
                  using P1 l(2) n by blast 
              next
                case 2
                then have " X closure_of Vn (i l) \<subseteq> Vn k"
                  by (metis h i(1) l(1) l(2) n nle_le)
                thus ?thesis
                  by (metis P1 closure_of_closure_of closure_of_mono l(2) n subset_trans)
              qed
            qed
          qed
        qed
      qed
    qed

    define Vr where "Vr \<equiv> (\<lambda>x. let n = THE n. x = r n in Vn n)"
    have Vr_Vn: "Vr (r n) = Vn n" for n
    proof -
      have 1:"\<And>n m. r n = r m \<longleftrightarrow> n = m"
        using r_bij by(auto simp: bij_betw_def injD)
      have [simp]:"(THE m. r n = r m) = n"
        by(auto simp: 1)
      show ?thesis
        by(simp add: Vr_def)
    qed
    have Vr0: "Vr 0 = V0"
      using Vr_Vn[of 0] by(auto simp: Vn_0 r_01)
    have Vr1: "Vr 1 = V1"
      using Vr_Vn[of 1] Vn_1 by(auto simp: r_01)
    have openin_Vr: "openin X (Vr s)" if s:"s \<in> {0..1} \<inter> \<rat>" for s
    proof -
      consider "0 < s" "s < 1" | "s = 0" | "s = 1"
        using s by fastforce
      then show ?thesis
      proof cases
        case 1
        then obtain n where "n \<ge> 2" "s = r n"
          by (metis r0_min r1_max s One_nat_def Suc_1 bij_betw_iff_bijections bot_nat_0.extremum_unique le_SucE not_less_eq_eq r_bij r_def)
        thus ?thesis
          using Vns Vr_Vn by fastforce
      qed(auto simp: Vr0 Vr1 V0 V1)
    qed
    have compactin_clVr: "compactin X (X closure_of (Vr s))" if s:"s \<in> {0..1} \<inter> \<rat>" for s
    proof -
      consider "0 < s" "s < 1" | "s = 0" | "s = 1"
        using s by fastforce
      then show ?thesis
      proof cases
        case 1
        then obtain n where "n \<ge> 2" "s = r n"
          by (metis r0_min r1_max s One_nat_def Suc_1 bij_betw_iff_bijections bot_nat_0.extremum_unique le_SucE not_less_eq_eq r_bij r_def)
        thus ?thesis
          using Vns Vr_Vn by fastforce
      qed(auto simp: Vr0 Vr1 V0 V1)
    qed
    have Vr_antimono:"X closure_of Vr s \<subseteq> Vr k" if h:"s \<in> {0..1} \<inter> \<rat>" "k \<in> {0..1} \<inter> \<rat>" "k < s" for k s
    proof -
      obtain ns nk where n: "s = r ns" "k = r nk"
        by (metis h(1,2) bij_betw_iff_bijections r_bij)
      show ?thesis
        using Vr_Vn Vns[of "max ns nk"] h by(auto simp: n)
    qed
    define f where "f \<equiv> (\<lambda>x. \<Squnion>s\<in>{0..1} \<inter> \<rat>. s * indicat_real (Vr s) x)" 
    define g where "g \<equiv> (\<lambda>x. \<Sqinter>s\<in>{0..1} \<inter> \<rat>. (1 - s) * indicat_real (X closure_of Vr s) x + s)"
    note [intro!] = bdd_belowI[where m=0] bdd_aboveI[where M=1]
    note [simp] = mult_le_one
    have ne[simp]: "{0..1::real} \<inter> \<rat> \<noteq> {}"
      using Rats_0 atLeastAtMost_iff zero_less_one_class.zero_le_one by blast
      
    have f_lower:"lower_semicontinuous_map X f"
      unfolding f_def
      by(auto intro!: lower_semicontinuous_map_cSup lower_semicontinuous_map_real_cmult indicator_open_lower_semicontinuous_map openin_Vr)
    have g_upper:"upper_semicontinuous_map X g"
      unfolding g_def
      by(auto intro!: upper_semicontinuous_map_cInf upper_semicontinuous_map_real_cmult indicator_closed_upper_semicontinuous_map
                simp: upper_semicontinuous_map_add_c_iff)

    have f_01: "\<And>x. 0 \<le> f x" "\<And>x. f x \<le> 1"
    proof -
      show "\<And>x. 0 \<le> f x"
        unfolding f_def by(subst le_cSup_iff) (auto intro!: bexI[where x=0])
      show "\<And>x. f x \<le> 1"
        unfolding f_def by(subst cSup_le_iff) (auto intro!: bexI[where x=0])
    qed
    have g_01: "\<And>x. 0 \<le> g x" "\<And>x. g x \<le> 1"
    proof -
      show "\<And>x. 0 \<le> g x"
        unfolding g_def by(subst le_cInf_iff) auto
      have "\<And>x. \<forall>y>1. \<exists>a\<in>(\<lambda>s. (1 - s) * indicat_real (X closure_of Vr s) x + s) ` ({0..1} \<inter> \<rat>). a < y"
        by (metis (no_types, lifting) Int_iff Rats_1 add_0 atLeastAtMost_iff cancel_comm_monoid_add_class.diff_cancel image_eqI less_eq_real_def mult_cancel_left1 zero_less_one_class.zero_le_one)
      thus "\<And>x. g x \<le> 1"
        unfolding g_def by(subst cInf_le_iff) auto
    qed

    have disj: "disjnt (X closure_of {x\<in>topspace X. f x \<noteq> 0}) S"
      and f_csupport:"compactin X (X closure_of {x\<in>topspace X. f x \<noteq> 0})"
    proof -
      have 1:"{x\<in>topspace X. f x \<noteq> 0} \<subseteq> X closure_of V0"
      proof -
        have "{x\<in>topspace X. f x \<noteq> 0} = {x\<in>topspace X. f x > 0}"
          using f_01 by (simp add: order_less_le)
        also have "... \<subseteq> X closure_of V0"
        proof safe
          fix x
          assume h:"x \<in> topspace X" "0 < f x"
          then have "\<exists>x\<in>(\<lambda>s. s * indicat_real (Vr s) x) ` ({0..1} \<inter> \<rat>). 0 < x"
            by(intro less_cSup_iff[THEN iffD1]) (auto simp: f_def)
          then obtain s where s: "s \<in> {0..1} \<inter> \<rat>" "s * indicat_real (Vr s) x > 0"
            by fastforce
          hence 1:"s > 0" "0 < indicat_real (Vr s) x"
            by (auto simp add: zero_less_mult_iff)
          hence 2:"x \<in> Vr s"
            by(auto simp: indicator_def)
          have "Vr s \<subseteq> X closure_of Vr s"
            by (meson closure_of_subset openin_Vr openin_subset s(1))
          also have "... \<subseteq> X closure_of V0"
            using Vr_antimono[OF _ _ 1(1)] s(1) by (metis IntI Rats_0 Vr0 atLeastAtMost_iff calculation closure_of_mono order.refl order_trans zero_less_one_class.zero_le_one)
          finally show "x \<in> X closure_of V0"
            using 2 by auto
        qed
        finally show ?thesis .
      qed
      thus "compactin X (X closure_of {x\<in>topspace X. f x \<noteq> 0})"
        by (meson V0(2) closed_compactin closedin_closure_of closure_of_minimal)
      show "disjnt (X closure_of {x\<in>topspace X. f x \<noteq> 0}) S"
        using 1 V0(4) closure_of_mono by(fastforce simp: disjnt_def)
    qed
    have f_1: "f x = 1" if x: "x \<in> T" for x
    proof -
      have xv:"x \<in> V1"
        using V1(3) x by blast
      have "1 \<le> f x"
        unfolding f_def by(subst le_cSup_iff) (auto intro!: bexI[where x=1] simp: Vr1 xv)
      with f_01 show ?thesis
        using nle_le by blast
    qed
    have f_0: "f x = 0" if x: "x \<in> S" for x
    proof -
      have "x \<notin> Vr s" if s: "s \<in> {0..1} \<inter> \<rat>"for s
      proof -
        have "x \<notin> Vr 0"
          using x V0 closure_of_subset[OF openin_subset[of X V0]] by(auto simp: Vr0)
        moreover have "Vr s \<subseteq> Vr 0"
          using Vr_antimono[of s 0] s closure_of_subset[OF openin_subset[OF openin_Vr[OF s]]]
          by(cases "s = 0") auto
        ultimately show ?thesis
          by blast
      qed
      hence "f x \<le> 0"
        unfolding f_def by(subst cSup_le_iff) auto
      with f_01 show ?thesis
        using nle_le by blast
    qed
    have fg:"f x = g x" if x: "x \<in> topspace X" for x
    proof -
      have "\<not> f x < g x"
      proof
        assume "f x < g x"
        then obtain r s where rs: "r \<in> \<rat>" "s \<in> \<rat>" "f x < r" "r < s" "s < g x"
          by (meson Rats_dense_in_real)
        hence r:"r \<in> {0..1} \<inter> \<rat>"
          using f_01 g_01 by (metis IntI atLeastAtMost_iff inf.orderE inf.strict_coboundedI2 linorder_not_less nle_le)
        hence s:"s \<in> {0..1} \<inter> \<rat>"
          using g_01 rs by (metis IntI atLeastAtMost_iff f_01(1) inf.strict_coboundedI2 inf.strict_order_iff less_eq_real_def)
        have x1:"x \<notin> Vr r"
        proof -
          have "r * indicat_real (Vr r) x < r"
            using r by(auto intro!: cSUP_lessD[OF _ rs(3)[simplified f_def]])
          thus ?thesis
            using r by auto
        qed
        have x2:"x \<in> X closure_of Vr s"
        proof -
          have 1:"s < (1 - s) * indicat_real (X closure_of Vr s) x + s"
            using s by(intro less_cINF_D[OF _ rs(5)[simplified g_def]]) auto
          show ?thesis
            by(rule ccontr) (use s 1 in auto)
        qed
        show False
          using x1 x2 Vr_antimono[OF s r rs(4)] by blast
      qed
      moreover have "f x \<le> g x"
      proof -
        have "l * indicat_real (Vr l) x \<le> (1 - s) * indicat_real (X closure_of Vr s) x + s"
          if ls: "l \<in> {0..1} \<inter> \<rat>" "s \<in> {0..1} \<inter> \<rat>" for l s
        proof(rule ccontr)
          assume h:"\<not> l * indicat_real (Vr l) x \<le> (1 - s) * indicat_real (X closure_of Vr s) x + s"
          then have "l * indicat_real (Vr l) x > (1 - s) * indicat_real (X closure_of Vr s) x + s"
            by auto
          hence "l > s \<and> x \<in> Vr l \<and> x \<notin> Vr s"
            using ls by (metis (no_types, opaque_lifting) h Int_iff add.commute add.right_neutral atLeastAtMost_iff closure_of_subset diff_add_cancel in_mono indicator_simps(1) indicator_simps(2) mult.commute mult_1 mult_zero_left openin_Vr openin_subset zero_less_one_class.zero_le_one)
          moreover have "Vr l \<subseteq> Vr s"
            using Vr_antimono[OF ls] by (meson calculation closure_of_subset ls(1) openin_Vr openin_subset order_trans)
          ultimately show False
            by blast
        qed
        thus "f x \<le> g x"
          unfolding f_def g_def by(auto intro!: cSup_le_iff[THEN iffD2] le_cInf_iff[THEN iffD2])
      qed
      ultimately show ?thesis
        by simp
    qed
    show ?thesis
    proof(safe intro!: exI[where x=f])
      have "continuous_map X euclideanreal f"
        by (simp add: fg f_lower g_upper upper_lower_semicontinuous_map_iff_continuous_map upper_semicontinuous_map_cong)
      thus "continuous_map X (top_of_set {0..1}) f"
        using f_01 by(auto simp: continuous_map_in_subtopology)
    qed(use f_0 f_1 f_csupport disj in auto)
  qed
  then obtain f where f: "continuous_map X (top_of_set {0..1}) f" "f ` S \<subseteq> {0::real}" "f ` T \<subseteq> {1}"
    "disjnt (X closure_of {x\<in>topspace X. f x \<noteq> 0}) S" "compactin X (X closure_of {x \<in> topspace X. f x \<noteq> 0})"
    by blast
  define g where "g \<equiv> (\<lambda>x. (b - a) * f x + a)"
  have "continuous_map X (top_of_set {a..b}) g"
  proof -
    have [simp]:"0 \<le> y \<and> y \<le> 1 \<Longrightarrow> (b - a) * y + a \<le> b" for y
      using assms(3) by (meson diff_ge_0_iff_ge le_diff_eq mult_left_le)
    show ?thesis
      using f(1) assms(3) by(auto simp: image_subset_iff continuous_map_in_subtopology g_def
                                intro!: continuous_map_add continuous_map_real_mult_left)
  qed  
  moreover have "g ` S \<subseteq> {a}" "g ` T \<subseteq> {b}"
    using f(2,3) by(auto simp: g_def)
  moreover have "disjnt (X closure_of {x\<in>topspace X. g x \<noteq> a}) S"
                "compactin X (X closure_of {x \<in> topspace X. g x \<noteq> a})"
  proof -
    consider "a = b" | "a < b"
      using assms by fastforce
    then have "disjnt (X closure_of {x\<in>topspace X. g x \<noteq> a}) S \<and> compactin X (X closure_of {x \<in> topspace X. g x \<noteq> a})"
    proof cases
      case 1
      then have [simp]:"{x \<in> topspace X. g x \<noteq> a} = {}"
        by(auto simp: g_def)
      thus ?thesis
        by simp_all
    next
      case 2
      then have "{x \<in> topspace X. g x \<noteq> a} = {x \<in> topspace X. f x \<noteq> 0}"
        by(auto simp: g_def)
      thus ?thesis
        by(simp add: f)
    qed
    thus "disjnt (X closure_of {x\<in>topspace X. g x \<noteq> a}) S" "compactin X (X closure_of {x \<in> topspace X. g x \<noteq> a})"
      by simp_all
  qed
  ultimately show ?thesis
    using that by auto
qed

end