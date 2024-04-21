(*  Title:   Abstract_Metrizable_Topology.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>Abstract Polish Spaces \<close>
theory Abstract_Metrizable_Topology
  imports "Set_Based_Metric_Product"
begin

subsection \<open> Polish Spaces \<close>
definition "Polish_space X \<equiv> completely_metrizable_space X \<and> separable_space X"

lemma(in Metric_space) Polish_space_mtopology:
  assumes mcomplete "separable_space mtopology"
  shows "Polish_space mtopology"
  by (simp add: assms completely_metrizable_space_mtopology Polish_space_def)

lemma
  assumes "Polish_space X"
  shows Polish_space_imp_completely_metrizable_space: "completely_metrizable_space X"
    and Polish_space_imp_metrizable_space: "metrizable_space X"
    and Polish_space_imp_second_countable: "second_countable X"
    and Polish_space_imp_separable_space: "separable_space X"
  using assms by(auto simp: completely_metrizable_imp_metrizable_space Polish_space_def  metrizable_space_separable_iff_second_countable)

lemma Polish_space_closedin:
  assumes "Polish_space X" "closedin X A"
  shows "Polish_space (subtopology X A)"
  using assms by(auto simp: completely_metrizable_imp_metrizable_space Polish_space_def completely_metrizable_space_closedin second_countable_subtopology metrizable_space_separable_iff_second_countable)

lemma Polish_space_gdelta_in:
  assumes "Polish_space X" "gdelta_in X A"
  shows "Polish_space (subtopology X A)"
  using assms by(auto simp: completely_metrizable_imp_metrizable_space Polish_space_def completely_metrizable_space_gdelta_in second_countable_subtopology metrizable_space_separable_iff_second_countable)

corollary Polish_space_openin:
  assumes "Polish_space X" "openin X A"
  shows "Polish_space (subtopology X A)"
  by (simp add: open_imp_gdelta_in assms Polish_space_gdelta_in)

lemma homeomorphic_Polish_space_aux:
  assumes "Polish_space X" "X homeomorphic_space Y"
  shows "Polish_space Y"
  using assms by(simp add: homeomorphic_completely_metrizable_space_aux homeomorphic_separable_space Polish_space_def)

corollary homeomorphic_Polish_space:
  assumes "X homeomorphic_space Y"
  shows "Polish_space X \<longleftrightarrow> Polish_space Y"
  by (meson assms homeomorphic_Polish_space_aux homeomorphic_space_sym)

lemma Polish_space_euclidean[simp]: "Polish_space (euclidean :: ('a :: polish_space) topology)"
  by (simp add: completely_metrizable_space_euclidean Polish_space_def second_countable_imp_separable_space)

lemma Polish_space_countable[simp]:
  "Polish_space (euclidean :: 'a :: {countable,discrete_topology} topology)"
proof -
  interpret discrete_metric "UNIV :: 'a set" .
  have [simp]:"euclidean = disc.mtopology"
    by (metis discrete_topology_class.open_discrete discrete_topology_unique istopology_open mtopology_discrete_metric topology_inverse' topspace_euclidean)
  show ?thesis
    by(auto simp: Polish_space_def intro!: disc.completely_metrizable_space_mtopology mcomplete_discrete_metric countable_space_separable_space)
qed

lemma Polish_space_discrete_topology: "Polish_space (discrete_topology I) \<longleftrightarrow> countable I"
  by (simp add: completely_metrizable_space_discrete_topology Polish_space_def separable_space_discrete_topology)

lemma Polish_space_prod:
  assumes "Polish_space X" and "Polish_space Y"
  shows "Polish_space (prod_topology X Y)"
  using assms by (simp add: completely_metrizable_space_prod_topology Polish_space_def separable_space_prod) 

lemma Polish_space_product:
  assumes "countable I" and "\<And>i. i \<in> I \<Longrightarrow> Polish_space (S i)"
  shows "Polish_space (product_topology S I)"
  using assms by(auto simp: separable_countable_product Polish_space_def completely_metrizable_space_product_topology)

lemma(in Product_metric) Polish_spaceI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> separable_space (Metric_space.mtopology (Mi i) (di i))"
      and "\<And>i. i \<in> I \<Longrightarrow> Metric_space.mcomplete (Mi i) (di i)"
  shows "Polish_space Product_metric.mtopology"
  using assms I by(auto simp: Polish_space_def Product_metric_mtopology_eq[symmetric] completely_metrizable_space_product_topology intro!: separable_countable_product Metric_space.completely_metrizable_space_mtopology Md_metric)

lemma(in Sum_metric) Polish_spaceI:
  assumes "countable I"
      and "\<And>i. i \<in> I \<Longrightarrow> separable_space (Metric_space.mtopology (Mi i) (di i))"
      and "\<And>i. i \<in> I \<Longrightarrow> Metric_space.mcomplete (Mi i) (di i)"
    shows "Polish_space Sum_metric.mtopology"
  by(auto simp: Polish_space_def intro!: separable_Mi_separable_M assms mcomplete_Mi_mcomplete_M Sum_metric.completely_metrizable_space_mtopology)

lemma compact_metrizable_imp_Polish_space:
  assumes "metrizable_space X" "compact_space X"
  shows "Polish_space X"
proof -
  obtain d where "Metric_space (topspace X) d" "Metric_space.mtopology (topspace X) d = X"
    by (metis assms(1) Metric_space.topspace_mtopology metrizable_space_def)
  thus ?thesis
    by (metis Metric_space.compact_space_imp_separable assms(1) assms(2) compact_imp_locally_compact_space locally_compact_imp_completely_metrizable_space Polish_space_def)
qed

subsection \<open> Extended Reals and Non-Negative Extended Reals \<close>
lemma Polish_space_ereal:"Polish_space (euclidean :: ereal topology)"
proof(rule homeomorphic_Polish_space_aux)
  show "Polish_space (subtopology euclideanreal {-1..1})"
    by (auto intro!: Polish_space_closedin)
next
  define f :: "real \<Rightarrow> ereal"
    where "f \<equiv> (\<lambda>r. if r = - 1 then - \<infinity> else if r = 1 then \<infinity> else if r \<le> 0 then ereal (1 - (1 / (1 + r))) else ereal ((1 / (1 - r)) - 1))"
  define g :: "ereal \<Rightarrow> real"
    where "g \<equiv> (\<lambda>r. if r \<le> 0 then real_of_ereal (inverse (1 - r)) - 1 else 1 - real_of_ereal (inverse (1 + r)))"
  show "top_of_set {-1..1::real} homeomorphic_space (euclidean :: ereal topology)"
    unfolding homeomorphic_space_def homeomorphic_maps_def continuous_map_iff_continuous
  proof(safe intro!: exI[where x=f] exI[where x=g])
    show "continuous_on {- 1..1} f"
      unfolding continuous_on_eq_continuous_within
    proof safe
      fix x :: real
      assume "x \<in> {- 1..1}"
      then consider "x = -1" | "-1 < x" "x < 0" | "x = 0" | "0 < x" "x < 1" | "x = 1"
        by fastforce
      then show "continuous (at x within {- 1..1}) f"
      proof cases
        show "- 1 < x \<Longrightarrow> x < 0 \<Longrightarrow> ?thesis"
          by(simp add: at_within_Icc_at, intro isCont_cong[where f="\<lambda>r. ereal (1 - (1 / (1 + r)))" and g=f,THEN iffD1,OF _ continuous_on_interior[of "{-1<..<0}"]]) (auto simp: at_within_Icc_at eventually_nhds f_def intro!: exI[where x="{-1<..<0}"] continuous_on_divide continuous_on_ereal continuous_on_diff continuous_on_add)
      next
        have *:"isCont (\<lambda>r. if r \<le> 0 then ereal (1 - (1 / (1 + r))) else ereal ((1 / (1 - r)) - 1)) 0"
          by(rule isCont_If_ge) (auto simp add: continuous_within intro!: continuous_on_Icc_at_leftD[where a="- (1 / 2)" and b=0 and f="\<lambda>r::real. 1 - (1 / (1 + r))",simplified] continuous_on_Icc_at_rightD[where a=0 and b="1 / 2" and f="\<lambda>r::real. (1 / (1 - r)) - 1",simplified] continuous_on_diff continuous_on_divide continuous_on_add)
        show ?thesis if x:"x = 0"
          unfolding x at_within_Icc_at[of "- 1 :: real" 0 1,simplified]
          by(rule isCont_cong[THEN iffD1,OF _ *]) (auto simp: eventually_nhds f_def intro!: exI[where x="{-1 / 2<..<1/2}"])
      next
        show "0 < x \<Longrightarrow> x < 1 \<Longrightarrow> ?thesis"
          by(simp add: at_within_Icc_at, intro isCont_cong[where f="\<lambda>r. ereal ((1 / (1 - r)) - 1)" and g=f,THEN iffD1,OF _ continuous_on_interior[of "{0<..<1}"]]) (auto simp: at_within_Icc_at eventually_nhds f_def intro!: exI[where x="{0<..<1}"] continuous_on_divide continuous_on_ereal continuous_on_diff continuous_on_add)
      next
        show ?thesis if x:"x = -1"
          unfolding x at_within_Icc_at_right[where a="- 1 :: real" and b=1,simplified] continuous_within ereal_tendsto_simps(2)[symmetric]
        proof(subst tendsto_cong)
          show "\<forall>\<^sub>F r in at_right (ereal (- 1)). (f \<circ> real_of_ereal) r = 1 - (1 / (1 + r))"
            unfolding eventually_at_right[of "ereal (- 1)" 0,simplified]
          proof(safe intro!: exI[where x="ereal (- 1 / 2)"])
            fix y
            assume "ereal (- 1) < y" "y < ereal (- 1 / 2)"
            then obtain y' where y':"y = ereal y'" "- 1 < y'" "y' < - 1 / 2"
              by (metis ereal_real' less_ereal.simps(1) not_inftyI)
            show "(f \<circ> real_of_ereal) y = 1 - 1 / (1 + y)"
              using y'(2,3) by(auto simp add: y'(1) f_def one_ereal_def)
          qed simp
        next
          have "((\<lambda>r. 1 - 1 / (1 + r)) \<longlongrightarrow> - \<infinity>) (at_right (ereal (- 1)))"
            unfolding tendsto_MInfty
          proof safe
            fix r :: real
            consider "r \<ge> 1" | "r < 1"
              by argo
            then show "\<forall>\<^sub>F x in at_right (ereal (- 1)). 1 - 1 / (1 + x) < ereal r"
            proof cases
              case [arith]:1
              show ?thesis
                unfolding eventually_at_right[of "ereal (- 1)" 0,simplified]
              proof(safe intro!: exI[where x=0])
                fix y
                assume "ereal (- 1) < y" "y < 0"
                then obtain y' where y':"y = ereal y'" "- 1 < y'" "y' < 0"
                  using not_inftyI by force
                then have *:"1 - 1 / (1 + y) < 1"
                  by (simp add: one_ereal_def)
                show "1 - 1 / (1 + y) < ereal r"
                  by(rule order.strict_trans2[OF *]) (use 1 in auto)
              qed simp
            next
              case 2
              show ?thesis
                unfolding eventually_at_right[of "ereal (- 1)" 0,simplified]
              proof(safe intro!: exI[where x="ereal (1 / (1 - r) - 1)"])
                fix y
                assume " ereal (- 1) < y" "y < ereal (1 / (1 - r) - 1)"
                then obtain y' where y':"y = ereal y'" "- 1 < y'" "y' < 1 / (1 - r) - 1"
                  by (metis ereal_less_eq(3) ereal_real' linorder_not_le not_inftyI)
                have "1 - 1 / (1 + y) = ereal (1 - 1 / (1 + y'))"
                  by (metis ereal_divide ereal_minus(1) one_ereal_def order_less_irrefl plus_ereal.simps(1) real_0_less_add_iff y'(1) y'(2))
                also have "... < ereal r"
                proof -
                  have "1 + y' < 1 / (1 - r)"
                    using y' by simp
                  hence "1 - r < 1 / (1 + y')"
                    using y' 2 by (simp add: less_divide_eq mult.commute)
                  thus ?thesis
                    by simp
                qed
                finally show "1 - 1 / (1 + y) < ereal r" .
              qed(use 2 in auto)
            qed
          qed
          thus "((\<lambda>r. 1 - 1 / (1 + r)) \<longlongrightarrow> f (- 1)) (at_right (ereal (- 1)))"
            by(simp add: f_def)
        qed
      next
        show ?thesis if x:"x = 1"
          unfolding x at_within_Icc_at_left[where a="- 1 :: real" and b=1,simplified] continuous_within ereal_tendsto_simps(1)[symmetric]
        proof(subst tendsto_cong)
          show "\<forall>\<^sub>F r in at_left (ereal 1). (f \<circ> real_of_ereal) r = (1 / (1 - r)) - 1"
            unfolding eventually_at_left[of 0 "ereal 1",simplified]
          proof(safe intro!: exI[where x="ereal (1 / 2)"])
            fix y
            assume "ereal (1 / 2) < y" "y < ereal 1"
            then obtain y' where y':"y = ereal y'" "1 / 2 < y'" "y' < 1"
              using ereal_less_ereal_Ex by force
            show "(f \<circ> real_of_ereal) y = 1 / (1 - y) - 1"
              using y'(2,3) by(auto simp add: y'(1) f_def one_ereal_def)
          qed simp
        next
          have "((\<lambda>r. (1 / (1 - r)) - 1) \<longlongrightarrow> \<infinity>) (at_left (ereal 1))"
            unfolding tendsto_PInfty
          proof safe
            fix r :: real
            consider "r \<le> - 1" | "- 1 < r"
              by argo
            then show "\<forall>\<^sub>F x in at_left (ereal 1). (1 / (1 - x)) - 1 > ereal r"
            proof cases
              case [arith]:1
              show ?thesis
                unfolding eventually_at_left[of 0 "ereal 1",simplified]
              proof(safe intro!: exI[where x=0])
                fix y
                assume "0 < y" "y < ereal 1"
                then obtain y' where y':"y = ereal y'" "0 < y'" "y' < 1"
                  using not_inftyI by force
                then have *:"(1 / (1 - y)) - 1 > ereal (- 1)"
                  by (simp add: one_ereal_def)
                show "ereal r < 1 / (1 - y) - 1"
                  by(rule order.strict_trans1[OF _ *]) (use 1 in auto)
              qed simp
            next
              case 2
              show ?thesis
                unfolding eventually_at_left[of 0 "ereal 1",simplified]
              proof(safe intro!: exI[where x="ereal (1 - 1 / (1 + r))"])
                fix y
                assume "ereal (1 - 1 / (1 + r)) < y" "y < ereal 1"
                then obtain y' where y':"y = ereal y'" "1 - 1 / (1 + r) < y'" "y' < 1"
                  by (metis ereal_less_eq(3) ereal_real' linorder_not_le not_inftyI)
                have "ereal r < ereal (1 / (1 - y') - 1)"
                proof -
                  have "1 - y' < 1 / (r + 1)"
                    using y'(2) by argo
                  hence "r + 1 < 1 / (1 - y')"
                    using y' 2 by (simp add: less_divide_eq mult.commute)
                  thus ?thesis
                    by simp
                qed
                also have "... = 1 / (1 - y) - 1"
                  by (metis diff_gt_0_iff_gt ereal_divide ereal_minus(1) less_numeral_extra(3) one_ereal_def y'(1) y'(3))
                finally show "ereal r < 1 / (1 - y) - 1" .
              qed(use 2 in auto)
            qed
          qed
          thus " ((\<lambda>r. 1 / (1 - r) - 1) \<longlongrightarrow> f 1) (at_left (ereal 1))"
            by(simp add: f_def)
        qed
      qed
    qed
  next
    show "continuous_map euclidean (top_of_set {- 1..1}) g"
    proof(safe intro!: continuous_map_into_subtopology)
      show "continuous_map euclidean euclideanreal g"
        unfolding Abstract_Topology.continuous_map_iff_continuous2 continuous_on_eq_continuous_within
      proof safe
        fix x :: ereal
        consider "x = - \<infinity>" | "- \<infinity> < x" "x < 0" | "x = 0" | "0 < x" "x < \<infinity>" | "x = \<infinity>"
          by fastforce
        then show "isCont g x"
        proof cases
          assume x:"- \<infinity> < x" "x < 0"
          then obtain x' where x':"x = ereal x'" "x' < 0"
            by (metis ereal_infty_less(2) ereal_less_ereal_Ex zero_ereal_def)
          show ?thesis
          proof(subst isCont_cong)
            have [simp]:"isCont ((-) 1) x"
            proof -
              have *:"isCont (\<lambda>x. ereal (real_of_ereal 1 - real_of_ereal x)) x"
                using x' by(auto simp add: continuous_at_iff_ereal[symmetric,simplified comp_def] intro!: continuous_diff continuous_at_of_ereal)
              have **: "ereal (x' - 1) < x \<Longrightarrow> x < 0 \<Longrightarrow> ereal (1 - real_of_ereal x) = ereal 1 - x" for x
                by (metis ereal_minus(1) less_ereal.simps(2) less_ereal.simps(3) real_of_ereal.elims)
              show ?thesis
                apply(rule isCont_cong[THEN iffD1,OF _ *])
                using x'(2) ** by(auto simp: eventually_nhds x'(1) one_ereal_def intro!: exI[where x="{x-1<..<0}"])
            qed
            have *:"abs (1 - x) \<noteq> \<infinity>" " 1 - x \<noteq> 0"
              using x'(2) by(auto simp add: x'(1) one_ereal_def)
            show "isCont (\<lambda>r. real_of_ereal (inverse (1 - r)) - 1) x"
              using x * by(auto intro!: continuous_diff continuous_divide isCont_o2[OF _ continuous_at_of_ereal])
          next
            show "\<forall>\<^sub>F x in nhds x. g x = real_of_ereal (inverse (1 - x)) - 1"
              using x(2) by(auto simp: eventually_nhds x'(1) g_def one_ereal_def intro!: exI[where x="{x-1<..<0}"])
          qed
        next
          assume x:"\<infinity> > x" "x > 0"
          then obtain x' where x':"x = ereal x'" "x' > 0"
            by (metis ereal_less(2) less_ereal.elims(2) less_ereal.simps(2))
          show ?thesis
          proof(subst isCont_cong)
            have [simp]: "isCont ((+) 1) x"
            proof -
              have *:"isCont (\<lambda>x. ereal (real_of_ereal 1 + real_of_ereal x)) x"
                using x' by(auto simp add: continuous_at_iff_ereal[symmetric,simplified comp_def] intro!: continuous_add continuous_at_of_ereal)
              have **: " 0 < x \<Longrightarrow> x < ereal (x' + 1) \<Longrightarrow> ereal (1 + real_of_ereal x) = ereal 1 + x" for x
                using ereal_less_ereal_Ex by auto
              show ?thesis
                apply(rule isCont_cong[THEN iffD1,OF _ *])
                using x'(2) ** by(auto simp: eventually_nhds x'(1) one_ereal_def intro!: exI[where x="{0<..<x + 1}"])
            qed
            have "real_of_ereal (1 + x) \<noteq> 0"
              using x' by auto
            thus "isCont (\<lambda>r. 1 - real_of_ereal (inverse (1 + r))) x"
              using x by(auto intro!: continuous_diff continuous_divide isCont_o2[OF _ continuous_at_of_ereal])
          next
            show "\<forall>\<^sub>F x in nhds x. g x = 1 - real_of_ereal (inverse (1 + x))"
              using x(2) by(auto simp: eventually_nhds x'(1) g_def one_ereal_def intro!: exI[where x="{0<..<x+1}"])
          qed
        next
          show "isCont g x" if x:"x = - \<infinity>"
            unfolding x
          proof(safe intro!: continuous_at_sequentiallyI)
            fix u :: "nat \<Rightarrow> ereal"
            assume u:"u \<longlonglongrightarrow> - \<infinity>"
            show "(\<lambda>n. g (u n)) \<longlonglongrightarrow> g (- \<infinity>)"
              unfolding LIMSEQ_def
            proof safe
              fix r :: real
              assume r[arith]: "r > 0"
              obtain no where no: "\<And>n. n \<ge> no \<Longrightarrow> u n < ereal (min (1 - 1 / r) 0)"
                using u unfolding tendsto_MInfty eventually_sequentially by blast
              show "\<exists>no. \<forall>n\<ge>no. dist (g (u n)) (g (- \<infinity>)) < r"
              proof(safe intro!: exI[where x=no])
                fix n
                assume n:"n \<ge> no"
                have r0:"1 - min (ereal (1 - 1 / r)) (ereal 0) > 0"
                  by (simp add: ereal_diff_gr0 min.strict_coboundedI2)
                have u1:"1 - u n > 0"
                  by (metis ereal_0_less_1 ereal_diff_gr0 ereal_min linorder_not_le min.strict_coboundedI2 n no order_le_less_trans order_less_not_sym zero_ereal_def)
                have "real_of_ereal (inverse (1 - u n)) < r"
                proof -
                  have "real_of_ereal (inverse (1 - u n)) < real_of_ereal (inverse (1 -  ereal (min (1 - 1 / r) 0)))"
                  proof(safe intro!: ereal_less_real_iff[THEN iffD2])
                    have "ereal (real_of_ereal (inverse (1 - u n))) = inverse (1 - u n)"
                      by(rule ereal_real') (use no[OF n] u1 in auto)
                    also have "... < inverse (1 - ereal (min (1 - 1 / r) 0))"
                      apply(rule ereal_inverse_antimono_strict)
                      using no[OF n] apply(simp add: ereal_diff_positive min.coboundedI2)
                      by (metis (no_types, lifting) no[OF n] ereal_add_uminus_conv_diff ereal_eq_minus_iff ereal_less_minus_iff ereal_minus_less_minus ereal_times(1) ereal_times(3))
                    finally show "ereal (real_of_ereal (inverse (1 - u n))) < inverse (1 - ereal (min (1 - 1 / r) 0))" .
                  qed(use r0 in auto)
                  also have "... \<le> r"
                    by(cases "r \<ge> 1") (auto simp add: real_of_ereal_minus)
                  finally show "real_of_ereal (inverse (1 - u n)) < r" .
                qed
                thus "dist (g (u n)) (g (- \<infinity>)) < r"
                  using u1 no[OF n] by(auto simp: g_def zero_ereal_def dist_real_def)
              qed
            qed
          qed
        next
          show "isCont g x" if x:"x = \<infinity>"
            unfolding x
          proof(safe intro!: continuous_at_sequentiallyI)
            fix u :: "nat \<Rightarrow> ereal"
            assume u:"u \<longlonglongrightarrow> \<infinity>"
            show "(\<lambda>n. g (u n)) \<longlonglongrightarrow> g \<infinity>"
              unfolding LIMSEQ_def
            proof safe
              fix r :: real
              assume r[arith]: "r > 0"
              obtain no where no: "\<And>n. n \<ge> no \<Longrightarrow> u n > ereal (max (1 / r - 1) 0)"
                using u unfolding tendsto_PInfty eventually_sequentially by blast 
              show "\<exists>no. \<forall>n\<ge>no. dist (g (u n)) (g \<infinity>) < r"
              proof(safe intro!: exI[where x=no])
                fix n
                assume n:"n \<ge> no"
                have u0: "1 + u n > 0"
                  using no[OF n] by simp (metis add_nonneg_pos zero_ereal_def zero_less_one_ereal)
                have "\<bar>- real_of_ereal (inverse (1 + u n))\<bar> < r"
                proof -
                  have "\<bar>- real_of_ereal (inverse (1 + u n))\<bar> < \<bar>- (inverse (1 + max (1 / r - 1) 0))\<bar>"
                    unfolding abs_real_of_ereal abs_minus
                  proof(safe intro!: real_less_ereal_iff[THEN iffD2])
                    have "\<bar>inverse (1 + u n)\<bar> < inverse (1 + ereal (max (1 / r - 1) 0))"
                      using no[OF n] u0 by (simp add: ereal_add_strict_mono ereal_inverse_antimono_strict inverse_ereal_ge0I le_max_iff_disj order_less_imp_le u0)
                    also have "... = ereal \<bar>inverse (1 + max (1 / r - 1) 0)\<bar>"
                      by(auto simp: abs_ereal.simps(1)[symmetric] ereal_max[symmetric] simp del: abs_ereal.simps(1) ereal_max)
                    finally show "\<bar>inverse (1 + u n)\<bar> < ereal \<bar>inverse (1 + max (1 / r - 1) 0)\<bar>" .
                  qed auto
                  also have "... = inverse (1 + max (1 / r - 1) 0)"
                    by auto
                  also have "... \<le> r"
                    by(cases "r \<le> 1") auto
                  finally show ?thesis .
                qed
                thus "dist (g (u n)) (g \<infinity>) < r"
                  using no[OF n] by(auto simp: g_def dist_real_def zero_ereal_def)
              qed
            qed
          qed
        next
          show "isCont g x" if x:"x = 0"
            unfolding x g_def
          proof(safe intro!: isCont_If_ge)
            have "((\<lambda>x. real_of_ereal (1 - x)) \<longlongrightarrow> 1) (at_left 0)"
            proof(subst tendsto_cong)
              show "((\<lambda>x. 1 - real_of_ereal x) \<longlongrightarrow> 1) (at_left 0)"
                by(auto intro!: tendsto_diff[where a=1 and b=0,simplified] simp: zero_ereal_def)
            next
              show "\<forall>\<^sub>F x in at_left 0. real_of_ereal (1 - x) = 1 - real_of_ereal x"
                by(auto simp: eventually_at_left[where y="- 1" and x="0::ereal",simplified] real_of_ereal_minus ereal_uminus_eq_reorder  intro!: exI[where x="-1"])
            qed
            thus "continuous (at_left 0) (\<lambda>x. real_of_ereal (inverse (1 - x)) - 1)"
              unfolding continuous_within
              by (auto intro!: tendsto_diff[where a = 1 and b=1,simplified] tendsto_divide[where a=1 and b=1,simplified])
          next
            have "((\<lambda>x. real_of_ereal (1 + x)) \<longlongrightarrow> 1) (at_right 0)"
            proof(subst tendsto_cong)
              show "((\<lambda>x. 1 + real_of_ereal x) \<longlongrightarrow> 1) (at_right 0)"
                by(auto intro!: tendsto_add[where a=1 and b=0,simplified] simp: zero_ereal_def)
            next
              show "\<forall>\<^sub>F x in at_right 0. real_of_ereal (1 + x) = 1 + real_of_ereal x"
                by(auto simp: eventually_at_right[where y=1 and x="0::ereal",simplified] real_of_ereal_add ereal_uminus_eq_reorder  intro!: exI[where x=1])
            qed
            thus "((\<lambda>x. 1 - real_of_ereal (inverse (1 + x))) \<longlongrightarrow> real_of_ereal (inverse (1 - 0)) - 1) (at_right 0)"
              by (auto intro!: tendsto_diff[where a = 1 and b=1,simplified] tendsto_divide[where a=1 and b=1,simplified])
          qed
        qed
      qed
    next
      fix x :: ereal
      consider "x = - \<infinity>" | "- \<infinity> < x" "x \<le> 0" | "0 < x" "x < \<infinity>" | "x = \<infinity>"
        by fastforce
      then show "g x \<in> {- 1..1}"
      proof cases
        assume "- \<infinity> < x" "x \<le> 0"
        then obtain x' where "x = ereal x'" "x' \<le> 0"
          by (metis dual_order.refl ereal_less_ereal_Ex order_less_le zero_ereal_def)
        then show ?thesis
          by(auto simp: g_def real_of_ereal_minus intro!: pos_divide_le_eq[THEN iffD2])
      next
        assume "0 < x" "x < \<infinity>"
        then obtain x' where "x = ereal x'" "x' > 0"
          by (metis ereal_less(2) less_ereal.elims(2) order_less_le)
        then show ?thesis
          by(auto simp: g_def real_of_ereal_add inverse_eq_divide intro!: pos_divide_le_eq[THEN iffD2])
      qed(auto simp: g_def)
    qed
  next
    fix x :: ereal
    consider "x = - \<infinity>" | "- \<infinity> < x" "x \<le> 0" | "0 < x" "x < \<infinity>" | "x = \<infinity>"
      by fastforce
    then show "f (g x) = x"
    proof cases
      assume "- \<infinity> < x" "x \<le> 0"
      then obtain x' where x':"x = ereal x'" "x' \<le> 0"
        by (metis dual_order.refl ereal_less_ereal_Ex order_less_le zero_ereal_def)
      then have [arith]:"1 / (1 - x') - 1 \<le> 0"
        by simp
      show ?thesis
        using x' by(auto simp: g_def real_of_ereal_minus f_def)
    next
      assume "0 < x" "x < \<infinity>"
      then obtain x' where x':"x = ereal x'" "x' > 0"
        by (metis ereal_less(2) less_ereal.elims(2) order_less_le)
      hence [arith]: "1 - 1 / (x' + 1) \<ge> 0"
        by simp
      show ?thesis
        using x' by(simp add: g_def inverse_eq_divide f_def)
    qed(auto simp: f_def g_def)
  next
    fix x :: real
    assume "x \<in> topspace (top_of_set {- 1..1})"
    then consider "x = - 1" | "- 1 < x" "x \<le> 0" | "0 < x" "x < 1" | "x = 1"
      by fastforce
    then show "g (f x) = x"
      by cases (auto simp: f_def g_def real_of_ereal_minus real_of_ereal_add)
  qed
qed

corollary Polish_space_ennreal:"Polish_space (euclidean :: ennreal topology)"
proof(rule homeomorphic_Polish_space_aux)
  show "Polish_space (top_of_set {0::ereal..})"
    using Polish_space_closedin Polish_space_ereal by fastforce
next
  show "top_of_set {0::ereal..} homeomorphic_space (euclidean :: ennreal topology)"
    by(auto intro!: exI[where x=e2ennreal] exI[where x=enn2ereal] simp: homeomorphic_space_def homeomorphic_maps_def enn2ereal_e2ennreal continuous_on_e2ennreal continuous_map_in_subtopology continuous_on_enn2ereal image_subset_iff)
qed

subsection \<open>Continuous Embddings\<close>
abbreviation Hilbert_cube_topology :: "(nat \<Rightarrow> real) topology" where
"Hilbert_cube_topology \<equiv> (product_topology (\<lambda>n. top_of_set {0..1}) UNIV)"

lemma topspace_Hilbert_cube: "topspace Hilbert_cube_topology = (\<Pi>\<^sub>E x\<in>UNIV. {0..1})"
  by simp

lemma Polish_space_Hilbert_cube: "Polish_space Hilbert_cube_topology"
  by(auto intro!: Polish_space_closedin Polish_space_product)

abbreviation Cantor_space_topology :: "(nat \<Rightarrow> real) topology" where
"Cantor_space_topology \<equiv> (product_topology (\<lambda>n. top_of_set {0,1}) UNIV)"

lemma topspace_Cantor_space:
 "topspace Cantor_space_topology = (\<Pi>\<^sub>E x\<in>UNIV. {0,1})"
  by simp

lemma Polish_space_Cantor_space: "Polish_space Cantor_space_topology"
  by(auto intro!: Polish_space_closedin Polish_space_product)

corollary completely_metrizable_space_homeo_image_gdelta_in:
  assumes "completely_metrizable_space X" "completely_metrizable_space Y" "B \<subseteq> topspace Y" "X homeomorphic_space subtopology Y B"
  shows "gdelta_in Y B"
  using assms completely_metrizable_space_eq_gdelta_in homeomorphic_completely_metrizable_space by blast

subsubsection \<open> Embedding into Hilbert Cube\<close>
lemma embedding_into_Hilbert_cube:
  assumes "metrizable_space X" "separable_space X"
  shows "\<exists>A \<subseteq> topspace Hilbert_cube_topology. X homeomorphic_space (subtopology Hilbert_cube_topology A)"
proof -
  consider "X = trivial_topology" | "topspace X \<noteq> {}" by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by(auto intro!: exI[where x="{}"] simp: homeomorphic_empty_space_eq)
  next
    case S_ne:2
    then obtain U where U:"countable U" "dense_in X U" "U \<noteq> {}"
      using assms(2) by(auto simp: separable_space_def2 dense_in_nonempty)
    obtain xn where xn:"\<And>n::nat. xn n \<in> U" "U = range xn"
      by (metis U(1) U(3) from_nat_into range_from_nat_into)
    then have xns:"xn n \<in> topspace X" for n
      using dense_in_subset[OF U(2)] by auto
    obtain d' where d':"Metric_space (topspace X) d'" "Metric_space.mtopology (topspace X) d' = X"
      by (metis Metric_space.topspace_mtopology assms(1) metrizable_space_def)
    interpret ms': Metric_space "topspace X" d' by fact
    define d where "d = ms'.capped_dist (1/2)"
    have d: "Metric_space.mtopology (topspace X) d = X" "\<And>x y. d x y < 1"
      by(simp add: d_def ms'.mtopology_capped_metric d') (simp add: d_def ms'.capped_dist_def)
    interpret ms: Metric_space "topspace X" d
      by (simp add: d_def ms'.capped_dist)
    define f where "f \<equiv> (\<lambda>x n. d x (xn n))"
    have f_inj:"inj_on f (topspace X)"
    proof
      fix x y
      assume xy:"x \<in> topspace X" "y \<in> topspace X" "f x = f y"
      then have "\<And>n. d x (xn n) = d y (xn n)" by(auto simp: f_def dest: fun_cong)
      hence d2:"d x y \<le> 2 * d x (xn n)" for n
        using ms.triangle[OF xy(1) _ xy(2),of "xn n",simplified ms.commute[of "xn n" y]] dense_in_subset[OF U(2)] xn(1)[of n]
        by auto
      have "d x y < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
      proof -
        have "0 < \<epsilon> / 2" using that by simp
        then obtain n where "d x (xn n) < \<epsilon> / 2"
          using ms.mdense_def2[of U,simplified d(1)] U(2) xy(1) xn(2) by blast
        with d2[of n] show ?thesis by simp
      qed
      hence "d x y = 0"
        by (metis ms.nonneg[of x y] dual_order.irrefl order_neq_le_trans)
      thus "x = y"
        using xy by simp
    qed
    have f_img: "f ` topspace X \<subseteq> topspace Hilbert_cube_topology"
      using d(2) ms.nonneg by(auto simp: topspace_Hilbert_cube f_def less_le_not_le)
    have f_cont: "continuous_map X Hilbert_cube_topology f"
      unfolding continuous_map_componentwise_UNIV f_def continuous_map_in_subtopology
    proof safe
      show "continuous_map X euclideanreal (\<lambda>x. d x (xn k))" for k
      proof(rule continuous_map_eq[of _ _  "mdist_set ms.Self {xn k}"])
        show "continuous_map X euclideanreal (mdist_set ms.Self {xn k})"
          by (metis d(1) mdist_set_uniformly_continuous ms.mdist_Self ms.mspace_Self mtopology_of_def mtopology_of_euclidean uniformly_continuous_imp_continuous_map)
      next
        fix x
        assume "x \<in> topspace X"
        then show "mdist_set ms.Self {xn k} x = d x (xn k)"
          by(auto simp: ms.mdist_set_Self xns)
      qed    next
      show "d x (xn k) \<in> {0..1}" for x k
        using d(2) ms.nonneg by(auto simp: less_le_not_le)
    qed
    hence f_cont': "continuous_map X (subtopology Hilbert_cube_topology (f ` topspace X)) f"
      using continuous_map_into_subtopology by blast
    obtain g where g: "g ` (f ` topspace X) = topspace X" "\<And>x. x \<in> topspace X \<Longrightarrow> g (f x) = x" "\<And>x. x \<in> f ` topspace X \<Longrightarrow> f (g x) = x"
      by (meson f_inj f_the_inv_into_f the_inv_into_f_eq the_inv_into_onto)
    have g_cont: "continuous_map (subtopology Hilbert_cube_topology (f ` topspace X)) X g"    
    proof -
      interpret m01: Submetric UNIV dist "{0..1::real}"
        by(simp add: Submetric_def Submetric_axioms_def Met_TC.Metric_space_axioms)
      have m01_eq: "m01.sub.mtopology = top_of_set {0..1}"
        using m01.mtopology_submetric by auto
      have m01_Polish: "Polish_space m01.sub.mtopology"
        by(auto simp: m01_eq intro!: Polish_space_closedin)
      interpret m01': Metric_space "{0..1::real}" "\<lambda>x y. if 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 then dist x y else 0"
        by(auto intro!: Metric_space_eq[OF m01.sub.Metric_space_axioms]) metric
      have m01'_eq: "m01'.mtopology = top_of_set {0..1}"
        by(auto intro!: Metric_space_eq_mtopology[OF m01.sub.Metric_space_axioms,simplified m01_eq,symmetric]) metric
      have "dist x y \<le> 1" "dist x y \<ge> 0" if "x \<ge> 0" "x \<le> 1" "y \<ge> 0" "y \<le> 1" for x y :: real
        using dist_real_def that by auto
      then interpret ppm: Product_metric "1/2" "UNIV :: nat set" id id "\<lambda>_. {0..1::real}" "\<lambda>_ x y. if  0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 then dist x y else 0" 1
        by(auto intro!: product_metric_natI Metric_space_eq[OF m01.sub.Metric_space_axioms] simp: m01.sub.commute)
        
      have Hilbert_cube_eq: "ppm.Product_metric.mtopology = Hilbert_cube_topology"
        by(simp add: ppm.Product_metric_mtopology_eq[symmetric] m01'_eq)
      interpret f_S: Submetric "\<Pi>\<^sub>E x\<in>UNIV. {0..1}"  ppm.product_dist "f ` topspace X"
        by(auto simp: Submetric_def ppm.Product_metric.Metric_space_axioms Submetric_axioms_def f_def order.strict_implies_order[OF d(2)])
      have 1:"subtopology Hilbert_cube_topology (f ` topspace X) = f_S.sub.mtopology"
        using Hilbert_cube_eq f_S.mtopology_submetric by auto
      have "continuous_map f_S.sub.mtopology ms.mtopology g"
        unfolding continuous_map_iff_limit_seq[OF f_S.sub.first_countable_mtopology]
      proof safe
        fix yn y
        assume h:" limitin f_S.sub.mtopology yn y sequentially"
        have h':"limitin ppm.Product_metric.mtopology yn y sequentially"
          using f_S.limitin_submetric_iff h by blast
        hence m01_conv:"\<And>n. limitin  m01'.mtopology (\<lambda>i. yn i n) (y n) sequentially" "y \<in> UNIV \<rightarrow>\<^sub>E {0..1}"
          by(auto simp: ppm.limitin_M_iff_limitin_Mi)
        have "\<exists>N. \<forall>n\<ge>N. \<exists>zn. yn n = f zn \<and> zn \<in> topspace X"
          using h g by(simp only: f_S.sub.limit_metric_sequentially) (meson imageE ppm.K_pos)
        then obtain N' zn where zn:"\<And>n. n \<ge> N' \<Longrightarrow> f (zn n) = yn n" "\<And>n. n \<ge> N' \<Longrightarrow> zn n \<in> topspace X"
          by metis
        obtain z where z:"f z = y" "z \<in> topspace X"
          using h f_S.sub.limitin_mspace by blast
        show "limitin ms.mtopology (\<lambda>n. g (yn n)) (g y) sequentially"
          unfolding ms.limit_metric_sequentially
        proof safe
          fix \<epsilon> :: real
          assume he: "0 < \<epsilon>"
          then have "0 < \<epsilon> / 3" by simp
          then obtain m where m:"d z (xn m) < \<epsilon> / 3"
            using ms.mdense_def2[of U,simplified d(1)] U(2) z(2) xn(2) by blast
          have "\<And>e. e>0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. yn n m \<in> {0..1} \<and> dist (yn n m) (y m) < e"
            using m01_conv(1)[of m,simplified m01'.limit_metric_sequentially]
            by fastforce
          from this[OF \<open>0 < \<epsilon> / 3\<close>] obtain N where "\<And>n. n \<ge> N \<Longrightarrow> \<bar>yn n m - y m\<bar> < \<epsilon> / 3" "\<And>n. n \<ge> N \<Longrightarrow> yn n m \<in> {0..1}"
            by(auto simp: dist_real_def)
          hence N:"\<And>n. n \<ge> N \<Longrightarrow> yn n m < \<epsilon> / 3 + y m"
            by (metis abs_diff_less_iff add.commute)
          have "\<exists>N. \<forall>n\<ge>N. zn n \<in> topspace X \<and> d (zn n) z < \<epsilon>"
          proof(safe intro!: exI[where x="max N N'"])
            fix n
            assume "max N N' \<le> n"
            then have "N \<le> n" "N' \<le> n"
              by auto
            then have "d (zn n) z \<le> f (zn n) m + d z (xn m)"
              using ms.triangle[OF zn(2)[of n] xns[of m] z(2),simplified ms.commute[of "xn m" z]]
              by(auto simp: f_def)
            also have "... < \<epsilon> / 3 + y m + d z (xn m)"
              using N[OF \<open>N\<le>n\<close>] zn(1)[of n] \<open>N' \<le> n\<close> by simp
            also have "... =  \<epsilon> / 3 + d z (xn m) + d z (xn m)"
              by(simp add: z(1)[symmetric] f_def)
            also have "... < \<epsilon>"
              using m by auto
            finally show "d (zn n) z < \<epsilon>" .
          qed(use zn in auto)
          thus "\<exists>N. \<forall>n\<ge>N. g (yn n) \<in> topspace X \<and> d (g (yn n)) (g y) < \<epsilon>"
            by (metis dual_order.trans nle_le zn(1) z(1) g(2)[OF z(2)] g(2)[OF zn(2)])
        qed(use g z in auto)
      qed
      hence "continuous_map f_S.sub.mtopology ms.mtopology g"
        by(auto simp: mtopology_of_def)
      thus ?thesis
        by(simp add: d(1) 1)
    qed
    show ?thesis
      using f_img g(2,3) f_cont' g_cont
      by(auto intro!: exI[where x="f ` topspace X"] homeomorphic_maps_imp_homeomorphic_space[where f=f and g=g] simp: homeomorphic_maps_def)
  qed
qed

corollary embedding_into_Hilbert_cube_gdelta_in:
  assumes "Polish_space X"
  shows "\<exists>A. gdelta_in Hilbert_cube_topology A \<and> X homeomorphic_space (subtopology Hilbert_cube_topology A)"
proof -
  obtain A where h:"A \<subseteq> topspace Hilbert_cube_topology" "X homeomorphic_space subtopology Hilbert_cube_topology A"
    using embedding_into_Hilbert_cube Polish_space_imp_metrizable_space Polish_space_imp_separable_space assms by blast
  with completely_metrizable_space_homeo_image_gdelta_in[OF Polish_space_imp_completely_metrizable_space[OF assms] Polish_space_imp_completely_metrizable_space[OF Polish_space_Hilbert_cube] h(1,2)]
  show ?thesis
    by blast
qed

subsubsection \<open> Embedding from Cantor Space \<close>
lemma embedding_from_Cantor_space:
  assumes "Polish_space X" "uncountable (topspace X)"
  shows "\<exists>A. gdelta_in X A \<and> Cantor_space_topology homeomorphic_space (subtopology X A)"
proof -
  obtain U P where up: "countable U" "openin X U" "perfect_set X P""U \<union> P = topspace X" "U \<inter> P = {}" "\<And>a. a \<noteq> {} \<Longrightarrow> openin (subtopology X P) a \<Longrightarrow> uncountable a"
    using Cantor_Bendixon[OF Polish_space_imp_second_countable[OF assms(1)]] by auto
  have P: "closedin X P" "P \<subseteq> topspace X" "uncountable P"
    using countable_Un_iff[of U P] up(1) assms up(4)
    by(simp_all add: perfect_setD[OF up(3)])
  then have pp: "Polish_space (subtopology X P)"
    by (simp add: assms(1) Polish_space_closedin)
  have Ptop: "topspace (subtopology X P) = P"
    using P(2) by auto
  obtain U where U: "countable U" "dense_in (subtopology X P) U"
    using Polish_space_def pp separable_space_def2 by auto
  with uncountable_infinite[OF P(3)] P(2)
  have "infinite U"
    by (metis Metric_space.t1_space_mtopology Ptop assms(1) completely_metrizable_space_def dense_in_infinite Polish_space_def t1_space_subtopology)
  obtain d where "Metric_space P d" and d:"Metric_space.mtopology P d = subtopology X P" and mdc: "Metric_space.mcomplete P d"
    by (metis Metric_space.topspace_mtopology Ptop completely_metrizable_space_def Polish_space_def pp)
  interpret md: Metric_space P d by fact
  define xn where "xn \<equiv> from_nat_into U"
  have xn: "bij_betw xn UNIV U" "\<And>n m. n \<noteq> m \<Longrightarrow> xn n \<noteq> xn m" "\<And>n. xn n \<in> U" "\<And>n. xn n \<in> P" "md.mdense (range xn)"
    using bij_betw_from_nat_into[OF U(1) \<open>infinite U\<close>] dense_in_subset[OF U(2)] d U(2) range_from_nat_into[OF infinite_imp_nonempty[OF \<open>infinite U\<close>] U(1)]
    by(auto simp add: xn_def  U(1) \<open>infinite U\<close> from_nat_into[OF infinite_imp_nonempty[OF \<open>infinite U\<close>]])
  have perfect:"perfect_space md.mtopology"
    using d perfect_set_subtopology up(3) by simp
  define jn where "jn \<equiv> (\<lambda>n. LEAST i. i > n \<and> md.mcball (xn i) ((1/2)^i) \<subseteq> md.mball (xn n) ((1/2)^n) - md.mball (xn n) ((1/2)^i))"
  define kn where "kn \<equiv> (\<lambda>n. LEAST k. k > jn n \<and> md.mcball (xn k) ((1/2)^k) \<subseteq> md.mball (xn n) ((1/2)^jn n))"
  have dxmxn: "\<forall>n n'. \<exists>m. m > n \<and> m > n' \<and> (1/2)^(m-1) < d (xn n) (xn m) \<and> d (xn n) (xn m) < (1/2)^(Suc n')"
  proof safe
    fix n n'
    have hinfin':"infinite (md.mball x e \<inter> (range xn))" if "x \<in> P" "e > 0" for x e
    proof
      assume h_fin:"finite (md.mball x e \<inter> range xn)"
      have h_nen:"md.mball x e \<inter> range xn \<noteq> {}"
        using xn(5) that by(auto simp: md.mdense_def)
      have infin: "infinite (md.mball x e)"
        using md.perfect_set_mball_infinite[OF perfect] that by simp
      then obtain y where y:"y \<in> md.mball x e" "y \<notin> range xn"
        using h_fin by(metis inf.absorb_iff2 inf_commute subsetI)
      define e' where "e' = Min {d y xk |xk. xk \<in> md.mball x e \<inter> range xn}"
      have fin: "finite  {d y xk |xk. xk \<in> md.mball x e \<inter> range xn}"
        using finite_imageI[OF h_fin,of "d y"] by (metis Setcompr_eq_image)
      have nen: "{d y xk |xk. xk \<in> md.mball x e \<inter> range xn} \<noteq> {}"
        using h_nen by auto
      have "e' > 0"
        unfolding e'_def Min_gr_iff[OF fin nen]
      proof safe
        fix l
        assume "xn l \<in> md.mball x e"
        with y
        show "0 < d y (xn l)"
          by auto
      qed
      obtain e'' where e'': "e'' > 0" "md.mball y e'' \<subseteq> md.mball x e" "y \<in> md.mball y e''"
        by (meson md.centre_in_mball_iff md.in_mball md.openin_mball md.openin_mtopology y(1))
      define \<epsilon> where "\<epsilon> \<equiv> min e' e''"
      have "\<epsilon> > 0"
        using e''(1) \<open>e' > 0\<close> by(simp add: \<epsilon>_def)
      then obtain m where m: "d y (xn m) < \<epsilon>"
        using md.mdense_def2[of "range xn"] xn(5) y(1) by fastforce
      consider "xn m \<in> md.mball x e" | "xn m \<in> P - md.mball x e"
        using xn(4) by auto
      then show False
      proof cases
        case 1
        then have "e' \<le> d y (xn m)"
          using Min_le_iff[OF fin nen] by(auto simp: e'_def)
        thus ?thesis
          using m by(simp add: \<epsilon>_def)
      next
        case 2
        then have "xn m \<notin> md.mball y e''"
          using e''(2) by auto
        hence "e'' \<le> d y (xn m)"
          using y e'' xn by auto
        thus ?thesis
          using m by(simp add: \<epsilon>_def)
      qed
    qed
    have hinfin:"infinite (md.mball x e \<inter> (xn ` {l<..}))" if "x \<in> P" "e > 0" for x e l
    proof
      assume "finite (md.mball x e \<inter> xn ` {l<..})"
      moreover have "finite (md.mball x e \<inter> xn ` {..l})" by simp
      moreover have "(md.mball x e \<inter> (range xn)) = (md.mball x e \<inter> xn ` {l<..}) \<union> (md.mball x e \<inter> xn ` {..l})"
        by fastforce
      ultimately have "finite (md.mball x e \<inter> (range xn))"
        by auto
      with hinfin'[OF that] show False ..
    qed
    have "infinite (md.mball (xn n) ((1/2)^Suc n'))"
      using md.perfect_set_mball_infinite[OF perfect] xn(4)[of n] by simp
    then obtain x where x: "x \<in> md.mball (xn n) ((1/2)^Suc n')" "x \<noteq> xn n"
      by (metis finite_insert finite_subset infinite_imp_nonempty singletonI subsetI)
    then obtain e where e: "e > 0" "md.mball x e \<subseteq> md.mball (xn n) ((1/2)^Suc n')" "x \<in> md.mball x e"
      by (meson md.centre_in_mball_iff md.in_mball md.openin_mball md.openin_mtopology)
    have "d (xn n) x > 0"
      using xn x by simp
    then obtain m' where m': "m' - 1 > 0" "(1/2)^(m' - 1) < d (xn n) x"
      by (metis One_nat_def diff_Suc_Suc diff_zero one_less_numeral_iff reals_power_lt_ex semiring_norm(76))
    define m where "m \<equiv> max m' (max n' (Suc n))"
    then have "m \<ge> m'" "m \<ge> n'" "m \<ge> Suc n" by simp_all
    hence m: "m - 1 > 0" "(1/2)^(m - 1) < d (xn n) x" "m > n"
      using m' less_trans[OF _ m'(2),of "(1 / 2) ^ (m - 1)"]
      by auto (metis diff_less_mono le_eq_less_or_eq)
    define \<epsilon> where "\<epsilon> \<equiv> min e (d (xn n) x - (1/2)^(m - 1))"
    have "\<epsilon> > 0"
      using e m by(simp add: \<epsilon>_def)
    have ball_le:"md.mball x \<epsilon> \<subseteq> md.mball (xn n) ((1 / 2) ^ Suc n')"
      using e(2) by(auto simp add: \<epsilon>_def)
    obtain k where k: "xn k \<in> md.mball x \<epsilon>" "k > m"
      using \<open>\<epsilon> > 0\<close> infinite_imp_nonempty[OF hinfin,of _ \<epsilon>] x(1) by fastforce
    show "\<exists>m>n. n' < m \<and> (1 / 2) ^ (m - 1) < d (xn n) (xn m) \<and> d (xn n) (xn m) < (1 / 2) ^ Suc n'"
    proof(intro exI[where x=k] conjI)
      have "(1 / 2) ^ (k - 1) < (1 / (2 :: real)) ^ (m - 1)"
        using k(2) m(3) by simp
      also have "... = d (xn n) x + ((1/2)^ (m - 1) - d (xn n) x)" by simp
      also have "... < d (xn n) x - d (xn k) x"
        using k by(auto simp: \<epsilon>_def md.commute)
      also have "... \<le> d (xn n) (xn k)"
        using xn x md.mdist_reverse_triangle[of "xn n" x "xn k"] by(auto simp: md.commute)
      finally show "(1 / 2) ^ (k - 1) < d (xn n) (xn k)" .
    qed(use \<open>m \<ge> n'\<close> k ball_le m(3) in auto)
  qed
  have "jn n > n \<and> md.mcball (xn (jn n)) ((1/2)^(jn n)) \<subseteq> md.mball (xn n) ((1/2)^n) - md.mball (xn n) ((1/2)^(jn n))" for n
    unfolding jn_def
  proof(rule LeastI_ex)
    obtain m where m:"m > n" "(1 / 2) ^ (m - 1) < d (xn n) (xn m)" "d (xn n) (xn m) < (1 / 2) ^ Suc n"
      using dxmxn by auto
    show "\<exists>x>n. md.mcball (xn x) ((1 / 2) ^ x) \<subseteq> md.mball (xn n) ((1 / 2) ^ n) - md.mball (xn n) ((1 / 2) ^ x)"
    proof(safe intro!: exI[where x=m] m(1))
      fix x
      assume h:"x \<in> md.mcball (xn m) ((1 / 2) ^ m)"
      have 1:"d (xn n) x < (1 / 2) ^ n"
      proof -
        have "d (xn n) x < (1 / 2) ^ Suc n + (1 / 2) ^ m"
          using m(3) md.triangle[OF xn(4)[of n] xn(4)[of m],of x] h by auto
        also have "... \<le> (1 / 2) ^ Suc n + (1 / 2) ^ Suc n"
          by (metis Suc_lessI add_mono divide_less_eq_1_pos divide_pos_pos less_eq_real_def m(1) one_less_numeral_iff power_strict_decreasing_iff semiring_norm(76) zero_less_numeral zero_less_one)
        finally show ?thesis by simp
      qed
      have 2:"(1 / 2) ^ m \<le> d (xn n) x"
      proof -
        have "(1 / 2) ^ (m - 1) < d (xn n) x + (1 / 2) ^ m"
          using order.strict_trans2[OF m(2) md.triangle[OF xn(4)[of n] _ xn(4)[of m]]] h md.commute by fastforce
        hence "(1 / 2) ^ (m - 1) - (1 / 2) ^ m \<le> d (xn n) x"
          by simp
        thus ?thesis
          using not0_implies_Suc[OF gr_implies_not0[OF m(1)]] by auto
      qed
      show "x \<in> md.mball (xn n) ((1 / 2) ^ n)"
           "x \<in> md.mball (xn n) ((1 / 2) ^ m) \<Longrightarrow> False"
        using xn h 1 2 by auto
    qed
  qed
  hence jn: "\<And>n. jn n > n" "\<And>n. md.mcball (xn (jn n)) ((1/2)^(jn n)) \<subseteq> md.mball (xn n) ((1/2)^n) - md.mball (xn n) ((1/2)^(jn n))"
    by simp_all
  have "kn n > jn n \<and> md.mcball (xn (kn n)) ((1/2)^(kn n)) \<subseteq> md.mball (xn n) ((1/2)^jn n)" for n
    unfolding kn_def
  proof(rule LeastI_ex)
    obtain m where m:"m > jn n" "d (xn n) (xn m) < (1 / 2) ^ Suc (jn n)"
      using dxmxn by blast 
    show "\<exists>x>jn n. md.mcball (xn x) ((1 / 2) ^ x) \<subseteq> md.mball (xn n) ((1 / 2) ^ jn n)"
    proof(intro exI[where x=m] conjI)
      show "md.mcball (xn m) ((1 / 2) ^ m) \<subseteq> md.mball (xn n) ((1 / 2) ^ jn n)"
      proof
        fix x
        assume h:"x \<in> md.mcball (xn m) ((1 / 2) ^ m)"
        have "d (xn n) x < (1 / 2)^ Suc (jn n) + (1 / 2) ^ m"
          using md.triangle[OF xn(4)[of n] xn(4)[of m]] h m(2) by fastforce
        also have "... \<le> (1 / 2)^ Suc (jn n) + (1 / 2)^ Suc (jn n)"
          by (metis Suc_le_eq add_mono dual_order.refl less_divide_eq_1_pos linorder_not_less m(1) not_numeral_less_one power_decreasing zero_le_divide_1_iff zero_le_numeral zero_less_numeral)
        finally show "x \<in> md.mball (xn n) ((1 / 2) ^ jn n)"
          using xn(4) h by auto
      qed
    qed(use m(1) in auto)
  qed
  hence kn: "\<And>n. kn n > jn n" "\<And>n. md.mcball (xn (kn n)) ((1/2)^(kn n)) \<subseteq> md.mball (xn n) ((1/2)^(jn n))"
    by simp_all
  have jnkn_pos: "jn n > 0" "kn n > 0" for n
    using not0_implies_Suc[OF gr_implies_not0[OF jn(1)[of n]]] kn(1)[of n] by auto

  define bn :: "real list \<Rightarrow> nat"
    where "bn \<equiv> rec_list 1 (\<lambda>a l t. if a = 0 then jn t else kn t)"
  have bn_simp: "bn [] = 1" "bn (a # l) = (if a = 0 then jn (bn l) else kn (bn l))" for a l
    by(simp_all add: bn_def)
  define to_listn :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real list"
    where "to_listn \<equiv> (\<lambda>x . rec_nat [] (\<lambda>n t. x n # t))"
  have to_listn_simp: "to_listn x 0 = []" "to_listn x (Suc n) = x n # to_listn x n" for x n
    by(simp_all add: to_listn_def)
  have to_listn_eq: "(\<And>m. m < n \<Longrightarrow> x m = y m) \<Longrightarrow> to_listn x n = to_listn y n" for x y n
    by(induction n) (auto simp: to_listn_simp)
  have bn_gtn: "bn (to_listn x n) > n" for x n
    apply(induction n arbitrary: x)
    using jn(1) kn(1) by(auto simp: bn_simp to_listn_simp) (meson Suc_le_eq le_less less_trans_Suc)+
  define rn where "rn \<equiv> (\<lambda>n. Min (range (\<lambda>x. (1 / 2 :: real) ^ bn (to_listn x n))))"
  have rn_fin: "finite (range (\<lambda>x. (1 / 2 :: real) ^ bn (to_listn x n)))" for n
  proof -
    have "finite (range (\<lambda>x. bn (to_listn x n)))"
    proof(induction n)
      case ih:(Suc n)
      have "(range (\<lambda>x. bn (to_listn x (Suc n)))) \<subseteq> (range (\<lambda>x. jn (bn (to_listn x n)))) \<union> (range (\<lambda>x. kn (bn (to_listn x n))))"
        by(auto simp: to_listn_simp bn_simp)
      moreover have "finite ..."
        using ih finite_range_imageI by auto
      ultimately show ?case by(rule finite_subset)
    qed(simp add: to_listn_simp)
    thus ?thesis
      using finite_range_imageI by blast
  qed
  have rn_nen: "(range (\<lambda>x. (1 / 2 :: real) ^ bn (to_listn x n))) \<noteq> {}" for n
    by simp
  have rn_pos: "0 < rn n" for n
    by(simp add: Min_gr_iff[OF rn_fin rn_nen] rn_def)
  have rn_less: "rn n < (1/2)^n" for n
    using bn_gtn[of n] by(auto simp: rn_def Min_less_iff[OF rn_fin rn_nen])
  have cball_le_ball:"md.mcball (xn (bn (a#l))) ((1/2)^(bn (a#l))) \<subseteq> md.mball (xn (bn l)) ((1/2) ^ (bn l))" for a l    
    using kn(2)[of "bn l"] less_imp_le[OF jn(1)] jn(2) md.mball_subset_concentric[of  "(1 / 2) ^ jn (bn l)" "(1 / 2) ^ bn l" "xn (bn l)"]
    by(auto simp: bn_simp)
  hence cball_le:"md.mcball (xn (bn (a#l))) ((1/2)^(bn (a#l))) \<subseteq> md.mcball (xn (bn l)) ((1/2) ^ (bn l))" for a l
    using md.mball_subset_mcball by blast
  have cball_disj: "md.mcball (xn (bn (0#l))) ((1/2)^(bn (0#l))) \<inter> md.mcball (xn (bn (1#l))) ((1/2)^(bn (1#l))) = {}" for l
    using jn(2) kn(2) by(auto simp: bn_simp)
  have "\<forall>x. \<exists>l. l \<in> P \<and> (\<Inter>n. md.mcball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))) = {l}"
  proof
    fix x
    show "\<exists>l. l \<in> P \<and> (\<Inter>n. md.mcball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))) = {l}"
    proof(safe intro!: md.mcomplete_nest_sing[THEN iffD1,OF mdc,rule_format])
      show "md.mcball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n)) = {} \<Longrightarrow> False" for n
        using md.mcball_eq_empty xn(4) by auto
    next
      show "decseq (\<lambda>n. md.mcball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n)))"
        by(intro decseq_SucI,simp add: to_listn_simp cball_le)
    next
      fix e :: real
      assume "0 < e"
      then obtain N where N: "(1 / 2) ^ N <  e"
        by (meson reals_power_lt_ex rel_simps(49) rel_simps(9))
      show "\<exists>n a. md.mcball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n)) \<subseteq> md.mcball a e"
      proof(safe intro!: exI[where x=N] exI[where x="xn (bn (to_listn x N))"])
        fix y
        assume "y \<in> md.mcball (xn (bn (to_listn x N))) ((1 / 2) ^ bn (to_listn x N))"
        then have "y \<in> md.mcball (xn (bn (to_listn x N))) ((1 / 2) ^ N)"
          using md.mcball_subset_concentric[OF power_decreasing[OF less_imp_le[OF bn_gtn[of N x]],of "1/2"]]
          by fastforce
        thus "y \<in> md.mcball (xn (bn (to_listn x N))) e"
          using N \<open>0 < e\<close> by auto
      qed
    qed
  qed
  then obtain f where f:"\<And>x. f x \<in> P" "\<And>x. (\<Inter>n. md.mcball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))) = {f x}"
    by metis
  hence f': "\<And>n x. f x \<in> md.mcball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))"
    by blast
  have f'': "f x \<in> md.mball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))" for n x
    using f'[of x "Suc n"] cball_le_ball[of _ "to_listn x n"] by(fastforce simp: to_listn_simp)
  interpret bdmd: Submetric P d "f ` (\<Pi>\<^sub>E i\<in>UNIV. {0,1})"
    by standard (use f in auto)
  have bdmd_sub: "bdmd.sub.mtopology = subtopology X (f ` (\<Pi>\<^sub>E i\<in>UNIV. {0,1}))"
    using f(1) Int_absorb1[of "f ` (UNIV \<rightarrow>\<^sub>E {0, 1})" P] by(fastforce simp: bdmd.mtopology_submetric d subtopology_subtopology)
  let ?d = "\<lambda>x y. if (x = 0 \<or> x = 1) \<and> (y = 0 \<or> y = 1) then dist x y else 0"
  interpret d01: Metric_space "{0,1::real}" ?d
    by(auto simp: Metric_space_def)
  have d01: "d01.mtopology = top_of_set {0,1}"
  proof -
    have "d01.mtopology = Metric_space.mtopology {0,1} dist"
      by(auto intro!: Metric_space_eq_mtopology simp: Metric_space_def metric_space_class.dist_commute)
    also have "... = top_of_set {0,1}"
      by(auto intro!: Submetric.mtopology_submetric[of UNIV dist "{0,1::real}",simplified] simp: Submetric_def Metric_space_def Submetric_axioms_def dist_real_def)
    finally show ?thesis .
  qed
  interpret pd: Product_metric "1/2" UNIV id id "\<lambda>_. {0,1::real}" "\<lambda>_. ?d" 1
    by(auto intro!: product_metric_natI d01.Metric_space_axioms)
  have mpd_top: "pd.Product_metric.mtopology = Cantor_space_topology"
    by(auto simp: pd.Product_metric_mtopology_eq[symmetric] d01 intro!: product_topology_cong)
  define def_at where "def_at x y \<equiv> LEAST n. x n \<noteq> y n" for x y :: "nat \<Rightarrow> real"
  have def_atxy: "\<And>n. n < def_at x y \<Longrightarrow> x n = y n" "x (def_at x y) \<noteq> y (def_at x y)" if "x \<noteq> y" for x y
  proof -
    have "\<exists>n. x n \<noteq> y n"
      using that by auto
    from LeastI_ex[OF this]
    show "\<And>n. n < def_at x y \<Longrightarrow> x n = y n" "x (def_at x y) \<noteq> y (def_at x y)"
      using not_less_Least by(auto simp: def_at_def)
  qed
  have def_at_le_if: "pd.product_dist x y \<le> (1/2)^n \<Longrightarrow> n \<le> def_at x y" if assm:"x \<noteq> y" "x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" for x y n
  proof -
    assume h:"pd.product_dist x y \<le> (1 / 2) ^ n"
    have "x m = y m" if m_less_n: "m < n" for m
    proof(rule ccontr)
      assume nen: "x m \<noteq> y m"
      then have "?d (x m) (y m) = 1"
        using assm(2,3) by(auto simp: submetric_def)
      hence "1 \<le> 2 ^ m * pd.product_dist x y"
        using pd.product_dist_geq[of m m,simplified,OF assm(2,3)] by simp
      hence "(1/2)^m \<le> 2^m * (1/2)^m * pd.product_dist x y" by simp
      hence "(1/2)^m \<le> pd.product_dist x y" by (simp add: power_one_over)
      also have "... \<le> (1 / 2) ^ n"
        by(simp add: h)
      finally show False
        using that by auto
    qed
    thus "n \<le> def_at x y"
      by (meson def_atxy(2) linorder_not_le that(1))
  qed
  have def_at_le_then: "pd.product_dist x y \<le> 2 * (1/2)^n" if assm:"x \<noteq> y" "x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "n \<le> def_at x y" for x y n
  proof -
    have "\<And>m. m < n \<Longrightarrow> x m = y m"
      by (metis def_atxy(1) order_less_le_trans that(4))
    hence 1:"\<And>m. m < n \<Longrightarrow> ?d (x m) (y m) = 0"
      by (simp add: submetric_def)
    have "pd.product_dist x y = (\<Sum>i. (1/2)^(i + n) * (?d (x (i + n)) (y (i + n)))) + (\<Sum>i<n. (1/2)^i * (?d (x i) (y i)))"
      using assm pd.product_dist_summable'[simplified] unfolding product_dist_def id_apply by(auto intro!: suminf_split_initial_segment simp: product_dist_def )
    also have "... = (\<Sum>i. (1/2)^(i + n) * (?d (x (i + n)) (y (i + n))))"
      by(simp add: 1)
    also have "... \<le> (\<Sum>i. (1/2)^(i + n))"
      using pd.product_dist_summable' unfolding id_apply by(auto intro!: suminf_le summable_ignore_initial_segment)
    finally show ?thesis
      using pd.nsum_of_rK[of n] by simp
  qed
  have d_le_def: "d (f x) (f y) \<le> (1/2)^(def_at x y)" if assm:"x \<noteq> y" "x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" for x y
  proof -
    have 1:"to_listn x n = to_listn y n" if "n \<le> def_at x y" for n
    proof -
      have "\<And>m. m < n \<Longrightarrow> x m = y m"
        by (metis def_atxy(1) order_less_le_trans that)
      then show ?thesis
        by(auto intro!: to_listn_eq)
    qed
    have "f x \<in> md.mcball (xn (bn (to_listn x (def_at x y)))) ((1 / 2) ^ bn (to_listn x (def_at x y)))"
         "f y \<in> md.mcball (xn (bn (to_listn x (def_at x y)))) ((1 / 2) ^ bn (to_listn x (def_at x y)))"
      using f'[of x "def_at x y"] f'[of y "def_at x y"] by(auto simp: 1[OF order_refl])
    hence "d (f x) (f y) \<le> 2 * (1 / 2) ^ bn (to_listn x (def_at x y))"
      using f(1) by(auto intro!: md.mdiameter_is_sup'[OF _ _ md.mdiameter_cball_leq])
    also have "... \<le> (1/2)^(def_at x y)"
    proof -
      have "Suc (def_at x y) \<le> bn (to_listn x (def_at x y))"
        using bn_gtn[of "def_at x y" x] by simp
      hence "(1 / 2) ^ bn (to_listn x (def_at x y)) \<le> (1 / 2 :: real) ^ Suc (def_at x y)"
        using power_decreasing_iff[OF pd.r] by blast
      thus ?thesis
        by simp
    qed
    finally show "d (f x) (f y) \<le> (1/2)^(def_at x y)" .
  qed
  have fy_in:"f y \<in> md.mcball (xn (bn (to_listn x m))) ((1/2)^bn (to_listn x m)) \<Longrightarrow> \<forall>l<m. x l = y l" if assm:"x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" for x y m
  proof(induction m)
    case ih:(Suc m)
    have "f y \<in> md.mcball (xn (bn (to_listn x m))) ((1 / 2) ^ bn (to_listn x m))"
      using ih(2) cball_le by(fastforce simp: to_listn_simp)
    with ih(1) have k:"k < m \<Longrightarrow> x k = y k" for k by simp
    show ?case
    proof safe
      fix l
      assume "l < Suc m"
      then consider "l < m" | "l = m"
        using \<open>l < Suc m\<close> by fastforce
      thus "x l = y l"
      proof cases
        case 2
        have 3:"f y \<in> md.mcball (xn (bn (y l # to_listn y l))) ((1 / 2) ^ bn (y l # to_listn y l))"
          using f'[of y "Suc l"] by(simp add: to_listn_simp)
        have 4:"f y \<in> md.mcball (xn (bn (x l # to_listn y l))) ((1 / 2) ^ bn (x l # to_listn y l))"
          using ih(2) to_listn_eq[of m x y,OF k] by(simp add: to_listn_simp 2)
        show ?thesis
        proof(rule ccontr)
          assume "x l \<noteq> y l"
          then consider "x l = 0" "y l = 1" | "x l = 1" "y l = 0"
            using assm(1,2) by(auto simp: PiE_def Pi_def) metis
          thus False
            by cases (use cball_disj[of "to_listn y l"] 3 4 in auto)
        qed
      qed(simp add: k)
    qed
  qed simp
  have d_le_rn_then: "\<exists>e>0. \<forall>y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1}). x \<noteq> y \<longrightarrow> d (f x) (f y) < e \<longrightarrow> n \<le> def_at x y" if assm: "x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" for x n
  proof(safe intro!: exI[where x="(1/2)^bn (to_listn x n) - d (xn (bn (to_listn x n))) (f x)"])
    show "0 < (1 / 2) ^ bn (to_listn x n) - d (xn (bn (to_listn x n))) (f x)"
      using f'' by auto
  next
    fix y
    assume h:"y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "d (f x) (f y) < (1 / 2) ^ bn (to_listn x n) - d (xn (bn (to_listn x n))) (f x)" "x \<noteq> y"
    then have "f y \<in> md.mcball (xn (bn (to_listn x n))) ((1/2)^bn (to_listn x n))"
      using md.triangle[OF xn(4)[of "bn (to_listn x n)"] f(1)[of x] f(1)[of y]]
      by(simp add: xn(4)[of "bn (to_listn x n)"] f(1)[of y] md.mcball_def)
    with fy_in[OF assm h(1)] have "\<forall>m < n. x m = y m"
      by auto
    thus "n \<le> def_at x y"
      by (meson def_atxy(2) linorder_not_le h(3))
  qed
  have 0: "f ` (\<Pi>\<^sub>E i\<in>UNIV. {0,1}) \<subseteq> topspace X"
    using f(1) P(2) by auto
  have 1: "continuous_map pd.Product_metric.mtopology bdmd.sub.mtopology f"
    unfolding pd.Product_metric.metric_continuous_map[OF bdmd.sub.Metric_space_axioms]
  proof safe
    fix x :: "nat \<Rightarrow> real" and \<epsilon> :: real
    assume h:"x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "0 < \<epsilon>"
    then obtain n where n:"(1/2)^n < \<epsilon>"
      using real_arch_pow_inv[OF _ pd.r(2)] by auto
    show "\<exists>\<delta>>0. \<forall>y. y\<in>UNIV \<rightarrow>\<^sub>E {0, 1} \<and> pd.product_dist x y < \<delta> \<longrightarrow> d (f x) (f y) < \<epsilon>"
    proof(safe intro!: exI[where x="(1/2)^n"])
      fix y
      assume y:"y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "pd.product_dist x y < (1 / 2) ^ n"
      consider "x = y" | "x \<noteq> y" by auto
      thus "d (f x) (f y) < \<epsilon>"
      proof cases
        case 1
        with y(1) h md.zero[OF f(1)[of y] f(1)[of y]]
        show ?thesis by simp
      next
        case 2
        then have "n \<le> def_at x y"
          using h(1) y by(auto intro!: def_at_le_if)
        have "d (f x) (f y) \<le> (1/2)^(def_at x y)"
          using h(1) y(1) by(auto simp: d_le_def[OF 2 h(1) y(1)])
        also have "... \<le> (1/2)^n"
          using \<open>n \<le> def_at x y\<close> by simp
        finally show ?thesis
          using n by simp
      qed
    qed simp
  qed
  have 2: "open_map pd.Product_metric.mtopology bdmd.sub.mtopology f"
  proof -
    have "open_map (mtopology_of pd.Product_metric.Self) (subtopology (mtopology_of md.Self) (f ` mspace pd.Product_metric.Self)) f"
    proof(safe intro!: Metric_space_open_map_from_dist)
      fix x :: "nat \<Rightarrow> real" and \<epsilon> :: real
      assume h:"x \<in> mspace pd.Product_metric.Self" "0 < \<epsilon>"
      then have x:"x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" by simp
      from h obtain n where n: "(1/2)^n < \<epsilon>"
        using real_arch_pow_inv[OF _ pd.r(2)] by auto
      obtain e where e: "e > 0" "\<And>y. y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1}) \<Longrightarrow> x \<noteq> y \<Longrightarrow> d (f x) (f y) < e \<Longrightarrow> Suc n \<le> def_at x y"
        using d_le_rn_then[OF x,of "Suc n"] by auto
      show "\<exists>\<delta>>0. \<forall>y\<in>mspace pd.Product_metric.Self. mdist md.Self (f x) (f y) < \<delta> \<longrightarrow> mdist pd.Product_metric.Self x y < \<epsilon>"
        unfolding md.mdist_Self pd.Product_metric.mspace_Self pd.Product_metric.mdist_Self
      proof(safe intro!: exI[where x=e])
        fix y
        assume y:"y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" and "d (f x) (f y) < e"
        then have d':"d (f x) (f y) < e"
          using h(1) by simp
        consider "x = y" | "x \<noteq> y" by auto
        thus "pd.product_dist x y < \<epsilon>"
          by cases (use pd.Product_metric.zero[OF y y] h(2) def_at_le_then[OF _ x y e(2)[OF y _ d']] n in auto)
      qed(use e(1) in auto)
    qed(use f in auto)
    thus ?thesis
      by (simp add: bdmd.mtopology_submetric mtopology_of_def)
  qed
  have 3: "f ` (topspace pd.Product_metric.mtopology) = topspace bdmd.sub.mtopology"
    by simp
  have 4: "inj_on f (topspace pd.Product_metric.mtopology)"
    unfolding pd.Product_metric.topspace_mtopology
  proof
    fix x y
    assume h:"x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "f x = f y"
    show "x = y"
    proof
      fix n
      have "f y \<in> md.mcball (xn (bn (to_listn x (Suc n)))) ((1/2)^bn (to_listn x (Suc n)))"
        using f'[of x "Suc n"] by(simp add: h)
      thus "x n = y n"
        using fy_in[OF h(1,2),of "Suc n"] by simp
    qed
  qed
  show ?thesis
    using homeomorphic_map_imp_homeomorphic_space[OF bijective_open_imp_homeomorphic_map[OF 1 2 3 4]] 0
    by (metis (no_types, lifting) assms(1) bdmd_sub completely_metrizable_space_homeo_image_gdelta_in mpd_top Polish_space_Cantor_space Polish_space_def)
qed



subsection \<open>Borel Spaces generated from Polish Spaces\<close>
lemma closedin_clopen_topology:
  assumes "Polish_space X" "closedin X a"
  shows "\<exists>X'. Polish_space X' \<and> (\<forall>u. openin X u \<longrightarrow> openin X' u) \<and> topspace X = topspace X' \<and> sets (borel_of X) = sets (borel_of X') \<and> openin X' a \<and> closedin X' a"
proof -
  have p1:"Polish_space (subtopology X a)"
    by (simp add: assms Polish_space_closedin)
  then obtain da' where da': "Metric_space a da'" "subtopology X a = Metric_space.mtopology a da'" "Metric_space.mcomplete a da'"
    by (metis Metric_space.topspace_mtopology assms(2) closedin_subset completely_metrizable_space_def Polish_space_imp_completely_metrizable_space topspace_subtopology_subset)
  define da where "da = Metric_space.capped_dist da' (1/2)"
  have da: "subtopology X a = Metric_space.mtopology a da" "Metric_space.mcomplete a da"
    using da' by(auto simp: da_def Metric_space.mtopology_capped_metric Metric_space.mcomplete_capped_metric)
  interpret pa: Metric_space a da
    using da' by(simp add: Metric_space.capped_dist da_def)
  have da_bounded: "\<And>x y. da x y < 1"
    using da' by(auto simp: da_def Metric_space.capped_dist_def)
  have p2:"Polish_space (subtopology X (topspace X - a))"
    by (meson assms(1) assms(2) closedin_def Polish_space_openin)
  then obtain db' where db': "Metric_space (topspace X - a) db'" "subtopology X (topspace X - a) = Metric_space.mtopology (topspace X - a) db'" "Metric_space.mcomplete (topspace X - a) db'"
    by (metis Diff_subset Metric_space.topspace_mtopology completely_metrizable_space_def Polish_space_imp_completely_metrizable_space topspace_subtopology_subset)
  define db where "db = Metric_space.capped_dist db' (1/2)"
  have db: "subtopology X (topspace X - a) = Metric_space.mtopology (topspace X - a) db" "Metric_space.mcomplete (topspace X - a) db"
    using db' by(auto simp: db_def Metric_space.mtopology_capped_metric Metric_space.mcomplete_capped_metric)
  interpret pb: Metric_space "topspace X - a" db
    using db' by(simp add: Metric_space.capped_dist db_def)
  have db_bounded: "\<And>x y. db x y < 1"
    using db' by(auto simp: db_def Metric_space.capped_dist_def)
  interpret p: Sum_metric UNIV "\<lambda>b. if b then a else topspace X - a" "\<lambda>b. if b then da else db"
    using da db da_bounded db_bounded by(auto intro!: sum_metricI simp: disjoint_family_on_def pa.Metric_space_axioms pb.Metric_space_axioms)
  have 0: "(\<Union>i. if i then a else topspace X - a) = topspace X"
    using closedin_subset assms by auto

  have 1: "sets (borel_of X) = sets (borel_of p.Sum_metric.mtopology)"
  proof -
    have "sigma_sets (topspace X) (Collect (openin X)) = sigma_sets (topspace X) (Collect (openin p.Sum_metric.mtopology))"
    proof(rule sigma_sets_eqI)
      fix a
      assume "a \<in> Collect (openin X)"
      then have "openin p.Sum_metric.mtopology a"
        by(simp only: p.openin_mtopology_iff) (auto simp: 0 da(1)[symmetric] db(1)[symmetric] openin_subtopology dest: openin_subset)
      thus "a \<in> sigma_sets (topspace X) (Collect (openin p.Sum_metric.mtopology))"
        by auto
    next
      interpret s: sigma_algebra "topspace X" "sigma_sets (topspace X) (Collect (openin X))"
        by(auto intro!: sigma_algebra_sigma_sets openin_subset)
      fix b
      assume "b \<in> Collect (openin p.Sum_metric.mtopology)"
      then have "openin p.Sum_metric.mtopology b" by auto
      then have b:"b \<subseteq> topspace X" "openin (subtopology X a) (b \<inter> a)" "openin (subtopology X (topspace X - a)) (b \<inter> (topspace X - a))"
        by(simp_all only: p.openin_mtopology_iff,insert 0 da(1) db(1)) (auto simp: all_bool_eq)
      have [simp]: "(b \<inter> a) \<union> (b \<inter> (topspace X - a)) = b"
        using Diff_partition b(1) by blast
      have "(b \<inter> a) \<union> (b \<inter> (topspace X - a)) \<in> sigma_sets (topspace X) (Collect (openin X))"
      proof(rule sigma_sets_Un)
        have [simp]:"a \<in> sigma_sets (topspace X) (Collect (openin X))"
        proof -
          have "topspace X - (topspace X - a) \<in> sigma_sets (topspace X) (Collect (openin X))"
            by(rule sigma_sets.Compl) (use assms in auto)
          thus ?thesis
            using double_diff[OF closedin_subset[OF assms(2)]] by simp
        qed            
        from b(2,3) obtain T T' where T:"openin X T" "openin X T'" and [simp]:"b \<inter> a = T \<inter> a" "b \<inter> (topspace X - a) = T' \<inter> (topspace X - a)"
          by(auto simp: openin_subtopology)
        show "b \<inter> a \<in> sigma_sets (topspace X) (Collect (openin X))"
             "b \<inter> (topspace X - a) \<in> sigma_sets (topspace X) (Collect (openin X))"
          using T assms by auto
      qed
      thus "b \<in> sigma_sets (topspace X) (Collect (openin X))"
        by simp
    qed
    thus ?thesis
      by(simp only: sets_borel_of p.Sum_metric.topspace_mtopology) (use 0 in auto)
  qed
  have 2:"\<And>u. openin X u \<Longrightarrow> openin p.Sum_metric.mtopology u"
    by(simp only: p.openin_mtopology_iff) (auto simp: all_bool_eq da(1)[symmetric] db(1)[symmetric] openin_subtopology dest: openin_subset)
  have 3:"openin p.Sum_metric.mtopology a"
    by(simp only: p.openin_mtopology_iff) (auto simp: all_bool_eq)
  have 4:"closedin p.Sum_metric.mtopology a"
    by (metis 0 2 assms(2) closedin_def p.Sum_metric.topspace_mtopology)
  have 5: "topspace X = topspace p.Sum_metric.mtopology"
    by(simp only: p.Sum_metric.topspace_mtopology) (simp only: 0)
  have 6: "Polish_space p.Sum_metric.mtopology"
    by(rule p.Polish_spaceI,insert da(2) db(2)  p1 p2) (auto simp: da(1) db(1) Polish_space_def)
  show ?thesis
    by(rule exI[where x=p.Sum_metric.mtopology]) (insert 5 2 6, simp only: 1 3 4 ,auto)
qed

lemma Polish_space_union_Polish:
  fixes X :: "nat \<Rightarrow> 'a topology"
  assumes "\<And>n. Polish_space (X n)" "\<And>n. topspace (X n) = Xt" "\<And>x y. x \<in> Xt \<Longrightarrow> y \<in> Xt \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>Ox Oy. (\<forall>n. openin (X n) Ox) \<and> (\<forall>n. openin (X n) Oy) \<and> x \<in> Ox \<and> y \<in> Oy \<and> disjnt Ox Oy"
  defines "Xun \<equiv> topology_generated_by (\<Union>n. {u. openin (X n) u})"
  shows "Polish_space Xun"
proof -
  have topsXun:"topspace Xun = Xt"
    using assms(2) by(auto simp: Xun_def dest:openin_subset)
  define f :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where "f \<equiv> (\<lambda>x n. x)"
  have "continuous_map Xun (product_topology X UNIV) f"
    by(auto simp: assms(2) topsXun f_def continuous_map_componentwise, auto simp: Xun_def openin_topology_generated_by_iff continuous_map_def assms(2) dest:openin_subset[of "X _",simplified assms(2)] )
      (insert openin_subopen, fastforce intro!: generate_topology_on.Basis)
  hence 1: "continuous_map Xun (subtopology (product_topology X UNIV) (f ` (topspace Xun))) f"
    by(auto simp: continuous_map_in_subtopology)
  have 2: "inj_on f (topspace Xun)"
    by(auto simp: inj_on_def f_def dest:fun_cong)
  have 3: "f ` (topspace Xun) = topspace (subtopology (product_topology X UNIV) (f ` (topspace Xun)))"
    by(auto simp: topsXun assms(2) f_def)
  have 4: "open_map Xun (subtopology (product_topology X UNIV) (f ` (topspace Xun))) f"
  proof(safe intro!: open_map_generated_topo[OF _ 2[simplified Xun_def],simplified Xun_def[symmetric]])
    fix u n
    assume u:"openin (X n) u"
    show "openin (subtopology (product_topology X UNIV) (f ` topspace Xun)) (f ` u)"
      unfolding openin_subtopology
    proof(safe intro!: exI[where x="{ \<lambda>i. if i = n then a else b i |a b. a \<in>u \<and> b \<in> UNIV \<rightarrow> Xt}"])
      show "openin (product_topology X UNIV) {\<lambda>i. if i = n then a else b i |a b. a \<in>u \<and> b \<in> UNIV \<rightarrow> Xt}"
        by(auto simp: openin_product_topology_alt u assms(2) openin_topspace[of "X _",simplified assms(2)] intro!: exI[where x="\<lambda>i. if i = n then u else Xt"])
          (auto simp: PiE_def Pi_def, metis openin_subset[OF u,simplified assms(2)] in_mono)
    next
      show "\<And>y. y \<in> u \<Longrightarrow> \<exists>a b. f y = (\<lambda>i. if i = n then a else b i) \<and> a \<in> u \<and> b \<in> UNIV \<rightarrow> Xt"
        using assms(2) f_def openin_subset u by fastforce
    next
      show "\<And>y. y \<in> u \<Longrightarrow> f y \<in> f ` topspace Xun"
        using openin_subset[OF u] by(auto simp: assms(2) topsXun)
    next
      show "\<And>x xa a b. xa \<in> topspace Xun \<Longrightarrow> f xa = (\<lambda>i. if i = n then a else b i) \<Longrightarrow> a \<in> u \<Longrightarrow> b \<in> UNIV \<rightarrow> Xt \<Longrightarrow> f xa \<in> f ` u"
        using openin_subset[OF u] by(auto simp: topsXun assms(2)) (metis f_def imageI)
    qed
  qed
  have 5:"(subtopology (product_topology X UNIV) (f ` topspace Xun)) homeomorphic_space Xun"
    using homeomorphic_map_imp_homeomorphic_space[OF bijective_open_imp_homeomorphic_map[OF 1 4 3 2]]
    by(simp add: homeomorphic_space_sym[of Xun])
  show ?thesis
  proof(safe intro!: homeomorphic_Polish_space_aux[OF Polish_space_closedin[OF Polish_space_product] 5] assms)
    show "closedin (product_topology X UNIV) (f ` topspace Xun)"
    proof -
      have 1: "openin (product_topology X UNIV) ((UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt)"
      proof(rule openin_subopen[THEN iffD2])
        show "\<forall>x\<in>(UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt. \<exists>T. openin (product_topology X UNIV) T \<and> x \<in> T \<and> T \<subseteq> (UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt"
        proof safe
          fix x
          assume x:"x \<in> UNIV \<rightarrow>\<^sub>E Xt" "x \<notin> f ` Xt"
          have "\<exists>n. x n \<noteq> x 0"
          proof(rule ccontr)
            assume " \<nexists>n. x n \<noteq> x 0"
            then have "\<forall>n. x n = x 0" by auto
            hence "x = (\<lambda>_. x 0)" by auto
            thus False
              using x by(auto simp: f_def topsXun assms(2))
          qed
          then obtain n where n: "n \<noteq> 0" "x n \<noteq> x 0"
            by metis
          from assms(3)[OF _ _ this(2)] x
          obtain On O0 where h:"\<And>n. openin (X n) On" "\<And>n. openin (X n) O0" "x n \<in> On" "x 0 \<in> O0" "disjnt On O0"
            by fastforce
          have "openin (product_topology X UNIV) ((\<lambda>x. x 0) -` O0 \<inter> topspace (product_topology X UNIV))"
            using continuous_map_product_coordinates[of 0 UNIV X] h(2)[of 0] by blast
          moreover have "openin (product_topology X UNIV) ((\<lambda>x. x n) -` On \<inter> topspace (product_topology X UNIV))"
            using continuous_map_product_coordinates[of n UNIV X] h(1)[of n] by blast
          ultimately have op: "openin (product_topology X UNIV) ((\<lambda>T. T 0) -` O0 \<inter> topspace (product_topology X UNIV) \<inter> ((\<lambda>T. T n) -` On \<inter> topspace (product_topology X UNIV)))"
            by auto
          have xin:"x \<in> (\<lambda>T. T 0) -` O0 \<inter> topspace (product_topology X UNIV) \<inter> ((\<lambda>T. T n) -` On \<inter> topspace (product_topology X UNIV))"
            using x h(3,4) by(auto simp: assms(2))
          have subset:"(\<lambda>T. T 0) -` O0 \<inter> topspace (product_topology X UNIV) \<inter> ((\<lambda>T. T n) -` On \<inter> topspace (product_topology X UNIV)) \<subseteq> (UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt"
            using h(5) by(auto simp: assms(2) disjnt_def f_def)

          show "\<exists>T. openin (product_topology X UNIV) T \<and> x \<in> T \<and> T \<subseteq> (UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt"
            by(rule exI[where x="((\<lambda>x. x 0) -` O0 \<inter> topspace (product_topology X UNIV)) \<inter> ((\<lambda>x. x n) -` On \<inter> topspace (product_topology X UNIV))"]) (use op xin subset in auto)
        qed
      qed
      thus ?thesis
        by(auto simp: closedin_def assms(2) topsXun f_def)
    qed
  qed(simp add: f_def)
qed

lemma sets_clopen_topology:
  assumes "Polish_space X" "a \<in> sets (borel_of X)"
  shows "\<exists>X'. Polish_space X' \<and> (\<forall>u. openin X u \<longrightarrow> openin X' u) \<and> topspace X = topspace X' \<and> sets (borel_of X) = sets (borel_of X') \<and> openin X' a \<and> closedin X' a"
proof -
  have "a \<in> sigma_sets (topspace X) {U. closedin X U}"
    using assms by(simp add: sets_borel_of_closed)
  thus ?thesis
  proof induction
    case (Basic a)
    then show ?case
      by(simp add: assms closedin_clopen_topology)
  next
    case Empty
    with polish_space_axioms assms show ?case
      by auto
  next
    case (Compl a)
    then obtain X' where S':"Polish_space X'" "(\<forall>u. openin X u \<longrightarrow> openin X' u)" "topspace X = topspace X'" "sets (borel_of X) = sets (borel_of X')" "openin X' a" "closedin X' a"
      by auto
    from closedin_clopen_topology[OF S'(1) S'(6)] S'
    show ?case by auto
  next
    case ih:(Union a)
    then obtain Si where Si:
    "\<And>i. Polish_space (Si i)" "\<And>u i. openin X u \<Longrightarrow> openin (Si i) u" "\<And>i::nat. topspace X = topspace (Si i)" "\<And>i. sets (borel_of X) = sets (borel_of (Si i))" "\<And>i. openin (Si i) (a i)" "\<And>i. closedin (Si i) (a i)"
      by metis
    define Sun where "Sun \<equiv> topology_generated_by (\<Union>n. {u. openin (Si n) u})"
    have Sun1: "Polish_space Sun"
      unfolding Sun_def 
    proof(safe intro!: Polish_space_union_Polish[where Xt="topspace X"])
      fix x y
      assume xy:"x \<in> topspace X" "y \<in> topspace X" "x \<noteq> y"
      then obtain Ox Oy where Oxy: "x \<in> Ox" "y \<in> Oy" "openin X Ox" "openin X Oy" "disjnt Ox Oy"
        using metrizable_imp_Hausdorff_space[OF Polish_space_imp_metrizable_space[OF assms(1)]]
        by(simp only: Hausdorff_space_def) metis
      show "\<exists>Ox Oy. (\<forall>x. openin (Si x) Ox) \<and> (\<forall>x. openin (Si x) Oy) \<and> x \<in> Ox \<and> y \<in> Oy \<and> disjnt Ox Oy"
        by(rule exI[where x=Ox],insert Si(2) Oxy, auto intro!: exI[where x=Oy])
    qed (use Si in auto)
    have Suntop:"topspace X = topspace Sun"
      using Si(3) by(auto simp: Sun_def dest: openin_subset)
    have Sunsets: "sets (borel_of X) = sets (borel_of Sun)" (is "?lhs = ?rhs")
    proof -
      have "?lhs = sigma_sets (topspace X) (\<Union>n. {u. openin (Si n) u})"
      proof
        show "sets (borel_of X) \<subseteq> sigma_sets (topspace X) (\<Union>n. {u. openin (Si n) u})"
          using Si(2) by(auto simp: sets_borel_of intro!: sigma_sets_mono')
      next
        show "sigma_sets (topspace X) (\<Union>n. {u. openin (Si n) u}) \<subseteq> sets (borel_of X)"
          by(simp add: sigma_sets_le_sets_iff[of "borel_of X" "\<Union>n. {u. openin (Si n) u}",simplified space_borel_of]) (use Si(4) sets_borel_of in fastforce)
      qed
      also have "... = ?rhs"
        using borel_of_second_countable'[OF Polish_space_imp_second_countable[OF Sun1],of "\<Union>n. {u. openin (Si n) u}"]
        by (simp add: Sun_def Suntop subbase_in_def subset_Pow_Union)
      finally show ?thesis .
    qed
    have Sun_open: "\<And>u i. openin (Si i) u \<Longrightarrow> openin Sun u"
      by(auto simp: Sun_def openin_topology_generated_by_iff intro!: generate_topology_on.Basis)
    have Sun_opena: "openin Sun (\<Union>i. a i)"
      using Sun_open[OF Si(5),simplified Sun_def] by(auto simp: Sun_def openin_topology_generated_by_iff intro!: generate_topology_on.UN)
    hence "closedin Sun (topspace Sun - (\<Union>i. a i))"
      by auto
    from closedin_clopen_topology[OF Sun1 this]
    show ?case
      using Suntop Sunsets Sun_open[OF Si(2)] Sun_opena
      by (metis closedin_def openin_closedin_eq)
  qed
qed

end