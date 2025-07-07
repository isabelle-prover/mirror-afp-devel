section \<open>Kraus families\<close>

theory Kraus_Families
  imports
    Wlog.Wlog
    Hilbert_Space_Tensor_Product.Partial_Trace
  
    Backported
    Misc_Kraus_Maps
  
  abbrevs
    "=kr" = "=\<^sub>k\<^sub>r" and "==kr" = "\<equiv>\<^sub>k\<^sub>r" and "*kr" = "*\<^sub>k\<^sub>r"
begin

unbundle cblinfun_syntax

subsection \<open>Kraus families\<close>

definition \<open>kraus_family \<EE> \<longleftrightarrow> bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>}) \<and> 0 \<notin> fst ` \<EE>\<close>
  for \<EE> :: \<open>((_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space) \<times> _) set\<close>

typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family = 
  \<open>Collect kraus_family :: (('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> 'x) set set\<close>
  by (rule exI[of _ \<open>{}\<close>], auto simp: kraus_family_def)
setup_lifting type_definition_kraus_family

lemma kraus_familyI:
  assumes \<open>bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
  assumes \<open>0 \<notin> fst ` \<EE>\<close>
  shows \<open>kraus_family \<EE>\<close>
  by (meson assms kraus_family_def)

lift_definition kf_apply :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a,'a) trace_class \<Rightarrow> ('b,'b) trace_class\<close> is
  \<open>\<lambda>\<EE> \<rho>. (\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>)\<close> .
notation kf_apply (infixr \<open>*\<^sub>k\<^sub>r\<close> 70)

lemma kraus_family_if_finite[iff]: \<open>kraus_family \<EE>\<close> if \<open>finite \<EE>\<close> and \<open>0 \<notin> fst ` \<EE>\<close>
proof -
  define B where \<open>B = (\<Sum>(E,x)\<in>\<EE>. E* o\<^sub>C\<^sub>L E)\<close>
  have \<open>(\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite M\<close> and \<open>M \<subseteq> \<EE>\<close> for M
    unfolding B_def
    using \<open>finite \<EE>\<close> \<open>M \<subseteq> \<EE>\<close> apply (rule sum_mono2)
    by (auto intro!: positive_cblinfun_squareI)
  with that show ?thesis
    by (auto intro!: bdd_aboveI[of _ B] simp: kraus_family_def)
qed

lemma kf_apply_scaleC:
  shows \<open>kf_apply \<EE> (c *\<^sub>C x) = c *\<^sub>C kf_apply \<EE> x\<close>
  by (simp add: kf_apply_def cblinfun.scaleC_right case_prod_unfold sandwich_tc_scaleC_right
      flip: infsum_scaleC_right)

lemma kf_apply_abs_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) abs_summable_on \<EE>\<close>
proof -
  wlog \<rho>_pos: \<open>\<rho> \<ge> 0\<close> generalizing \<rho>
  proof -
    obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
      and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
      apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
    have \<open>norm (sandwich_tc x \<rho>) 
      \<le> norm (sandwich_tc x \<rho>1)
      + norm (sandwich_tc x \<rho>2)
      + norm (sandwich_tc x \<rho>3)
      + norm (sandwich_tc x \<rho>4)\<close> 
      (is \<open>_ \<le> ?S x\<close>) for x
      by (auto simp add: \<rho>_decomp sandwich_tc_plus sandwich_tc_minus  sandwich_tc_scaleC_right
          scaleC_add_right scaleC_diff_right norm_mult
          intro!: norm_triangle_le norm_triangle_le_diff)
    then have *: \<open>norm (sandwich_tc (fst x) \<rho>) \<le> norm (?S (fst x))\<close> for x
      by force
    show ?thesis
      unfolding case_prod_unfold
      apply (rule abs_summable_on_comparison_test[OF _ *])
      apply (intro Misc_Kraus_Maps.abs_summable_on_add abs_summable_norm abs_summable_on_scaleC_right pos)
      using hypothesis
      by (simp_all add: case_prod_unfold pos)
  qed

  have aux: \<open>trace_norm x = Re (trace x)\<close> if \<open>x \<ge> 0\<close> and \<open>trace_class x\<close> for x
    by (metis Re_complex_of_real that(1) trace_norm_pos)
  have trace_EE\<rho>_pos: \<open>trace ((E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>) \<ge> 0\<close> for E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    apply (simp add: cblinfun_assoc_right trace_class_comp_right
        flip: circularity_of_trace)
    by (auto intro!: trace_pos sandwich_pos 
        simp: cblinfun_assoc_left from_trace_class_pos \<rho>_pos 
        simp flip: sandwich_apply)
  have trace_EE\<rho>_lin: \<open>linear (\<lambda>M. Re (trace (M o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close> for M
    apply (rule linear_compose[where g=Re, unfolded o_def])
    by (auto intro!: bounded_linear.linear bounded_clinear.bounded_linear
        bounded_clinear_trace_duality' bounded_linear_Re)
  have trace_EE\<rho>_mono: \<open>mono_on (Collect ((\<le>) 0)) (\<lambda>A. Re (trace (A o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close> for M
    apply (intro mono_onI Re_mono)
    apply (subst diff_ge_0_iff_ge[symmetric])
    apply (subst trace_minus[symmetric])
    by (auto intro!: trace_class_comp_right trace_comp_pos
        simp: from_trace_class_pos \<rho>_pos
        simp flip: cblinfun_compose_minus_left)

  from assms
  have \<open>bdd_above ((\<lambda>F. (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
    by (simp add: kraus_family_def)
  then have \<open>bdd_above ((\<lambda>F. Re (trace ((\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
    apply (rule bdd_above_transform_mono_pos)
    by (auto intro!: sum_nonneg positive_cblinfun_squareI[OF refl] trace_EE\<rho>_mono
        simp: case_prod_unfold)
  then have \<open>bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. Re (trace ((E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))) ` {F. F \<subseteq> \<EE> \<and> finite F})\<close>
    apply (subst (asm) real_vector.linear_sum[where f=\<open>\<lambda>M. Re (trace (M o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>])
    by (auto intro!: trace_EE\<rho>_lin simp: case_prod_unfold conj_commute)
  then have \<open>(\<lambda>(E,_). Re (trace ((E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))) summable_on \<EE>\<close>
    apply (rule nonneg_bdd_above_summable_on[rotated])
    using trace_EE\<rho>_pos 
    by (auto simp: less_eq_complex_def)
 then have \<open>(\<lambda>(E,_). Re (trace (from_trace_class (sandwich_tc E \<rho>)))) summable_on \<EE>\<close>
    by (simp add: from_trace_class_sandwich_tc sandwich_apply cblinfun_assoc_right trace_class_comp_right
        flip: circularity_of_trace)
  then have \<open>(\<lambda>(E,_). trace_norm (from_trace_class (sandwich_tc E \<rho>))) summable_on \<EE>\<close>
    by (simp add: aux from_trace_class_pos \<rho>_pos  sandwich_tc_pos)
  then show \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) abs_summable_on \<EE>\<close>
    by (simp add: norm_trace_class.rep_eq case_prod_unfold)
qed

lemma kf_apply_summable:
  shows \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) summable_on (Rep_kraus_family \<EE>)\<close>
  apply (rule abs_summable_summable)
  apply (rule kf_apply_abs_summable)
  using Rep_kraus_family by blast


lemma kf_apply_has_sum:
  shows \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum kf_apply \<EE> \<rho>) (Rep_kraus_family \<EE>)\<close>
  using kf_apply_summable Rep_kraus_family[of \<EE>]
  by (auto intro!: has_sum_infsum simp add: kf_apply_def kf_apply_summable case_prod_unfold)

lemma kf_apply_plus_right:
  shows \<open>kf_apply \<EE> (x + y) = kf_apply \<EE> x + kf_apply \<EE> y\<close>
  using kf_apply_summable Rep_kraus_family[of \<EE>]
  by (auto intro!: infsum_add
      simp add: kf_apply_def sandwich_tc_plus scaleC_add_right case_prod_unfold)

lemma kf_apply_uminus_right:
  shows \<open>kf_apply \<EE> (- x) = - kf_apply \<EE> x\<close>
  using kf_apply_summable  Rep_kraus_family[of \<EE>]
  by (auto intro!: infsum_uminus 
      simp add: kf_apply_def sandwich_tc_uminus_right scaleC_minus_right case_prod_unfold)


lemma kf_apply_minus_right:
  shows \<open>kf_apply \<EE> (x - y) = kf_apply \<EE> x - kf_apply \<EE> y\<close>
  by (simp only: diff_conv_add_uminus kf_apply_plus_right kf_apply_uminus_right)

lemma kf_apply_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_apply \<EE> \<rho> \<ge> 0\<close>
  by (auto intro!: infsum_nonneg_traceclass scaleC_nonneg_nonneg of_nat_0_le_iff
      sandwich_tc_pos assms simp: kf_apply_def)

lemma kf_apply_mono_right:
  assumes \<open>\<rho> \<ge> \<tau>\<close>
  shows \<open>kf_apply \<EE> \<rho> \<ge> kf_apply \<EE> \<tau>\<close>
  apply (subst diff_ge_0_iff_ge[symmetric])
  apply (subst kf_apply_minus_right[symmetric])
  apply (rule kf_apply_pos)
  using assms by (subst diff_ge_0_iff_ge)

lemma kf_apply_geq_sum:
  assumes \<open>\<rho> \<ge> 0\<close> and \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
  shows \<open>kf_apply \<EE> \<rho> \<ge> (\<Sum>(E,_)\<in>M. sandwich_tc E \<rho>)\<close>
proof (cases \<open>finite M\<close>)
  case True
  have *: \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on X\<close> if \<open>X \<subseteq> Rep_kraus_family \<EE>\<close> for X
    apply (rule summable_on_subset_banach[where A=\<open>Rep_kraus_family \<EE>\<close>])
     apply (rule kf_apply_summable[unfolded case_prod_unfold])
    using assms that by blast
  show ?thesis
    apply (subst infsum_finite[symmetric])
    using assms 
    by (auto intro!: infsum_mono_neutral_traceclass * scaleC_nonneg_nonneg of_nat_0_le_iff 
        True sandwich_tc_pos
        simp: kf_apply_def case_prod_unfold)
next
  case False
  with assms show ?thesis
    by (simp add: kf_apply_pos) 
qed

lift_definition kf_domain :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> 'x set\<close> is
  \<open>\<lambda>\<EE>. snd ` \<EE>\<close>.

(* lift_definition kf_remove_0 :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> ('a,'b,'x) kraus_family\<close> is
  \<open>Set.filter (\<lambda>(E,x). E\<noteq>0)\<close>
proof -
  fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close>
  have *: \<open>{F. finite F \<and> F \<subseteq> Set.filter (\<lambda>p. fst p \<noteq> 0) \<EE>} \<subseteq> {F. finite F \<and> F \<subseteq> \<EE>}\<close>
    by auto
  show \<open>\<EE> \<in> Collect kraus_family \<Longrightarrow> Set.filter (\<lambda>(E, x). E \<noteq> 0) \<EE> \<in> Collect kraus_family\<close>
    by (auto intro: bdd_above_mono2[OF _ *] simp add: kraus_family_def case_prod_unfold)
qed

lemma kf_remove_0_idem[simp]: \<open>kf_remove_0 (kf_remove_0 \<EE>) = kf_remove_0 \<EE>\<close>
  apply transfer'
  by auto

lemma kf_apply_remove_0[simp]:
  \<open>kf_apply (kf_remove_0 \<EE>) = kf_apply \<EE>\<close>
  by (auto intro!: ext infsum_cong_neutral simp add: kf_apply_def kf_remove_0.rep_eq)
*)

lemma kf_apply_clinear[iff]: \<open>clinear (kf_apply \<EE>)\<close>
  by (auto intro!: clinearI kf_apply_plus_right kf_apply_scaleC mult.commute)


lemma kf_apply_0_right[iff]: \<open>kf_apply \<EE> 0 = 0\<close>
  by (metis ab_left_minus kf_apply_plus_right kf_apply_uminus_right)

(* lemma kraus_familyI_0:
  assumes \<open>\<And>E x. (E,x) \<in> \<EE> \<Longrightarrow> E = 0\<close>
  shows \<open>kraus_family \<EE>\<close>
proof (unfold kraus_family_def, rule bdd_aboveI2)
  fix F
  assume F: \<open>F \<in> {F. finite F \<and> F \<subseteq> \<EE>}\<close>
  have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = 0\<close>
  proof (intro sum.neutral ballI)
    fix Ex assume asm: \<open>Ex \<in> F\<close>
    obtain E x where Ex: \<open>Ex = (E,x)\<close>
      by fastforce
    with asm F assms have \<open>E = 0\<close>
      by blast
    then show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) = 0\<close>
      by (simp add: Ex)
  qed
  then show \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> 0\<close>
    by simp
qed *)

lift_definition kf_operators :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> is
  \<open>image fst :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>.

subsection \<open>Bound and norm\<close>

lift_definition kf_bound :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> is
  \<open>\<lambda>\<EE>. infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close> .

lemma kf_bound_def':
  \<open>kf_bound \<EE> = Rep_cblinfun_wot (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
  unfolding kf_bound.rep_eq infsum_euclidean_eq[symmetric]
  apply transfer'
  by simp

definition \<open>kf_norm \<EE> = norm (kf_bound \<EE>)\<close>

lemma kf_norm_sum_bdd: \<open>bdd_above ((\<lambda>F. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. F \<subseteq> Rep_kraus_family \<EE> \<and> finite F})\<close>
proof -
  from Rep_kraus_family[of \<EE>]
  obtain B where B_bound: \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>F \<subseteq> Rep_kraus_family \<EE>\<close> and \<open>finite F\<close> for F
    by (metis (mono_tags, lifting) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
  have \<open>norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> norm B\<close> if \<open>F \<subseteq> Rep_kraus_family \<EE>\<close> and \<open>finite F\<close> for F
    by (metis (no_types, lifting) B_bound norm_cblinfun_mono positive_cblinfun_squareI split_def sum_nonneg that(1) that(2))
  then show \<open>bdd_above ((\<lambda>F. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. F \<subseteq> Rep_kraus_family \<EE> \<and> finite F})\<close>
    by (metis (mono_tags, lifting) bdd_aboveI2 mem_Collect_eq)
qed

lemma kf_norm_geq0[iff]:
  shows \<open>kf_norm \<EE> \<ge> 0\<close>
proof (cases \<open>Rep_kraus_family \<EE> \<noteq> {}\<close>)
  case True
  then obtain E where \<open>E \<in> Rep_kraus_family \<EE>\<close> by auto
  have \<open>0 \<le> (\<Squnion>F\<in>{F. F \<subseteq> Rep_kraus_family \<EE> \<and> finite F}. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E))\<close>
    apply (rule cSUP_upper2[where x=\<open>{E}\<close>])
    using True by (simp_all add: \<open>E \<in> Rep_kraus_family \<EE>\<close> kf_norm_sum_bdd)
  then show ?thesis
    by (simp add: kf_norm_def True)
next
  case False
  then show ?thesis
    by (auto simp: kf_norm_def)
qed

lemma kf_bound_has_sum:
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>) (kf_bound \<EE>)\<close>
proof -
  obtain B where B: \<open>finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> for F
    using Rep_kraus_family[of \<EE>]
    by (auto simp: kraus_family_def case_prod_unfold bdd_above_def)
  have \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
    using B by (auto intro!: summable_wot_boundedI positive_cblinfun_squareI simp: kraus_family_def)
  then show ?thesis
    by (auto intro!: has_sum_in_infsum_in simp: kf_bound_def)
qed

lemma kraus_family_iff_summable:
  \<open>kraus_family \<EE> \<longleftrightarrow> summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE> \<and> 0 \<notin> fst ` \<EE>\<close>
proof (intro iffI conjI)
  assume \<open>kraus_family \<EE>\<close>
  have \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (Abs_kraus_family \<EE>))\<close>
    using \<open>kraus_family \<EE>\<close> kf_bound_has_sum summable_on_in_def by blast
  with \<open>kraus_family \<EE>\<close> show \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
    by (simp add: Abs_kraus_family_inverse)
  from \<open>kraus_family \<EE>\<close> show \<open>0 \<notin> fst ` \<EE>\<close>
    using kraus_family_def by blast
next
  assume \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE> \<and> 0 \<notin> fst ` \<EE>\<close>
  then show \<open>kraus_family \<EE>\<close>
    by (auto intro!: summable_wot_bdd_above[where X=\<EE>] positive_cblinfun_squareI simp: kraus_family_def)
qed

lemma kraus_family_iff_summable':
  \<open>kraus_family \<EE> \<longleftrightarrow> (\<lambda>(E,x). Abs_cblinfun_wot (E* o\<^sub>C\<^sub>L E)) summable_on \<EE> \<and> 0 \<notin> fst ` \<EE>\<close>
  apply (transfer' fixing: \<EE>)
  by (simp add: kraus_family_iff_summable)

lemma kf_bound_summable:
  shows \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
  using kf_bound_has_sum summable_on_in_def by blast

lemma kf_bound_has_sum':
  shows \<open>((\<lambda>(E,x). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) has_sum Abs_cblinfun_wot (kf_bound \<EE>)) (Rep_kraus_family \<EE>)\<close>
  using kf_bound_has_sum[of \<EE>]
  apply transfer'
  by auto

lemma kf_bound_summable':
  \<open>((\<lambda>(E,x). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on Rep_kraus_family \<EE>)\<close>
  using has_sum_imp_summable kf_bound_has_sum' by blast

lemma kf_bound_is_Sup:
  shows \<open>is_Sup ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Rep_kraus_family \<EE>}) (kf_bound \<EE>)\<close>
proof -
  from Rep_kraus_family[of \<EE>]
  obtain B where \<open>finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> for F
    by (metis (mono_tags, lifting) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
  then have \<open>is_Sup ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Rep_kraus_family \<EE>})
     (infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>))\<close>
    apply (rule infsum_wot_is_Sup[OF summable_wot_boundedI[where B=B]])
    by (auto intro!: summable_wot_boundedI positive_cblinfun_squareI simp: case_prod_beta)
  then show ?thesis
    by (auto intro!: simp: kf_bound_def)
qed

lemma kf_bound_leqI:
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
  shows \<open>kf_bound \<EE> \<le> B\<close>
  using kf_bound_is_Sup[of \<EE>]
  by (simp add: assms is_Sup_def)

lemma kf_bound_pos[iff]: \<open>kf_bound \<EE> \<ge> 0\<close>
  using kf_bound_is_Sup[of \<EE>]
  by (metis (no_types, lifting) empty_subsetI finite.emptyI image_iff is_Sup_def mem_Collect_eq sum.empty)


lemma not_not_singleton_kf_norm_0: 
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>kf_norm \<EE> = 0\<close>
  by (simp add: not_not_singleton_cblinfun_zero[OF assms] kf_norm_def)

lemma kf_norm_sum_leqI:
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
  shows \<open>kf_norm \<EE> \<le> B\<close>
proof -
  have bpos: \<open>B \<ge> 0\<close>
    using assms[of \<open>{}\<close>] by auto
  wlog not_singleton: \<open>class.not_singleton TYPE('a)\<close> keeping bpos
    using not_not_singleton_kf_norm_0[OF negation, of \<EE>]
    by (simp add: \<open>B \<ge> 0\<close>)
  have [simp]: \<open>norm (id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a) = 1\<close>
    apply (rule norm_cblinfun_id[internalize_sort' 'a])
     apply (rule complex_normed_vector_axioms)
    by (rule not_singleton)
  have *: \<open>selfadjoint (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close> for F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close>
    by (auto intro!: pos_imp_selfadjoint sum_nonneg intro: positive_cblinfun_squareI)
  from assms
  have \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B *\<^sub>R id_cblinfun\<close>
    apply (rule less_eq_scaled_id_norm)
    by (auto intro!: * )
  then have \<open>kf_bound \<EE> \<le> B *\<^sub>R id_cblinfun\<close>
    using kf_bound_leqI by blast
  then have \<open>norm (kf_bound \<EE>) \<le> norm (B *\<^sub>R (id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a))\<close>
    apply (rule norm_cblinfun_mono[rotated])
    by simp
  then show ?thesis
    using bpos by (simp add: kf_norm_def)
qed

lemma kf_bound_geq_sum:
  assumes \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
  shows \<open>(\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> kf_bound \<EE>\<close>
proof (cases \<open>finite M\<close>)
  case True
  then show ?thesis
  using kf_bound_is_Sup[of \<EE>]
  apply (simp add: is_Sup_def case_prod_beta)
  using assms by blast
next
  case False
  then show ?thesis
    by simp
qed



lemma kf_norm_geq_norm_sum:
  assumes \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
  shows \<open>norm (\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> kf_norm \<EE>\<close>
  using kf_bound_geq_sum assms
  by (auto intro!: norm_cblinfun_mono sum_nonneg 
      intro: positive_cblinfun_squareI
      simp add: kf_norm_def case_prod_beta)

lemma kf_bound_finite: \<open>kf_bound \<EE> = (\<Sum>(E,x)\<in>Rep_kraus_family \<EE>. E* o\<^sub>C\<^sub>L E)\<close> if \<open>finite (Rep_kraus_family \<EE>)\<close>
  by (auto intro!: kraus_family_if_finite simp: kf_bound_def that infsum_in_finite)

lemma kf_norm_finite: \<open>kf_norm \<EE> = norm (\<Sum>(E,x)\<in>Rep_kraus_family \<EE>. E* o\<^sub>C\<^sub>L E)\<close>
  if \<open>finite (Rep_kraus_family \<EE>)\<close>
  by (simp add: kf_norm_def kf_bound_finite that)

lemma kf_apply_bounded_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>norm (kf_apply \<EE> \<rho>) \<le> kf_norm \<EE> * norm \<rho>\<close>
proof -
  have \<open>norm (kf_apply \<EE> \<rho>) = Re (trace_tc (\<Sum>\<^sub>\<infinity>(E,_)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>))\<close>
    apply (subst Re_complex_of_real[symmetric])
    apply (subst norm_tc_pos)
    using \<open>\<rho> \<ge> 0\<close> apply (rule kf_apply_pos)
    by (simp add: kf_apply_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,_)\<in>Rep_kraus_family \<EE>. Re (trace_tc (sandwich_tc E \<rho>)))\<close>
    using kf_apply_summable[of _ \<EE>]
    by (simp_all flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: case_prod_unfold bounded_linear_compose[of Re trace_tc] bounded_linear_Re
        o_def bounded_clinear.bounded_linear)
  also have \<open>\<dots> \<le> kf_norm \<EE> * norm \<rho>\<close>
  proof (rule infsum_le_finite_sums)
    show \<open>(\<lambda>(E,_). Re (trace_tc (sandwich_tc E \<rho>))) summable_on (Rep_kraus_family \<EE>)\<close>
      unfolding case_prod_beta
      apply (rule summable_on_bounded_linear[unfolded o_def, where h=\<open>\<lambda>x. Re (trace_tc x)\<close>])
      using kf_apply_summable[of _ \<EE>]
      by (simp_all flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: bounded_linear_compose[of Re trace_tc] bounded_linear_Re bounded_clinear.bounded_linear 
        o_def trace_tc_scaleC assms kf_apply_def case_prod_unfold)
    fix M :: \<open>(('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> 'c) set\<close> assume \<open>finite M\<close> and \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
    have \<open>(\<Sum>(E,_)\<in>M. Re (trace_tc (sandwich_tc E \<rho>)))
        = (\<Sum>(E,_)\<in>M. Re (trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E*)))\<close>
      by (simp add: trace_tc.rep_eq from_trace_class_sandwich_tc sandwich_apply scaleC_trace_class.rep_eq trace_scaleC)
    also have \<open>\<dots> = (\<Sum>(E,_)\<in>M. Re (trace (E* o\<^sub>C\<^sub>L E o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close>
      apply (subst circularity_of_trace)
      by (auto intro!: trace_class_comp_right simp: cblinfun_compose_assoc)
    also have \<open>\<dots> = Re (trace ((\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      by (simp only: trace_class_scaleC trace_class_comp_right trace_class_from_trace_class case_prod_unfold
          flip: Re_sum trace_scaleC trace_sum cblinfun.scaleC_left cblinfun_compose_scaleC_left cblinfun_compose_sum_left)
    also have \<open>\<dots> \<le> cmod (trace ((\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      by (rule complex_Re_le_cmod)
    also have \<open>\<dots> \<le> norm (\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) * trace_norm (from_trace_class \<rho>)\<close>
      apply (rule cmod_trace_times)
      by simp
    also have \<open>\<dots> \<le> kf_norm \<EE> * norm \<rho>\<close>
      apply (simp add: flip: norm_trace_class.rep_eq)
      apply (rule mult_right_mono)
      apply (rule kf_norm_geq_norm_sum)
      using assms \<open>M \<subseteq> Rep_kraus_family \<EE>\<close> by auto
    finally show \<open>(\<Sum>(E,_)\<in>M. Re (trace_tc (sandwich_tc E \<rho>))) \<le> kf_norm \<EE> * norm \<rho>\<close>
      by -
  qed
  finally show ?thesis 
    by -
qed

lemma kf_apply_bounded:
  \<comment> \<open>We suspect the factor 4 is not needed here but don't know how to prove that.\<close>
  \<open>norm (kf_apply \<EE> \<rho>) \<le> 4 * kf_norm \<EE> * norm \<rho>\<close>
proof -
  have aux: \<open>4 * x = x + x + x + x\<close> for x :: real
    by auto
  obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
    and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
    and norm: \<open>norm \<rho>1 \<le> norm \<rho>\<close> \<open>norm \<rho>2 \<le> norm \<rho>\<close> \<open>norm \<rho>3 \<le> norm \<rho>\<close> \<open>norm \<rho>4 \<le> norm \<rho>\<close>
    apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
  have \<open>norm (kf_apply \<EE> \<rho>) \<le>
          norm (kf_apply \<EE> \<rho>1) +
          norm (kf_apply \<EE> \<rho>2) +
          norm (kf_apply \<EE> \<rho>3) +
          norm (kf_apply \<EE> \<rho>4)\<close>
    by (auto intro!: norm_triangle_le norm_triangle_le_diff
        simp add: \<rho>_decomp kf_apply_plus_right kf_apply_minus_right
        kf_apply_scaleC)
  also have \<open>\<dots> \<le> 
        kf_norm \<EE> * norm \<rho>1
        + kf_norm \<EE> * norm \<rho>2
        + kf_norm \<EE> * norm \<rho>3
        + kf_norm \<EE> * norm \<rho>4\<close>
    by (auto intro!: add_mono simp add: pos kf_apply_bounded_pos)
  also have \<open>\<dots> = kf_norm \<EE> * (norm \<rho>1 + norm \<rho>2 + norm \<rho>3 + norm \<rho>4)\<close>
    by argo
  also have \<open>\<dots> \<le> kf_norm \<EE> * (norm \<rho> + norm \<rho> + norm \<rho> + norm \<rho>)\<close>
    by (auto intro!: mult_left_mono add_mono kf_norm_geq0 
        simp only: aux norm)
  also have \<open>\<dots> = 4 * kf_norm \<EE> * norm \<rho>\<close>
    by argo
  finally show ?thesis
    by -
qed

lemma kf_apply_bounded_clinear[bounded_clinear]:
  shows \<open>bounded_clinear (kf_apply \<EE>)\<close>
  apply (rule bounded_clinearI[where K=\<open>4 * kf_norm \<EE>\<close>])
    apply (auto intro!: kf_apply_plus_right kf_apply_scaleC mult.commute)[2]
  using kf_apply_bounded
  by (simp add: mult.commute)

lemma kf_bound_from_map: \<open>\<psi> \<bullet>\<^sub>C kf_bound \<EE> \<phi> = trace_tc (\<EE> *\<^sub>k\<^sub>r tc_butterfly \<phi> \<psi>)\<close>
proof -
  have \<open>has_sum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>) (kf_bound \<EE>)\<close>
    by (simp add: kf_bound_has_sum)
  then have \<open>((\<lambda>(E, x). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum \<psi> \<bullet>\<^sub>C kf_bound \<EE> \<phi>) (Rep_kraus_family \<EE>)\<close>
    by (auto intro!: simp: has_sum_in_cweak_operator_topology_pointwise case_prod_unfold)
  moreover have \<open>((\<lambda>(E, x). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum trace_tc (kf_apply \<EE> (tc_butterfly \<phi> \<psi>))) (Rep_kraus_family \<EE>)\<close>
  proof -
    have *: \<open>trace_tc (sandwich_tc E (tc_butterfly \<phi> \<psi>)) = \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>\<close> for E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by (auto intro!: simp: trace_tc.rep_eq from_trace_class_sandwich_tc
          sandwich_apply tc_butterfly.rep_eq circularity_of_trace[symmetric, of _ E]
          trace_class_comp_left cblinfun_compose_assoc trace_butterfly_comp)
    from kf_apply_has_sum Rep_kraus_family[of \<EE>]
    have \<open>((\<lambda>(E,x). sandwich_tc E (tc_butterfly \<phi> \<psi>)) has_sum kf_apply \<EE> (tc_butterfly \<phi> \<psi>)) (Rep_kraus_family \<EE>)\<close>
      by blast
    then have \<open>((\<lambda>(E,x). trace_tc (sandwich_tc E (tc_butterfly \<phi> \<psi>))) has_sum trace_tc (kf_apply \<EE> (tc_butterfly \<phi> \<psi>))) (Rep_kraus_family \<EE>)\<close>
      unfolding case_prod_unfold
      apply (rule has_sum_bounded_linear[rotated, unfolded o_def])
      by (simp add: bounded_clinear.bounded_linear)
    then
    show ?thesis
      by (simp add: * )
  qed
  ultimately show ?thesis
    using has_sum_unique by blast
qed

lemma trace_from_kf_bound: \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc (compose_tcr (kf_bound \<EE>) \<rho>)\<close>
proof -
  have \<open>separating_set bounded_clinear (Collect rank1_tc)\<close>
    apply (rule separating_set_bounded_clinear_dense)
    by simp
  moreover have \<open>bounded_clinear (\<lambda>a. trace_tc (\<EE> *\<^sub>k\<^sub>r a))\<close>
    by (intro bounded_linear_intros)
  moreover have \<open>bounded_clinear (\<lambda>a. trace_tc (compose_tcr (kf_bound \<EE>) a))\<close>
    by (intro bounded_linear_intros)
  moreover have \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r t) = trace_tc (compose_tcr (kf_bound \<EE>) t)\<close> if \<open>t \<in> Collect rank1_tc\<close> for t
  proof -
    from that obtain x y where t: \<open>t = tc_butterfly x y\<close>
      apply (transfer' fixing: x y)
      by (auto simp: rank1_iff_butterfly)
    then have \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r t) = y \<bullet>\<^sub>C kf_bound \<EE> x\<close>
      by (simp add: kf_bound_from_map)
    also have \<open>\<dots> = trace_tc (compose_tcr (kf_bound \<EE>) (tc_butterfly x y))\<close>
      apply (transfer' fixing: x y \<EE>)
      by (simp add: trace_butterfly_comp')
    also have \<open>\<dots> = trace_tc (compose_tcr (kf_bound \<EE>) t)\<close>
      by (simp add: t)
    finally show ?thesis
      by -
  qed
  ultimately show ?thesis
    by (rule eq_from_separatingI[where P=bounded_clinear and S=\<open>Collect rank1_tc\<close>, THEN fun_cong])
qed

lemma kf_bound_selfadjoint[iff]: \<open>selfadjoint (kf_bound \<EE>)\<close>
  by (simp add: positive_selfadjointI)

lemma kf_bound_leq_kf_norm_id:
  shows \<open>kf_bound \<EE> \<le> kf_norm \<EE> *\<^sub>R id_cblinfun\<close>
  by (auto intro!: less_eq_scaled_id_norm simp: kf_norm_def)

subsection \<open>Basic Kraus families\<close>

lemma kf_emptyset[iff]: \<open>kraus_family {}\<close>
  by (auto simp: kraus_family_def)


instantiation kraus_family :: (chilbert_space, chilbert_space, type) \<open>zero\<close> begin
lift_definition zero_kraus_family :: \<open>('a,'b,'x) kraus_family\<close> is \<open>{}\<close>
  by simp
instance..
end

lemma kf_apply_0[simp]: \<open>kf_apply 0 = 0\<close>
  by (auto simp: kf_apply_def zero_kraus_family.rep_eq)

lemma kf_bound_0[simp]: \<open>kf_bound 0 = 0\<close>
  by (metis (mono_tags, lifting) finite.intros(1) kf_bound.rep_eq kf_bound_finite sum_clauses(1) zero_kraus_family.rep_eq)

lemma kf_norm_0[simp]: \<open>kf_norm 0 = 0\<close>
  by (simp add: kf_norm_def zero_kraus_family.rep_eq)

lift_definition kf_of_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('a, 'b, unit) kraus_family\<close> is
  \<open>\<lambda>E::'a\<Rightarrow>\<^sub>C\<^sub>L'b. if E = 0 then {} else {(E, ())}\<close>
  by (auto intro: kraus_family_if_finite)

lemma kf_of_op0[simp]: \<open>kf_of_op 0 = 0\<close>
  apply transfer'
  by simp

lemma kf_of_op_norm[simp]: \<open>kf_norm (kf_of_op E) = (norm E)\<^sup>2\<close>
  by (simp add: kf_of_op.rep_eq kf_norm_finite)

lemma kf_operators_in_kf_of_op[simp]: \<open>kf_operators (kf_of_op U) = (if U = 0 then {} else {U})\<close>
  apply (transfer' fixing: U)
  by simp

lemma kf_domain_of_op[simp]: \<open>kf_domain (kf_of_op A) = {()}\<close> if \<open>A \<noteq> 0\<close>
  apply (transfer' fixing: A)
  using that by auto

definition \<open>kf_id = kf_of_op id_cblinfun\<close>

lemma kf_domain_id[simp]: \<open>kf_domain (kf_id :: ('a::{chilbert_space,not_singleton},_,_) kraus_family) = {()}\<close>
  by (simp add: kf_id_def)

lemma kf_of_op_id[simp]: \<open>kf_of_op id_cblinfun = kf_id\<close>
  by (simp add: kf_id_def)

lemma kf_norm_id_leq1: \<open>kf_norm kf_id \<le> 1\<close>
  apply (simp add: kf_id_def del: kf_of_op_id)
  apply transfer
  by (auto intro!: power_le_one onorm_pos_le onorm_id_le)

lemma kf_norm_id_eq1[simp]: \<open>kf_norm (kf_id :: ('a :: {chilbert_space, not_singleton},'a,unit) kraus_family) = 1\<close>
  by (auto intro!: antisym kf_norm_id_leq1 simp: kf_id_def simp del: kf_of_op_id)

lemma kf_operators_in_kf_id[simp]: \<open>kf_operators kf_id = (if (id_cblinfun::'a::chilbert_space\<Rightarrow>\<^sub>C\<^sub>L_)=0 then {} else {id_cblinfun::'a\<Rightarrow>\<^sub>C\<^sub>L_})\<close>
  by (simp add: kf_id_def del: kf_of_op_id)


instantiation kraus_family :: (chilbert_space, chilbert_space, type) scaleR begin
lift_definition scaleR_kraus_family :: \<open>real \<Rightarrow> ('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> ('a,'b,'x) kraus_family\<close> is
  \<open>\<lambda>r \<EE>. if r \<le> 0 then {} else (\<lambda>(E,x). (sqrt r *\<^sub>R E, x)) ` \<EE>\<close>
proof (rename_tac r \<EE>)
  fix r and \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close>
  assume asm: \<open>\<EE> \<in> Collect kraus_family\<close>
  define scaled where \<open>scaled = (\<lambda>(E, y). (sqrt r *\<^sub>R E, y)) ` \<EE>\<close>
  show \<open>(if r \<le> 0 then {} else scaled) \<in> Collect kraus_family\<close>
  proof (cases \<open>r > 0\<close>)
    case True
    obtain B where B: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>M \<subseteq> \<EE>\<close> and \<open>finite M\<close> for M
      using asm
      by (auto intro!: simp: kraus_family_def bdd_above_def)
    have \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R B\<close> if Mr\<EE>: \<open>M \<subseteq> scaled\<close> and \<open>finite M\<close> for M
    proof -
      define M' where \<open>M' = (\<lambda>(E,x). (E /\<^sub>R sqrt r, x)) ` M\<close>
      then have \<open>finite M'\<close>
        using that(2) by blast
      moreover have \<open>M' \<subseteq> \<EE>\<close>
        using Mr\<EE> True by (auto intro!: simp: M'_def scaled_def)
      ultimately have 1: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M'. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
        using B by auto
      have 2: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) = r *\<^sub>R (\<Sum>\<^sub>\<infinity>(E,x)\<in>M'. E* o\<^sub>C\<^sub>L E)\<close>
        apply (simp add: M'_def case_prod_unfold)
        apply (subst infsum_reindex)
        using True
        by (auto intro!: inj_onI simp: o_def infsum_scaleR_right
            simp flip: inverse_mult_distrib)
      show ?thesis
        using 1 2 True scaleR_le_cancel_left_pos by auto
    qed
    moreover have \<open>0 \<notin> fst ` scaled\<close> if \<open>r \<noteq> 0\<close>
      using asm that
      by (auto intro!: simp: scaled_def kraus_family_def)
    ultimately show ?thesis
      by (auto intro!: simp: kraus_family_def bdd_above_def)
  next
    case False
    then show ?thesis
      by (simp add: scaled_def)
  qed
qed
instance..
end

lemma kf_scale_apply:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kf_apply (r *\<^sub>R \<EE>) \<rho> = r *\<^sub>R kf_apply \<EE> \<rho>\<close>
proof (cases \<open>r > 0\<close>)
  case True
  then show ?thesis
    apply (simp add: scaleR_kraus_family.rep_eq kf_apply_def)
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI
        simp: kf_apply_def case_prod_unfold
        o_def sandwich_tc_scaleR_left cblinfun.scaleR_left infsum_scaleR_right)
next
  case False
  with assms show ?thesis
    by (simp add: kf_apply.rep_eq scaleR_kraus_family.rep_eq)
qed

lemma kf_bound_scale[simp]: \<open>kf_bound (c *\<^sub>R \<EE>) = c *\<^sub>R kf_bound \<EE>\<close> if \<open>c \<ge> 0\<close>
  apply (rule cblinfun_cinner_eqI)
  using that
  by (simp add: kf_bound_from_map cblinfun.scaleR_left kf_scale_apply scaleR_scaleC trace_tc_scaleC)

lemma kf_norm_scale[simp]: \<open>kf_norm (c *\<^sub>R \<EE>) = c * kf_norm \<EE>\<close> if \<open>c \<ge> 0\<close>
  by (simp add: kf_norm_def that)

lemma kf_of_op_apply: \<open>kf_apply (kf_of_op E) \<rho> = sandwich_tc E \<rho>\<close>
  by (simp add: kf_apply_def kf_of_op.rep_eq)

lemma kf_id_apply[simp]: \<open>kf_apply kf_id \<rho> = \<rho>\<close>
  by (simp add: kf_id_def kf_of_op_apply del: kf_of_op_id)

lemma kf_scale_apply_neg:
  assumes \<open>r \<le> 0\<close>
  shows \<open>kf_apply (r *\<^sub>R \<EE>) = 0\<close>
  apply (transfer fixing: r)
  using assms
  by (auto intro!: ext simp: scaleR_kraus_family.rep_eq kf_apply.rep_eq)

lemma kf_apply_0_left[iff]: \<open>kf_apply 0 \<rho> = 0\<close>
  apply (transfer' fixing: \<rho>)
  by simp

lemma kf_bound_of_op[simp]: \<open>kf_bound (kf_of_op A) = A* o\<^sub>C\<^sub>L A\<close>
  by (simp add: kf_bound_def kf_of_op.rep_eq infsum_in_finite)

lemma kf_bound_id[simp]: \<open>kf_bound kf_id = id_cblinfun\<close>
  by (simp add: kf_id_def del: kf_of_op_id)

subsection \<open>Filtering\<close>

lift_definition kf_filter :: \<open>('x \<Rightarrow> bool) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close> is
  \<open>\<lambda>(P::'x \<Rightarrow> bool) \<EE>. Set.filter (\<lambda>(E,x). P x) \<EE>\<close>
proof (rename_tac P \<EE>, rule CollectI)
  fix P \<EE>
  assume \<open>\<EE> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close>
    by simp
  then have \<open>bdd_above (sum (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
    by (simp add: kraus_family_def)
  then have \<open>bdd_above (sum (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Set.filter P \<EE>})\<close>
    apply (rule bdd_above_mono2)
    by auto
  moreover from \<open>kraus_family \<EE>\<close> have \<open>0 \<notin> fst ` Set.filter P \<EE>\<close>
    by (auto simp add: kraus_family_def)
  ultimately show \<open>kraus_family (Set.filter P \<EE>)\<close>
    by (simp add: kraus_family_def)
qed

lemma kf_filter_false[simp]: \<open>kf_filter (\<lambda>_. False) \<EE> = 0\<close>
  apply transfer by auto

lemma kf_filter_true[simp]: \<open>kf_filter (\<lambda>_. True) \<EE> = \<EE>\<close>
  apply transfer by auto

definition \<open>kf_apply_on \<EE> S = kf_apply (kf_filter (\<lambda>x. x \<in> S) \<EE>)\<close>
notation kf_apply_on ("_ *\<^sub>k\<^sub>r @_/ _" [71, 1000, 70] 70)

lemma kf_apply_on_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_apply_on \<EE> X \<rho> \<ge> 0\<close>
  by (simp add: kf_apply_on_def kf_apply_pos assms)

lemma kf_apply_on_bounded_clinear[bounded_clinear]:
  shows \<open>bounded_clinear (kf_apply_on \<EE> X)\<close>
  by (simp add: kf_apply_on_def kf_apply_bounded_clinear)

lemma kf_filter_twice:
  \<open>kf_filter P (kf_filter Q \<EE>) = kf_filter (\<lambda>x. P x \<and> Q x) \<EE>\<close>
  apply (transfer' fixing: P Q)
  by auto

lemma kf_apply_on_union_has_sum:
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>((\<lambda>X. kf_apply_on \<EE> X \<rho>) has_sum (kf_apply_on \<EE> (\<Union>F) \<rho>)) F\<close>
proof -
  define EE EEf where \<open>EE = Rep_kraus_family \<EE>\<close> and \<open>EEf X = Set.filter (\<lambda>(E,x). x\<in>X) EE\<close> for X
  have inj: \<open>inj_on snd (SIGMA X:F. EEf X)\<close>
    using assms by (force intro!: simp: inj_on_def disjnt_def EEf_def)
  have snd_Sigma: \<open>snd ` (SIGMA X:F. EEf X) = EEf (\<Union>F)\<close>
    apply (subgoal_tac \<open>\<And>a b x. (a, b) \<in> EE \<Longrightarrow> x \<in> F \<Longrightarrow> b \<in> x \<Longrightarrow> (a, b) \<in> snd ` (SIGMA X:F. Set.filter (\<lambda>(E, x). x \<in> X) EE)\<close>)
     apply (auto simp add: EEf_def)[1]
    by force
  have map'_infsum: \<open>kf_apply_on \<EE> X \<rho> = (\<Sum>\<^sub>\<infinity>(E, x)\<in>EEf X. sandwich_tc E \<rho>)\<close> for X
    by (simp add: kf_apply_on_def kf_apply.rep_eq EEf_def kf_filter.rep_eq EE_def case_prod_unfold)
  have has_sum: \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum (kf_apply_on \<EE> X \<rho>)) (EEf X)\<close> for X
    using kf_apply_has_sum[of \<rho> \<open>kf_filter (\<lambda>x. x \<in> X) \<EE>\<close>]
    by (simp add: kf_apply_on_def kf_filter.rep_eq EEf_def EE_def)
  then have \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum (kf_apply_on \<EE> (\<Union>F) \<rho>)) (snd ` (SIGMA X:F. EEf X))\<close>
    by (simp add: snd_Sigma)
  then have \<open>((\<lambda>(X,(E,x)). sandwich_tc E \<rho>) has_sum (kf_apply_on \<EE> (\<Union>F) \<rho>)) (SIGMA X:F. EEf X)\<close>
    apply (subst (asm) has_sum_reindex)
     apply (rule inj)
    by (simp add: o_def case_prod_unfold)
  then have \<open>((\<lambda>X. \<Sum>\<^sub>\<infinity>(E, x)\<in>EEf X. sandwich_tc E \<rho>) has_sum kf_apply_on \<EE> (\<Union>F) \<rho>) F\<close>
    by (rule has_sum_Sigma'_banach)
  then show \<open>((\<lambda>X. kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<EE> (\<Union>F) \<rho>) F\<close>
    by (auto intro: has_sum_cong[THEN iffD2, rotated] simp: map'_infsum)
qed

lemma kf_apply_on_empty[simp]: \<open>kf_apply_on E {} \<rho> = 0\<close>
  by (simp add: kf_apply_on_def)

lemma kf_apply_on_union_eqI:
  assumes \<open>\<And>X Y. (X,Y)\<in>F \<Longrightarrow> kf_apply_on \<EE> X \<rho> = kf_apply_on \<FF> Y \<rho>\<close>
  assumes \<open>\<And>X Y X' Y'. (X,Y)\<in>F \<Longrightarrow> (X',Y')\<in>F \<Longrightarrow> (X,Y)\<noteq>(X',Y') \<Longrightarrow> disjnt X X'\<close>
  assumes \<open>\<And>X Y X' Y'. (X,Y)\<in>F \<Longrightarrow> (X',Y')\<in>F \<Longrightarrow> (X,Y)\<noteq>(X',Y') \<Longrightarrow> disjnt Y Y'\<close>
  assumes XX: \<open>XX = \<Union>(fst ` F)\<close> and YY: \<open>YY = \<Union>(snd ` F)\<close>
  shows \<open>kf_apply_on \<EE> XX \<rho> = kf_apply_on \<FF> YY \<rho>\<close>
proof -
  define F' where \<open>F' = Set.filter (\<lambda>(X,Y). X\<noteq>{} \<and> Y\<noteq>{}) F\<close>
  have inj1: \<open>inj_on fst F'\<close>
    apply (rule inj_onI)
    using assms(2)
    unfolding F'_def
    by fastforce
  have inj2: \<open>inj_on snd F'\<close>
    apply (rule inj_onI)
    using assms(3)
    unfolding F'_def
    by fastforce
  have \<open>((\<lambda>X. kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<EE> XX \<rho>) (fst ` F)\<close>
    unfolding XX
    apply (rule kf_apply_on_union_has_sum)
    using assms(2) by force
  then have \<open>((\<lambda>X. kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<EE> XX \<rho>) (fst ` F')\<close>
  proof (rule has_sum_cong_neutral[OF _ _ refl, THEN iffD2, rotated -1])
    show \<open>kf_apply_on \<EE> X \<rho> = 0\<close> if \<open>X \<in> fst ` F' - fst ` F\<close> for X
      using that by (auto simp: F'_def)
    show \<open>kf_apply_on \<EE> X \<rho> = 0\<close> if \<open>X \<in> fst ` F - fst ` F'\<close> for X
    proof -
      from that obtain Y where \<open>(X,Y) \<in> F\<close> and \<open>X = {} \<or> Y = {}\<close>
        apply atomize_elim
        by (auto intro!: simp: F'_def)
      then consider (X) \<open>X = {}\<close> | (Y) \<open>Y = {}\<close>
        by auto
      then show ?thesis
      proof cases
        case X
        then show ?thesis
          by simp
      next
        case Y
        then have \<open>kf_apply_on \<FF> Y \<rho> = 0\<close>
          by simp
        then show ?thesis
          using \<open>(X, Y) \<in> F\<close> assms(1) by presburger
      qed
    qed
  qed
  then have sum1: \<open>((\<lambda>(X,Y). kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<EE> XX \<rho>) F'\<close>
    apply (subst (asm) has_sum_reindex)
    using inj1 by (auto intro!: simp: o_def case_prod_unfold)
  have \<open>((\<lambda>Y. kf_apply_on \<FF> Y \<rho>) has_sum kf_apply_on \<FF> YY \<rho>) (snd ` F)\<close>
    unfolding YY
    apply (rule kf_apply_on_union_has_sum)
    using assms(3) by force
  then have \<open>((\<lambda>Y. kf_apply_on \<FF> Y \<rho>) has_sum kf_apply_on \<FF> YY \<rho>) (snd ` F')\<close>
  proof (rule has_sum_cong_neutral[OF _ _ refl, THEN iffD2, rotated -1])
    show \<open>kf_apply_on \<FF> Y \<rho> = 0\<close> if \<open>Y \<in> snd ` F' - snd ` F\<close> for Y
      using that by (auto simp: F'_def)
    show \<open>kf_apply_on \<FF> Y \<rho> = 0\<close> if \<open>Y \<in> snd ` F - snd ` F'\<close> for Y
    proof -
      from that obtain X where \<open>(X,Y) \<in> F\<close> and \<open>X = {} \<or> Y = {}\<close>
        apply atomize_elim
        by (auto intro!: simp: F'_def)
      then consider (X) \<open>X = {}\<close> | (Y) \<open>Y = {}\<close>
        by auto
      then show ?thesis
      proof cases
        case Y
        then show ?thesis
          by simp
      next
        case X
        then have \<open>kf_apply_on \<EE> X \<rho> = 0\<close>
          by simp
        then show ?thesis
          using \<open>(X, Y) \<in> F\<close> assms(1) by simp
      qed
    qed
  qed
  then have \<open>((\<lambda>(X,Y). kf_apply_on \<FF> Y \<rho>) has_sum kf_apply_on \<FF> YY \<rho>) F'\<close>
    apply (subst (asm) has_sum_reindex)
    using inj2 by (auto intro!: simp: o_def case_prod_unfold)
  then have sum2: \<open>((\<lambda>(X,Y). kf_apply_on \<EE> X \<rho>) has_sum kf_apply_on \<FF> YY \<rho>) F'\<close>
    apply (rule has_sum_cong[THEN iffD1, rotated -1])
    using assms(1) by (auto simp: F'_def)
  from sum1 sum2 show ?thesis
    using has_sum_unique by blast
qed

lemma kf_apply_on_UNIV[simp]: \<open>kf_apply_on \<EE> UNIV = kf_apply \<EE>\<close>
  by (auto simp: kf_apply_on_def)

lemma kf_apply_on_CARD_1[simp]: \<open>(\<lambda>\<EE>. kf_apply_on \<EE> {x::_::CARD_1}) = kf_apply\<close>
  apply (subst asm_rl[of \<open>{x} = UNIV\<close>])
  by auto

(* lemma kf_apply_eqI_from_map':
  assumes \<open>\<And>x. kf_apply_on \<EE> {x} = kf_apply_on \<FF> {x}\<close>
  shows \<open>kf_apply \<EE> = kf_apply \<FF>\<close>
  apply (subst kf_apply_on_UNIV[symmetric])+
  apply (rule ext)
  apply (rule kf_apply_on_union_eqI[where F=\<open>range (\<lambda>x. ({x},{x}))\<close> and \<EE>=\<EE> and \<FF>=\<FF>])
  using assms by auto *)

lemma kf_apply_on_union_summable_on:
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>(\<lambda>X. kf_apply_on \<EE> X \<rho>) summable_on F\<close>
  using assms by (auto intro!: has_sum_imp_summable kf_apply_on_union_has_sum)

lemma kf_apply_on_union_infsum:
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>X\<in>F. kf_apply_on \<EE> X \<rho>) = kf_apply_on \<EE> (\<Union>F) \<rho>\<close>
  by (metis assms infsumI kf_apply_on_union_has_sum)


lemma kf_bound_filter:
  \<open>kf_bound (kf_filter P \<EE>) \<le> kf_bound \<EE>\<close>
proof (unfold kf_bound.rep_eq, rule infsum_mono_neutral_wot)
  show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (kf_filter P \<EE>))\<close>
    using Rep_kraus_family kraus_family_iff_summable by blast
  show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
    using Rep_kraus_family kraus_family_iff_summable by blast
  fix Ex :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c\<close>
  show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close>
    by simp
  show \<open>0 \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close>
    by (auto intro!: positive_cblinfun_squareI simp: case_prod_unfold)
  show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> 0\<close>
    if \<open>Ex \<in> Rep_kraus_family (kf_filter P \<EE>) - Rep_kraus_family \<EE>\<close>
    using that
    by (auto simp: kf_filter.rep_eq)
qed

lemma kf_norm_filter:
  \<open>kf_norm (kf_filter P \<EE>) \<le> kf_norm \<EE>\<close>
  unfolding kf_norm_def
  apply (rule norm_cblinfun_mono)
  by (simp_all add: kf_bound_filter)

lemma kf_domain_filter[simp]:
  \<open>kf_domain (kf_filter P E) = Set.filter P (kf_domain E)\<close>
  apply (transfer' fixing: P)
  by force

(* lemma kf_filter_remove0:
  \<open>kf_filter f (kf_remove_0 \<EE>) = kf_remove_0 (kf_filter f \<EE>)\<close>
  apply (transfer' fixing: f)
  by auto *)

lemma kf_filter_0_right[simp]: \<open>kf_filter P 0 = 0\<close>
  apply (transfer' fixing: P)
  by auto

lemma kf_apply_on_0_right[simp]: \<open>kf_apply_on \<EE> X 0 = 0\<close>
  by (simp add: kf_apply_on_def)

lemma kf_apply_on_0_left[simp]: \<open>kf_apply_on 0 X \<rho> = 0\<close>
  by (simp add: kf_apply_on_def)

lemma kf_apply_on_mono3:
  assumes \<open>\<rho> \<le> \<sigma>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<EE> *\<^sub>k\<^sub>r @X \<sigma>\<close>
  by (simp add: assms kf_apply_mono_right kf_apply_on_def)

lemma kf_apply_on_mono2:
  assumes \<open>X \<subseteq> Y\<close> and \<open>\<rho> \<ge> 0\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<EE> *\<^sub>k\<^sub>r @Y \<rho>\<close>
proof -
  wlog \<open>Y \<noteq> {}\<close>
    using assms(1) negation by auto
  have [simp]: \<open>X \<union> Y = Y\<close>
    using assms(1) by blast
  from kf_apply_on_union_infsum[where F=\<open>{X, Y-X}\<close> and \<EE>=\<EE> and \<rho>=\<rho>]
  have \<open>(\<Sum>X\<in>{X, Y - X}. \<EE> *\<^sub>k\<^sub>r @X \<rho>) = \<EE> *\<^sub>k\<^sub>r @Y \<rho>\<close>
    by (auto simp: disjnt_iff sum.insert)
  then have \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> + \<EE> *\<^sub>k\<^sub>r @(Y-X) \<rho> = \<EE> *\<^sub>k\<^sub>r @Y \<rho>\<close> 
    apply (subst (asm) sum.insert)
    using \<open>Y \<noteq> {}\<close>     
    by auto
  moreover have \<open>\<EE> *\<^sub>k\<^sub>r @(Y-X) \<rho> \<ge> 0\<close>
    by (simp add: assms(2) kf_apply_on_pos)
  ultimately show \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<EE> *\<^sub>k\<^sub>r @Y \<rho>\<close>
    by (metis le_add_same_cancel1)
qed

lemma kf_operators_filter: \<open>kf_operators (kf_filter P \<EE>) \<subseteq> kf_operators \<EE>\<close>
  apply (transfer' fixing: P)
  by auto

lemma kf_equal_if_filter_equal:
  assumes \<open>\<And>x. kf_filter ((=)x) \<EE> = kf_filter ((=)x) \<FF>\<close>
  shows \<open>\<EE> = \<FF>\<close>
  using assms
  apply transfer'
  by fastforce

subsection \<open>Equivalence\<close>

definition \<open>kf_eq_weak \<EE> \<FF> \<longleftrightarrow> kf_apply \<EE> = kf_apply \<FF>\<close>
definition \<open>kf_eq \<EE> \<FF> \<longleftrightarrow> (\<forall>x. kf_apply_on \<EE> {x} = kf_apply_on \<FF> {x})\<close>

open_bundle kraus_map_syntax begin
notation kf_eq_weak (infix "=\<^sub>k\<^sub>r" 50)
notation kf_eq (infix "\<equiv>\<^sub>k\<^sub>r" 50)
notation kf_apply (infixr \<open>*\<^sub>k\<^sub>r\<close> 70)
notation kf_apply_on ("_ *\<^sub>k\<^sub>r @_/ _" [71, 1000, 70] 70)
end

lemma kf_eq_weak_reflI[iff]: \<open>x =\<^sub>k\<^sub>r x\<close>
  by (simp add: kf_eq_weak_def)

lemma kf_eq_weak_refl0[iff]: \<open>0 =\<^sub>k\<^sub>r 0\<close>
  by (simp add: kf_eq_weak_def)

lemma kf_bound_cong:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_bound \<EE> = kf_bound \<FF>\<close>
  using assms by (auto intro!: cblinfun_cinner_eqI simp: kf_eq_weak_def kf_bound_from_map)

lemma kf_norm_cong:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_norm \<EE> = kf_norm \<FF>\<close>
  using assms
  by (simp add: kf_norm_def kf_bound_cong)


lemma kf_eq_weakI:
  assumes \<open>\<And>\<rho>. \<rho> \<ge> 0 \<Longrightarrow> \<EE> *\<^sub>k\<^sub>r \<rho> = \<FF> *\<^sub>k\<^sub>r \<rho>\<close>
  shows \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  unfolding kf_eq_weak_def
  apply (rule eq_from_separatingI)
     apply (rule separating_density_ops[where B=1])
  using assms by auto

lemma kf_eqI: 
  assumes \<open>\<And>x \<rho>. \<rho> \<ge> 0 \<Longrightarrow> \<EE> *\<^sub>k\<^sub>r @{x} \<rho> = \<FF> *\<^sub>k\<^sub>r @{x} \<rho>\<close>
  shows \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  using kf_eq_weakI
  using assms
  by (auto simp: kf_eq_weak_def kf_eq_def kf_apply_on_def)

(* lemma kf_norm_remove_0[simp]:
  \<comment> \<open>Logically belongs in a different section but uses lemmas from this section.\<close>
  \<open>kf_norm (kf_remove_0 \<EE>) = kf_norm \<EE>\<close>
  by (auto intro!: kf_eq_weakI kf_norm_cong) *)

lemma kf_eq_weak_trans[trans]:
  \<open>F =\<^sub>k\<^sub>r G \<Longrightarrow> G =\<^sub>k\<^sub>r H \<Longrightarrow> F =\<^sub>k\<^sub>r H\<close>
  by (simp add: kf_eq_weak_def)

lemma kf_apply_eqI:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r \<rho> = \<FF> *\<^sub>k\<^sub>r \<rho>\<close>
  using assms by (simp add: kf_eq_weak_def)

lemma kf_eq_imp_eq_weak:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  unfolding kf_eq_weak_def 
  apply (subst kf_apply_on_UNIV[symmetric])+
  apply (rule ext)
  apply (rule kf_apply_on_union_eqI[where F=\<open>range (\<lambda>x. ({x},{x}))\<close> and \<EE>=\<EE> and \<FF>=\<FF>])
  using assms by (auto simp: kf_eq_def)

lemma kf_filter_cong_eq[cong]:
  assumes \<open>\<EE> = \<FF>\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<EE> \<Longrightarrow> P x = Q x\<close>
  shows \<open>kf_filter P \<EE> = kf_filter Q \<FF>\<close>
  using assms
  apply transfer
  by (force simp: kraus_family_def)

lemma kf_filter_cong:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<EE> \<Longrightarrow> P x = Q x\<close>
  shows \<open>kf_filter P \<EE> \<equiv>\<^sub>k\<^sub>r kf_filter Q \<FF>\<close>
proof -
  have \<open>kf_apply (kf_filter (\<lambda>xa. xa = x \<and> P xa) \<EE>)
      = kf_apply (kf_filter (\<lambda>xa. xa = x \<and> Q xa) \<EE>)\<close> for x
  proof (cases \<open>x \<in> kf_domain \<EE>\<close>)
    case True
    with assms have \<open>P x = Q x\<close>
      by blast
    then have \<open>(\<lambda>xa. xa = x \<and> P xa) = (\<lambda>xa. xa = x \<and> Q xa)\<close>
      by auto
    then show ?thesis
      by presburger
  next
    case False
    then have \<open>kf_filter (\<lambda>xa. xa = x \<and> P xa) \<EE> = 0\<close>
      apply (transfer fixing: P x)
      by force
    have *: \<open>(\<Sum>\<^sub>\<infinity>E\<in>Set.filter (\<lambda>(E, xa). xa = x \<and> P xa) \<EE>. sandwich_tc (fst E) \<rho>) = 0\<close>
      if \<open>x \<notin> snd ` Set.filter (\<lambda>(E, x). E \<noteq> 0) \<EE>\<close> for \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close> and \<rho> P
      apply (rule infsum_0)
      using that
      by force
    have \<open>kf_apply (kf_filter (\<lambda>xa. xa = x \<and> P xa) \<EE>) = 0\<close> for P
      using False
      apply (transfer fixing: x P)
      using *
      by (auto intro!: ext simp: kraus_family_def image_iff)
    then show ?thesis
      by simp
  qed
  also have \<open>kf_apply (kf_filter (\<lambda>xa. xa = x \<and> Q xa) \<EE>)
           = kf_apply (kf_filter (\<lambda>xa. xa = x \<and> Q xa) \<FF>)\<close> for x
  proof (cases \<open>Q x\<close>)
    case True
    then have \<open>(z = x \<and> Q z) \<longleftrightarrow> (z = x)\<close> for z
      by auto
    with assms show ?thesis
      by (simp add: kf_eq_def kf_apply_on_def)
  next
    case False
    then have [simp]: \<open>(z = x \<and> Q z) \<longleftrightarrow> False\<close> for z
      by auto
    show ?thesis
      by (simp add: kf_eq_def kf_apply_on_def)
  qed
  finally show ?thesis
    by (simp add: kf_eq_def kf_apply_on_def kf_filter_twice)
qed


lemma kf_filter_cong_weak:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<EE> \<Longrightarrow> P x = Q x\<close>
  shows \<open>kf_filter P \<EE> =\<^sub>k\<^sub>r kf_filter Q \<FF>\<close>
  by (simp add: assms kf_eq_imp_eq_weak kf_filter_cong)

lemma kf_eq_refl[iff]: \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
  using kf_eq_def by blast

lemma kf_eq_trans[trans]:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<GG>\<close>
  shows \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<GG>\<close>
  by (metis assms(1) assms(2) kf_eq_def)

lemma kf_eq_sym[sym]:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
  by (metis assms kf_eq_def)

lemma kf_eq_weak_imp_eq_CARD_1:
  fixes \<EE> \<FF> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x::CARD_1) kraus_family\<close>
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  by (metis CARD_1_UNIV assms kf_eqI kf_eq_weak_def kf_apply_on_UNIV)

lemma kf_apply_on_eqI_filter:
  assumes \<open>kf_filter (\<lambda>x. x \<in> X) \<EE> \<equiv>\<^sub>k\<^sub>r kf_filter (\<lambda>x. x \<in> X) \<FF>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> = \<FF> *\<^sub>k\<^sub>r @X \<rho>\<close>
proof (rule kf_apply_on_union_eqI[where F=\<open>(\<lambda>x.({x},{x})) ` X\<close>])
  show \<open>(A, B) \<in> (\<lambda>x. ({x}, {x})) ` X \<Longrightarrow>
       (A', B') \<in> (\<lambda>x. ({x}, {x})) ` X \<Longrightarrow> (A, B) \<noteq> (A', B') \<Longrightarrow> disjnt A A'\<close>
    for A B A' B'
    by force
  show \<open>(A, B) \<in> (\<lambda>x. ({x}, {x})) ` X \<Longrightarrow>
       (A', B') \<in> (\<lambda>x. ({x}, {x})) ` X \<Longrightarrow> (A, B) \<noteq> (A', B') \<Longrightarrow> disjnt B B'\<close>
    for A B A' B'
    by force
  show \<open>X = \<Union> (fst ` (\<lambda>x. ({x}, {x})) ` X)\<close>
    by simp
  show \<open>X = \<Union> (snd ` (\<lambda>x. ({x}, {x})) ` X)\<close>
    by simp
  show \<open>\<EE> *\<^sub>k\<^sub>r @A \<rho> = \<FF> *\<^sub>k\<^sub>r @B \<rho>\<close> if \<open>(A, B) \<in> (\<lambda>x. ({x}, {x})) ` X\<close> for A B
  proof -
    from that obtain x where \<open>x \<in> X\<close> and A: \<open>A = {x}\<close> and B: \<open>B = {x}\<close>
      by blast
    from \<open>x \<in> X\<close> have *: \<open>(\<lambda>x'. x = x' \<and> x' \<in> X) = (\<lambda>x'. x' = x)\<close>
      by blast
    from assms have \<open>kf_filter ((=)x) (kf_filter (\<lambda>x. x \<in> X) \<EE>) =\<^sub>k\<^sub>r kf_filter ((=)x) (kf_filter (\<lambda>x. x \<in> X) \<FF>)\<close>
      by (simp add: kf_filter_cong_weak)
    then have \<open>kf_filter (\<lambda>x'. x'=x) \<EE> =\<^sub>k\<^sub>r kf_filter (\<lambda>x'. x'=x) \<FF>\<close>
      by (simp add: kf_filter_twice * cong del: kf_filter_cong_eq)
    then have \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> = \<FF> *\<^sub>k\<^sub>r @{x} \<rho>\<close>
      by (simp add: kf_apply_on_def kf_eq_weak_def)
    then show ?thesis
      by (simp add: A B)
  qed
qed

lemma kf_apply_on_eqI:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> = \<FF> *\<^sub>k\<^sub>r @X \<rho>\<close>
  apply (rule kf_apply_on_union_eqI[where F=\<open>(\<lambda>x.({x},{x})) ` X\<close>])
  using assms by (auto simp: kf_eq_def)

lemma kf_apply_eq0I:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r 0\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r \<rho> = 0\<close>
  using assms kf_eq_weak_def by force

lemma kf_eq_weak0_imp_kf_eq0:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r 0\<close>
  shows \<open>\<EE> \<equiv>\<^sub>k\<^sub>r 0\<close>
proof -
  have \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> = 0\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho> x
  proof -
    from assms have \<open>\<EE> *\<^sub>k\<^sub>r @UNIV \<rho> = 0\<close>
      by (simp add: kf_eq_weak_def)
    moreover have \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> \<le> \<EE> *\<^sub>k\<^sub>r @UNIV \<rho>\<close>
      apply (rule kf_apply_on_mono2)
      using that by auto
    moreover have \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> \<ge> 0\<close>
      using that
      by (simp add: kf_apply_on_pos)
    ultimately show ?thesis
      by (simp add: basic_trans_rules(24))
  qed
  then show ?thesis
    by (simp add: kf_eqI)
qed

lemma kf_apply_on_eq0I:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r 0\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> = 0\<close>
proof -
  from assms
  have \<open>\<EE> \<equiv>\<^sub>k\<^sub>r 0\<close>
    by (rule kf_eq_weak0_imp_kf_eq0)
  then have \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> = 0 *\<^sub>k\<^sub>r @X \<rho>\<close>
    by (intro kf_apply_on_eqI_filter kf_filter_cong refl)
  then show ?thesis
    by simp
qed

(* lemma kf_remove_0_eq_weak[iff]: \<open>kf_remove_0 \<EE> =\<^sub>k\<^sub>r \<EE>\<close>
  by (simp add: kf_eq_weak_def)

lemma kf_remove_0_eq[iff]: \<open>kf_remove_0 \<EE> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
  by (simp add: kf_eq_def kf_apply_on_def kf_filter_remove0) *)

lemma kf_filter_to_domain[simp]:
  \<open>kf_filter (\<lambda>x. x \<in> kf_domain \<EE>) \<EE> = \<EE>\<close>
  apply transfer
  by (force simp: kraus_family_def)

lemma kf_eq_0_iff_eq_0: \<open>E =\<^sub>k\<^sub>r 0 \<longleftrightarrow> E = 0\<close>
proof (rule iffI)
  assume asm: \<open>E =\<^sub>k\<^sub>r 0\<close>
  show \<open>E = 0\<close>
  proof (insert asm, unfold kf_eq_weak_def, transfer, rename_tac \<EE>)
    fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close>
    assume \<open>\<EE> \<in> Collect kraus_family\<close>
    then have \<open>kraus_family \<EE>\<close>
      by simp
    have summable1: \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on \<EE>\<close> for \<rho>
      apply (rule abs_summable_summable)
      using kf_apply_abs_summable[OF \<open>kraus_family \<EE>\<close>]
      by (simp add: case_prod_unfold)
    then have summable2: \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on \<EE>-{E}\<close> for E \<rho>
      apply (rule summable_on_subset_banach)
      by simp
    assume \<open>(\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>) = (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>E\<in>{}. sandwich_tc (fst E) \<rho>)\<close>
    then have sum0: \<open>(\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>) = 0\<close> for \<rho>
      apply simp by meson
    have sand_E\<rho>_0:  \<open>sandwich_tc (fst E) \<rho> = 0\<close> if \<open>E \<in> \<EE>\<close> and \<open>\<rho> \<ge> 0\<close> for E \<rho>
    proof (rule ccontr)
      assume E\<rho>_neq0: \<open>sandwich_tc (fst E) \<rho> \<noteq> 0\<close>
      have E\<rho>_geq0: \<open>sandwich_tc (fst E) \<rho> \<ge> 0\<close>
        by (simp add: \<open>0 \<le> \<rho>\<close> sandwich_tc_pos)
      have E\<rho>_ge0: \<open>sandwich_tc (fst E) \<rho> > 0\<close>
        using E\<rho>_neq0 E\<rho>_geq0 by order
      have \<open>(\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>) = (\<Sum>\<^sub>\<infinity>E\<in>\<EE>-{E}. sandwich_tc (fst E) \<rho>) + sandwich_tc (fst E) \<rho>\<close>
        apply (subst asm_rl[of \<open>\<EE> = insert E (\<EE>-{E})\<close>])
        using that apply blast
        apply (subst infsum_insert)
        by (auto intro!: summable2)
      also have \<open>\<dots> \<ge> 0 + sandwich_tc (fst E) \<rho>\<close> (is \<open>_ \<ge> \<dots>\<close>)
        by (simp add: \<open>0 \<le> \<rho>\<close> infsum_nonneg_traceclass sandwich_tc_pos)
      also have \<open>\<dots> > 0\<close> (is \<open>_ > \<dots>\<close>)
        using E\<rho>_ge0
        by simp
      ultimately have \<open>(\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>) > 0\<close>
        by simp
      then show False
        using sum0 by simp
    qed
    then have \<open>fst E = 0\<close> if \<open>E \<in> \<EE>\<close> for E
      apply (rule sandwich_tc_eq0_D[where B=1])
      using that by auto
    then show \<open>\<EE> = {}\<close>
      using \<open>kraus_family \<EE>\<close>
      by (auto simp: kraus_family_def)
  qed
next
  assume \<open>E = 0\<close>
  then show \<open>E =\<^sub>k\<^sub>r 0\<close>
    by simp
qed

lemma in_kf_domain_iff_apply_nonzero:
  \<open>x \<in> kf_domain \<EE> \<longleftrightarrow> kf_apply_on \<EE> {x} \<noteq> 0\<close>
proof -
  define \<EE>' where \<open>\<EE>' = Rep_kraus_family \<EE>\<close>
  have \<open>x \<notin> kf_domain \<EE> \<longleftrightarrow> (\<forall>(E,x')\<in>Rep_kraus_family \<EE>. x'\<noteq>x)\<close>
    by (force simp: kf_domain.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>(E,x')\<in>Rep_kraus_family (kf_filter (\<lambda>y. y=x) \<EE>). False)\<close>
    by (auto simp: kf_filter.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> Rep_kraus_family (kf_filter (\<lambda>y. y=x) \<EE>) = {}\<close>
    by (auto simp:)
  also have \<open>\<dots> \<longleftrightarrow> (kf_filter (\<lambda>y. y=x) \<EE>) = 0\<close>
    using Rep_kraus_family_inject zero_kraus_family.rep_eq by auto
  also have \<open>\<dots> \<longleftrightarrow> kf_apply (kf_filter (\<lambda>y. y=x) \<EE>) = 0\<close>
    apply (subst kf_eq_0_iff_eq_0[symmetric])
    by (simp add: kf_eq_weak_def)
  also have \<open>\<dots> \<longleftrightarrow> kf_apply_on \<EE> {x} = 0\<close>
    by (simp add: kf_apply_on_def)
  finally show ?thesis
    by auto
qed


lemma kf_domain_cong:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_domain \<EE> = kf_domain \<FF>\<close>
  apply (rule Set.set_eqI)
  using assms
  by (simp add: kf_eq_def in_kf_domain_iff_apply_nonzero)

lemma kf_eq_weak_sym[sym]:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<FF> =\<^sub>k\<^sub>r \<EE>\<close>
  by (metis assms kf_eq_weak_def)

lemma kf_eqI_from_filter_eq_weak:
  assumes \<open>\<And>x. kf_filter ((=) x) E =\<^sub>k\<^sub>r kf_filter ((=) x) F\<close>
  shows \<open>E \<equiv>\<^sub>k\<^sub>r F\<close>
  using assms
  apply (simp add: kf_eq_weak_def kf_eq_def kf_apply_on_def)
  apply (subst flip_eq_const)
  apply (subst flip_eq_const)
  by simp


lemma kf_eq_weak_from_separatingI:
  fixes E :: \<open>('q::chilbert_space,'r::chilbert_space,'x) kraus_family\<close>
    and F :: \<open>('q,'r,'y) kraus_family\<close>
  assumes \<open>separating_set (bounded_clinear :: (('q,'q) trace_class \<Rightarrow> ('r,'r) trace_class) \<Rightarrow> bool) S\<close>
  assumes \<open>\<And>\<rho>. \<rho> \<in> S \<Longrightarrow> E *\<^sub>k\<^sub>r \<rho> = F *\<^sub>k\<^sub>r \<rho>\<close>
  shows \<open>E =\<^sub>k\<^sub>r F\<close>
proof -
  have \<open>kf_apply E = kf_apply F\<close>
    by (metis assms(1) assms(2) kf_apply_bounded_clinear separating_set_def)
  then show ?thesis
    by (simp add: kf_eq_weakI)
qed

lemma kf_eq_weak_eq_trans[trans]: \<open>a =\<^sub>k\<^sub>r b \<Longrightarrow> b \<equiv>\<^sub>k\<^sub>r c \<Longrightarrow> a =\<^sub>k\<^sub>r c\<close>
  by (metis kf_eq_imp_eq_weak kf_eq_weak_def)

lemma kf_eq_eq_weak_trans[trans]: \<open>a \<equiv>\<^sub>k\<^sub>r b \<Longrightarrow> b =\<^sub>k\<^sub>r c \<Longrightarrow> a =\<^sub>k\<^sub>r c\<close>
  by (metis kf_eq_imp_eq_weak kf_eq_weak_def)

instantiation kraus_family :: (chilbert_space,chilbert_space,type) preorder begin
definition less_eq_kraus_family where \<open>\<EE> \<le> \<FF> \<longleftrightarrow> (\<forall>x. \<forall>\<rho>\<ge>0. kf_apply_on \<EE> {x} \<rho> \<le> kf_apply_on \<FF> {x} \<rho>)\<close>
definition less_kraus_family where \<open>\<EE> < \<FF> \<longleftrightarrow> \<EE> \<le> \<FF> \<and> \<not> \<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
lemma kf_antisym: \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF> \<longleftrightarrow> \<EE> \<le> \<FF> \<and> \<FF> \<le> \<EE>\<close>
  for \<EE> \<FF> :: \<open>('a, 'b, 'c) kraus_family\<close>
  by (smt (verit, ccfv_SIG) kf_apply_on_eqI kf_eqI less_eq_kraus_family_def order.refl
      order_antisym_conv)
instance
proof (intro_classes)
  fix \<EE> \<FF> \<GG> :: \<open>('a, 'b, 'c) kraus_family\<close>
  show \<open>(\<EE> < \<FF>) = (\<EE> \<le> \<FF> \<and> \<not> \<FF> \<le> \<EE>)\<close>
    using kf_antisym less_kraus_family_def by auto
  show \<open>\<EE> \<le> \<EE>\<close>
    using less_eq_kraus_family_def by auto
  show \<open>\<EE> \<le> \<FF> \<Longrightarrow> \<FF> \<le> \<GG> \<Longrightarrow> \<EE> \<le> \<GG>\<close>
    by (meson basic_trans_rules(23) less_eq_kraus_family_def)
qed
end

lemma kf_apply_on_mono1: 
  assumes \<open>\<EE> \<le> \<FF>\<close> and \<open>\<rho> \<ge> 0\<close> 
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<FF> *\<^sub>k\<^sub>r @X \<rho>\<close>
proof -
  have [simp]: \<open>\<Union>((\<lambda>x. {x}) ` X) = X\<close> for X :: \<open>'c set\<close>
    by auto
  have \<open>((\<lambda>X. \<EE> *\<^sub>k\<^sub>r @X \<rho>) has_sum \<EE> *\<^sub>k\<^sub>r @(\<Union>((\<lambda>x. {x}) ` X)) \<rho>) ((\<lambda>x. {x}) ` X)\<close>
    for \<EE> :: \<open>('a, 'b, 'c) kraus_family\<close> and X
    apply (rule kf_apply_on_union_has_sum)
    by auto
  then have sum: \<open>((\<lambda>X. \<EE> *\<^sub>k\<^sub>r @X \<rho>) has_sum \<EE> *\<^sub>k\<^sub>r @X \<rho>) ((\<lambda>x. {x}) ` X)\<close>
    for \<EE> :: \<open>('a, 'b, 'c) kraus_family\<close> and X
    by simp
  from assms
  have leq: \<open>\<EE> *\<^sub>k\<^sub>r @{x} \<rho> \<le> \<FF> *\<^sub>k\<^sub>r @{x} \<rho>\<close> for x
    by (simp add: less_eq_kraus_family_def)
  show ?thesis
    using sum sum apply (rule has_sum_mono_traceclass)
    using leq by fast
qed

lemma kf_apply_mono_left: \<open>\<EE> \<le> \<FF> \<Longrightarrow> \<rho> \<ge> 0 \<Longrightarrow> \<EE> *\<^sub>k\<^sub>r \<rho> \<le> \<FF> *\<^sub>k\<^sub>r \<rho>\<close>
  by (metis kf_apply_on_UNIV kf_apply_on_mono1)

lemma kf_apply_mono:
  assumes \<open>\<rho> \<ge> 0\<close>
  assumes \<open>\<EE> \<le> \<FF>\<close> and \<open>\<rho> \<le> \<sigma>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r \<rho> \<le> \<FF> *\<^sub>k\<^sub>r \<sigma>\<close>
  by (meson assms(1,2,3) basic_trans_rules(23) kf_apply_mono_left kf_apply_mono_right)

lemma kf_apply_on_mono:
  assumes \<open>\<rho> \<ge> 0\<close>
  assumes \<open>\<EE> \<le> \<FF>\<close> and \<open>X \<subseteq> Y\<close> and \<open>\<rho> \<le> \<sigma>\<close>
  shows \<open>\<EE> *\<^sub>k\<^sub>r @X \<rho> \<le> \<FF> *\<^sub>k\<^sub>r @Y \<sigma>\<close>
  apply (rule order.trans)
  using assms(2,1) apply (rule kf_apply_on_mono1)
  apply (rule order.trans)
  using assms(3,1) apply (rule kf_apply_on_mono2)
  using assms(4) by (rule kf_apply_on_mono3)

lemma kf_one_dim_is_id[simp]:
  fixes \<EE> :: \<open>('a::one_dim, 'a::one_dim, 'x) kraus_family\<close>
  shows \<open>\<EE> =\<^sub>k\<^sub>r kf_norm \<EE> *\<^sub>R kf_id\<close>
proof (rule kf_eq_weakI)
  fix t :: \<open>('a, 'a) trace_class\<close>
  have \<EE>1pos[iff]: \<open>\<EE> *\<^sub>k\<^sub>r 1 \<ge> 0\<close>
    apply (rule kf_apply_pos)
    by (metis one_cinner_one one_dim_iso_of_one one_dim_scaleC_1 tc_butterfly_pos trace_tc_butterfly
          trace_tc_one_dim_iso)

  have \<EE>t: \<open>\<EE> *\<^sub>k\<^sub>r t = trace_tc t *\<^sub>C (\<EE> *\<^sub>k\<^sub>r 1)\<close> if \<open>NO_MATCH 1 t\<close>for t
    by (metis kf_apply_scaleC one_dim_scaleC_1 trace_tc_one_dim_iso)
  have \<open>kf_bound \<EE> = norm (\<EE> *\<^sub>k\<^sub>r 1) *\<^sub>R id_cblinfun\<close>
  proof (rule cblinfun_cinner_eqI)
    fix h :: 'a
    assume \<open>norm h = 1\<close>
    have \<open>h \<bullet>\<^sub>C kf_bound \<EE> h = one_dim_iso h * cnj (one_dim_iso h) * one_dim_iso (\<EE> *\<^sub>k\<^sub>r 1)\<close>
      apply (subst kf_bound_from_map)
      by (simp add: \<EE>t cinner_scaleR_right cblinfun.scaleR_left cdot_square_norm one_dim_tc_butterfly)
    also have 1: \<open>\<dots> = one_dim_iso (\<EE> *\<^sub>k\<^sub>r 1)\<close>
      by (smt (verit, best) \<open>norm h = 1\<close> cinner_simps(5) cnorm_eq_1 id_apply more_arith_simps(6) mult.commute
          one_dim_iso_def one_dim_iso_id one_dim_iso_is_of_complex one_dim_scaleC_1)
    also have \<open>\<dots> = trace_tc (\<EE> *\<^sub>k\<^sub>r 1)\<close>
      by simp
    also have \<open>\<dots> = norm (\<EE> *\<^sub>k\<^sub>r 1)\<close>
      apply (subst norm_tc_pos)
      by (simp_all add: \<EE>1pos)
    also have \<open>\<dots> = h \<bullet>\<^sub>C (norm (\<EE> *\<^sub>k\<^sub>r 1) *\<^sub>R id_cblinfun *\<^sub>V h)\<close>
      by (metis \<open>norm h = 1\<close> cblinfun.scaleR_left cinner_commute cinner_scaleR_left cnorm_eq_1
          complex_cnj_complex_of_real id_cblinfun.rep_eq mult.commute mult_cancel_right1)
    finally show \<open>h \<bullet>\<^sub>C (kf_bound \<EE> *\<^sub>V h) = h \<bullet>\<^sub>C (norm (\<EE> *\<^sub>k\<^sub>r 1) *\<^sub>R id_cblinfun *\<^sub>V h)\<close>
      by -
  qed
  then have \<open>kf_norm \<EE> = cmod (one_dim_iso (\<EE> *\<^sub>k\<^sub>r 1))\<close>
    by (simp add: kf_norm_def)
  then have norm: \<open>complex_of_real (kf_norm \<EE>) = one_dim_iso (\<EE> *\<^sub>k\<^sub>r 1)\<close>
  using norm_tc_pos by fastforce

  have \<open>(one_dim_iso (\<EE> *\<^sub>k\<^sub>r t) :: complex) = one_dim_iso t * one_dim_iso (\<EE> *\<^sub>k\<^sub>r 1)\<close>
  by (metis (mono_tags, lifting) kf_apply_scaleC of_complex_one_dim_iso one_dim_iso_is_of_complex
      one_dim_iso_scaleC one_dim_scaleC_1 scaleC_one_dim_is_times)
  also have \<open>\<dots> = one_dim_iso t * complex_of_real (kf_norm \<EE>)\<close>
    by (simp add: norm)
  also have \<open>\<dots> = one_dim_iso (kf_norm \<EE> *\<^sub>R t)\<close>
    by (simp add: scaleR_scaleC)
  also have \<open>\<dots> = one_dim_iso (kf_norm \<EE> *\<^sub>R kf_id *\<^sub>k\<^sub>r t)\<close>
    by (simp add: kf_scale_apply)
  finally show \<open>\<EE> *\<^sub>k\<^sub>r t = kf_norm \<EE> *\<^sub>R kf_id *\<^sub>k\<^sub>r t\<close>
    using one_dim_iso_inj by blast
qed


subsection \<open>Mapping and flattening\<close>

definition kf_similar_elements :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close> where
  \<comment> \<open>All elements of the Kraus family that are equal up to rescaling (and belong to the same output)\<close>
  \<open>kf_similar_elements \<EE> E = {(F,x) \<in> Rep_kraus_family \<EE>. (\<exists>r>0. E = r *\<^sub>R F)}\<close>

definition kf_element_weight where
  \<comment> \<open>The total weight (norm of the square) of all similar elements\<close>
  \<open>kf_element_weight \<EE> E = (\<Sum>\<^sub>\<infinity>(F,_)\<in>kf_similar_elements \<EE> E. norm (F* o\<^sub>C\<^sub>L F))\<close>

lemma kf_element_weight_geq0[simp]: \<open>kf_element_weight \<EE> E \<ge> 0\<close>
  by (auto intro!: infsum_nonneg simp: kf_element_weight_def)

lemma kf_similar_elements_abs_summable:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows \<open>(\<lambda>(F,_). F* o\<^sub>C\<^sub>L F) abs_summable_on (kf_similar_elements \<EE> E)\<close>
proof (cases \<open>E = 0\<close>)
  case True
  show ?thesis
    apply (rule summable_on_cong[where g=\<open>\<lambda>_. 0\<close>, THEN iffD2])
    by (auto simp: kf_similar_elements_def True)
next
  case False
  then obtain \<psi> where E\<psi>: \<open>E \<psi> \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_eqI)
  define \<phi> where \<open>\<phi> = ((norm E)\<^sup>2 / (\<psi> \<bullet>\<^sub>C (E* *\<^sub>V E *\<^sub>V \<psi>))) *\<^sub>C \<psi>\<close>
  have normFF: \<open>norm (fst Fx* o\<^sub>C\<^sub>L fst Fx) = \<psi> \<bullet>\<^sub>C (fst Fx* *\<^sub>V fst Fx *\<^sub>V \<phi>)\<close>
    if \<open>Fx \<in> kf_similar_elements \<EE> E\<close> for Fx
  proof -
    define F where \<open>F = fst Fx\<close>
    have \<open>\<exists>ra. x = (ra * r) *\<^sub>R x\<close> if \<open>r > 0\<close> for r and x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      apply (rule exI[of _ \<open>inverse r\<close>])
      using that 
      by auto
    with that obtain r where FE: \<open>F = r *\<^sub>R E\<close>
      apply atomize_elim
      by (auto simp: kf_similar_elements_def F_def)
    show \<open>norm (F* o\<^sub>C\<^sub>L F) = \<psi> \<bullet>\<^sub>C (F* *\<^sub>V F *\<^sub>V \<phi>)\<close>
      by (simp add: False \<phi>_def FE cblinfun.scaleR_left cblinfun.scaleR_right
          cblinfun.scaleC_left cblinfun.scaleC_right cinner_adj_right E\<psi>)
  qed

  have \<psi>\<phi>_mono: \<open>mono (\<lambda>A. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>))\<close>
  proof (rule monoI)
    fix A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    assume \<open>A \<le> B\<close>
    then have \<open>B - A \<ge> 0\<close>
      by auto
    then have \<open>\<psi> \<bullet>\<^sub>C ((B - A) *\<^sub>V \<psi>) \<ge> 0\<close>
      by (simp add: cinner_pos_if_pos)
    then have \<open>\<psi> \<bullet>\<^sub>C ((B - A) *\<^sub>V \<phi>) \<ge> 0\<close>
      by (auto intro!: mult_nonneg_nonneg
          simp: \<phi>_def cblinfun.scaleC_right divide_inverse cinner_adj_right power2_eq_square)
    then show \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>) \<le> \<psi> \<bullet>\<^sub>C (B *\<^sub>V \<phi>)\<close>
      by (simp add: cblinfun.diff_left cinner_diff_right)
  qed

  have \<psi>\<phi>_linear: \<open>clinear (\<lambda>A. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>))\<close>
    by (auto intro!: clinearI simp: cblinfun.add_left cinner_add_right)

  from Rep_kraus_family[of \<EE>]
  have \<open>bdd_above ((\<lambda>M. \<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) ` {M. finite M \<and> M \<subseteq> Rep_kraus_family \<EE>})\<close>
    by (simp add: kraus_family_def)
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. F* o\<^sub>C\<^sub>L F) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    apply (rule bdd_above_mono2[OF _ _ order.refl])
    by (auto simp: kf_similar_elements_def)
  then have \<open>bdd_above ((\<lambda>A. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>)) ` (\<lambda>M. \<Sum>(F, x)\<in>M. F* o\<^sub>C\<^sub>L F) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    by (rule bdd_above_image_mono[OF \<psi>\<phi>_mono])
  then have \<open>bdd_above ((\<lambda>M. \<psi> \<bullet>\<^sub>C ((\<Sum>(F, x)\<in>M. F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    by (simp add: image_image)
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. \<psi> \<bullet>\<^sub>C ((F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    unfolding case_prod_beta
    by (subst complex_vector.linear_sum[OF \<psi>\<phi>_linear, symmetric])
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. complex_of_real (norm (F* o\<^sub>C\<^sub>L F))) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    apply (rule bdd_above_mono2[OF _ subset_refl])
    unfolding case_prod_unfold
    apply (subst sum.cong[OF refl normFF])
    by auto
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. norm (F* o\<^sub>C\<^sub>L F)) ` {M. M \<subseteq> kf_similar_elements \<EE> E \<and> finite M})\<close>
    by (auto simp add: bdd_above_def case_prod_unfold less_eq_complex_def)
  then have \<open>(\<lambda>(F,_). norm (F* o\<^sub>C\<^sub>L F)) summable_on (kf_similar_elements \<EE> E)\<close>
    apply (rule nonneg_bdd_above_summable_on[rotated])
    by auto
  then show \<open>(\<lambda>(F,_). F* o\<^sub>C\<^sub>L F) abs_summable_on kf_similar_elements \<EE> E\<close>
    by (simp add: case_prod_unfold)
qed

lemma kf_similar_elements_kf_operators:
  assumes \<open>(F,x) \<in> kf_similar_elements \<EE> E\<close>
  shows \<open>F \<in> span (kf_operators \<EE>)\<close>
  using assms
  unfolding kf_similar_elements_def
  apply (transfer' fixing: E F x)
  by (metis (no_types, lifting) Product_Type.Collect_case_prodD fst_conv image_eqI span_base)

lemma kf_element_weight_neq0: \<open>kf_element_weight \<EE> E \<noteq> 0\<close> 
  if \<open>(E,x) \<in> Rep_kraus_family \<EE>\<close> and \<open>E \<noteq> 0\<close>
proof -
  have 1: \<open>(E, x) \<in> kf_similar_elements \<EE> E\<close>
    by (auto intro!: exI[where x=1] simp: kf_similar_elements_def that)

  have \<open>kf_element_weight \<EE> E = (\<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements \<EE> E. (norm F)\<^sup>2)\<close>
    by (simp add: kf_element_weight_def)
  moreover have \<open>\<dots> \<ge> (\<Sum>\<^sub>\<infinity>(F, x)\<in>{(E,x)}. (norm F)\<^sup>2)\<close> (is \<open>_ \<ge> \<dots>\<close>)
    apply (rule infsum_mono_neutral)
    using kf_similar_elements_abs_summable
    by (auto intro!: 1 simp: that case_prod_unfold)
  moreover have \<open>\<dots> > 0\<close>
    using that by simp
  ultimately show ?thesis
    by auto
qed


lemma kf_element_weight_0_left[simp]: \<open>kf_element_weight 0 E = 0\<close>
  by (simp add: kf_element_weight_def kf_similar_elements_def zero_kraus_family.rep_eq)

lemma kf_element_weight_0_right[simp]: \<open>kf_element_weight E 0 = 0\<close>
  by (auto intro!: infsum_0 simp add: kf_element_weight_def kf_similar_elements_def)

lemma kf_element_weight_scale:
  assumes \<open>r > 0\<close>
  shows \<open>kf_element_weight \<EE> (r *\<^sub>R E) = kf_element_weight \<EE> E\<close>
proof -
  have [simp]: \<open>(\<exists>r'>0. r *\<^sub>R E = r' *\<^sub>R F) \<longleftrightarrow> (\<exists>r'>0. E = r' *\<^sub>R F)\<close> for F
    apply (rule Ex_iffI[where f=\<open>\<lambda>r'. r' /\<^sub>R r\<close> and g=\<open>\<lambda>r'. r *\<^sub>R r'\<close>])
     apply (smt (verit, best) assms divideR_right real_scaleR_def scaleR_scaleR scaleR_simps(7)
        zero_le_scaleR_iff) 
    using assms by force
  show ?thesis
    using assms
    by (simp add: kf_similar_elements_def kf_element_weight_def)
qed

lemma kf_element_weight_kf_operators:
  assumes \<open>kf_element_weight \<EE> E \<noteq> 0\<close>
  shows \<open>E \<in> span (kf_operators \<EE>)\<close>
proof -
  from assms
  have \<open>(\<Sum>\<^sub>\<infinity>(F, _)\<in>{(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> (\<exists>r>0. E = r *\<^sub>R F)}. norm (F* o\<^sub>C\<^sub>L F)) \<noteq> 0\<close>
    by (simp add: kf_element_weight_def kf_similar_elements_def)
  then obtain F x r where \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> and \<open>E = r *\<^sub>R F\<close>
    by (smt (verit, ccfv_SIG) Product_Type.Collect_case_prodD infsum_0)
  then have \<open>F \<in> kf_operators \<EE>\<close>
    by (metis fst_conv image_eqI kf_operators.rep_eq)
  with \<open>E = r *\<^sub>R F\<close> show ?thesis
    by (simp add: span_clauses)
qed


lemma kf_map_aux:
  fixes f :: \<open>'x \<Rightarrow> 'y\<close> and \<EE> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
  defines \<open>B \<equiv> kf_bound \<EE>\<close>
  defines \<open>filtered y \<equiv> kf_filter (\<lambda>x. f x = y) \<EE>\<close>
  defines \<open>flattened \<equiv> {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (filtered y) E \<and> E \<noteq> 0}\<close>
  defines \<open>good \<equiv> (\<lambda>(E,y). (norm E)\<^sup>2 = kf_element_weight (filtered y) E \<and> E \<noteq> 0)\<close>
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close> (is ?has_sum)
    and \<open>snd ` (SIGMA (E, y):Collect good. kf_similar_elements (filtered y) E)
      = {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close> (is ?snd_sigma)
    and \<open>inj_on snd (SIGMA p:Collect good. kf_similar_elements (filtered (snd p)) (fst p))\<close> (is ?inj_snd)
proof -
  have E_inv: \<open>kf_element_weight (filtered y) E \<noteq> 0\<close> if \<open>good (E,y)\<close> for E y
    using that by (auto simp:  good_def)

  show snd_sigma: ?snd_sigma
  proof (intro Set.set_eqI iffI)
    fix Fx
    assume asm: \<open>Fx \<in> snd ` (SIGMA (E, y):Collect good. kf_similar_elements (filtered y) E)\<close>
    obtain F x where Fx_def: \<open>Fx = (F,x)\<close> by fastforce
    with asm obtain E y where Fx_rel_E: \<open>(F, x) \<in> kf_similar_elements (filtered y) E\<close> and \<open>good (E,y)\<close>
      by auto
    then have \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close>
      by (simp add: kf_similar_elements_def filtered_def kf_filter.rep_eq)
    from Fx_rel_E obtain r where \<open>E = r *\<^sub>R F\<close>
      by (smt (verit) kf_similar_elements_def mem_Collect_eq prod.sel(1) split_def)
    with \<open>good (E,y)\<close> have \<open>F \<noteq> 0\<close>
      by (simp add: good_def)
    with \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> show \<open>Fx \<in> {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
      by (simp add: Fx_def)
  next
    fix Fx
    assume asm: \<open>Fx \<in> {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
    obtain F x where Fx_def: \<open>Fx = (F,x)\<close> by fastforce
    from asm have Fx_\<EE>: \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> and [simp]: \<open>F \<noteq> 0\<close>
      by (auto simp: Fx_def)
    have weight_fx_F_not0: \<open>kf_element_weight (filtered (f x)) F \<noteq> 0\<close>
      using Fx_\<EE> by (simp_all add: filtered_def kf_filter.rep_eq kf_element_weight_neq0)
    then have weight_fx_F_pos: \<open>kf_element_weight (filtered (f x)) F > 0\<close>
      using kf_element_weight_geq0 
      by (metis less_eq_real_def)
    define E where \<open>E = (sqrt (kf_element_weight (filtered (f x)) F) / norm F) *\<^sub>R F\<close>
    have [simp]: \<open>E \<noteq> 0\<close>
      by (auto intro!: weight_fx_F_not0 simp: E_def)
    have E_F_same: \<open>kf_element_weight (filtered (f x)) E = kf_element_weight (filtered (f x)) F\<close>
      by (simp add: E_def kf_element_weight_scale weight_fx_F_pos)
    have \<open>good (E, f x)\<close>
      apply (simp add: good_def E_F_same)
      by (simp add: E_def)
    have 1: \<open>sqrt (kf_element_weight (filtered (f x)) F) / norm F > 0\<close>
      by (auto intro!: divide_pos_pos weight_fx_F_pos)
    then have \<open>(F, x) \<in> kf_similar_elements (filtered (f x)) E\<close>
      by (auto intro!: \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> simp: kf_similar_elements_def E_def \<open>F \<noteq> 0\<close>
         filtered_def kf_filter.rep_eq)
    with \<open>good (E,f x)\<close>
    show \<open>Fx \<in> snd ` (SIGMA (E, y):Collect good. kf_similar_elements (filtered y) E)\<close>
      by (force intro!: image_eqI[where x=\<open>((E,()),F,x)\<close>] simp: Fx_def filtered_def)
  qed

  show inj_snd: ?inj_snd
  proof (rule inj_onI)
    fix EFx EFx' :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'y) \<times> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x\<close>
    assume EFx_in: \<open>EFx \<in> (SIGMA p:Collect good. kf_similar_elements (filtered (snd p)) (fst p))\<close>
      and EFx'_in: \<open>EFx' \<in> (SIGMA p:Collect good. kf_similar_elements (filtered (snd p)) (fst p))\<close>
    assume snd_eq: \<open>snd EFx = snd EFx'\<close>
    obtain E F x y where [simp]: \<open>EFx = ((E,y),F,x)\<close>
      by (metis (full_types) old.unit.exhaust surj_pair)
    obtain E' F' x' y' where [simp]: \<open>EFx' = ((E',y'),(F',x'))\<close> 
      by (metis (full_types) old.unit.exhaust surj_pair)
    from snd_eq have [simp]: \<open>F' = F\<close> and [simp]: \<open>x' = x\<close>
      by auto
    from EFx_in have \<open>good (E,y)\<close> and F_rel_E: \<open>(F, x) \<in> kf_similar_elements (filtered y) E\<close>
      by auto
    from EFx'_in have \<open>good (E',y')\<close> and F_rel_E': \<open>(F, x) \<in> kf_similar_elements (filtered y') E'\<close>
      by auto
    from \<open>good (E,y)\<close> have \<open>E \<noteq> 0\<close>
      by (simp add: good_def)
    from \<open>good (E',y')\<close> have \<open>E' \<noteq> 0\<close>
      by (simp add: good_def)
    from F_rel_E obtain r where ErF: \<open>E = r *\<^sub>R F\<close> and \<open>r > 0\<close>
      by (auto intro!: simp: kf_similar_elements_def)
    from F_rel_E' obtain r' where E'rF: \<open>E' = r' *\<^sub>R F\<close> and \<open>r' > 0\<close>
      by (auto intro!: simp: kf_similar_elements_def)

    from EFx_in have \<open>y = f x\<close>
      by (auto intro!: simp: filtered_def kf_similar_elements_def kf_filter.rep_eq)
    moreover from EFx'_in have \<open>y' = f x'\<close>
      by (auto intro!: simp: filtered_def kf_similar_elements_def kf_filter.rep_eq)
    ultimately have [simp]: \<open>y = y'\<close>
      by simp

    define r'' where \<open>r'' = r' / r\<close>
    with E'rF ErF \<open>E \<noteq> 0\<close>
    have E'_E: \<open>E' = r'' *\<^sub>R E\<close>
      by auto
    with \<open>r' > 0\<close> \<open>r > 0\<close> \<open>E' \<noteq> 0\<close>
    have [simp]: \<open>r'' > 0\<close>
      by (fastforce simp: r''_def)
    from E'_E have \<open>kf_element_weight (filtered y') E' = kf_element_weight (filtered y) E\<close>
      by (simp add: kf_element_weight_scale)
    with \<open>good (E,y)\<close> \<open>good (E',y')\<close> have \<open>(norm E')\<^sup>2 = (norm E)\<^sup>2\<close>
      by (auto intro!: simp: good_def)
    with \<open>E' = r'' *\<^sub>R E\<close>
    have \<open>E' = E\<close>
      using \<open>0 < r''\<close> by force
    then show \<open>EFx = EFx'\<close>
      by simp
  qed

  show ?has_sum
  proof (unfold has_sum_in_cweak_operator_topology_pointwise, intro allI)
    fix \<psi> \<phi> :: 'a
    define B' where \<open>B' = \<psi> \<bullet>\<^sub>C B \<phi>\<close>
    define normal where \<open>normal E y = E /\<^sub>R sqrt (kf_element_weight (filtered y) E)\<close> for E y
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(F,x). F* o\<^sub>C\<^sub>L F) (Rep_kraus_family \<EE>) B\<close>
      using B_def kf_bound_has_sum by blast
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B') (Rep_kraus_family \<EE>)\<close>
      by (simp add: B'_def has_sum_in_cweak_operator_topology_pointwise case_prod_unfold)
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B') {(F,x)\<in>Rep_kraus_family \<EE>. F \<noteq> 0}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by (auto simp: zero_cblinfun_wot_def)
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B')
           (snd ` (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E))\<close>
      by (simp add: snd_sigma)
    then have \<open>((\<lambda>((E,x), (F,y)). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B')
       (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E)\<close>
      apply (subst (asm) has_sum_reindex)
      by (auto intro!: inj_on_def inj_snd simp: o_def case_prod_unfold)
    then have sum1: \<open>((\<lambda>((E,y), (F,x)). (norm F)\<^sup>2 *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>)) has_sum B')
        (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E)\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      apply (subgoal_tac \<open>\<And>b aa ba r.
       (r * norm aa)\<^sup>2 = kf_element_weight (filtered b) (complex_of_real r *\<^sub>C aa) \<Longrightarrow>
       aa \<noteq> 0 \<Longrightarrow>
       0 < r \<Longrightarrow>
       (complex_of_real (norm aa))\<^sup>2 *
       (inverse (complex_of_real (sqrt (kf_element_weight (filtered b) (complex_of_real r *\<^sub>C aa)))) *
        (inverse (complex_of_real (sqrt (kf_element_weight (filtered b) (complex_of_real r *\<^sub>C aa)))) *
         (complex_of_real r * complex_of_real r))) \<noteq>
       1 \<Longrightarrow>
       is_orthogonal \<psi> (aa* *\<^sub>V aa *\<^sub>V \<phi>)\<close>)
      apply (auto intro!: simp: good_def normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          kf_similar_elements_def kf_element_weight_scale 
          cblinfun.scaleC_left cblinfun.scaleC_right cinner_scaleC_right scaleR_scaleC)[1]
      by (smt (verit) Extra_Ordered_Fields.mult_sign_intros(5) Extra_Ordered_Fields.sign_simps(5) inverse_eq_iff_eq left_inverse more_arith_simps(11) of_real_eq_0_iff of_real_mult power2_eq_square power_inverse real_inv_sqrt_pow2 zero_less_norm_iff)
    then have \<open>((\<lambda>(E,y). \<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements (filtered y) E.
                (norm F)\<^sup>2 *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>)) has_sum B') (Collect good)\<close>
      by (auto intro!: has_sum_Sigma'_banach simp add: case_prod_unfold)
    then have \<open>((\<lambda>(E,y). (\<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements (filtered y) E.
                              (norm F)\<^sup>2) *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>))
                        has_sum B') (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply simp
      by (smt (verit) Complex_Vector_Spaces.infsum_scaleR_left cblinfun.scaleR_left infsum_cong split_def)
    then have \<open>((\<lambda>(E,y). kf_element_weight (filtered y) E *\<^sub>R 
                              (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>)) has_sum B') (Collect good)\<close>
      by (simp add: kf_element_weight_def)
    then have \<open>((\<lambda>(E,_). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum B') (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      by (auto  intro!: field_class.field_inverse
          simp add: normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          cblinfun.scaleR_left scaleR_scaleC
          simp flip: inverse_mult_distrib semigroup_mult.mult_assoc of_real_mult
          split!: prod.split)
    then have \<open>((\<lambda>(E,_). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum B') flattened\<close>
      by (simp add: flattened_def good_def)
    then show \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C ((case x of (E, uu_) \<Rightarrow> E* o\<^sub>C\<^sub>L E) *\<^sub>V \<phi>)) has_sum B') flattened\<close>
      by (simp add: case_prod_unfold)
  qed
qed


lift_definition kf_map :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a, 'b, 'y) kraus_family\<close> is
  \<open>\<lambda>f \<EE>. {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E \<and> E \<noteq> 0}\<close>
proof (rename_tac f \<EE>)
  fix f :: \<open>'x \<Rightarrow> 'y\<close> and \<EE> :: \<open>('a, 'b, 'x) kraus_family\<close>
  define filtered flattened B 
    where \<open>filtered y = kf_filter (\<lambda>x. f x = y) \<EE>\<close>
      and \<open>flattened = {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (filtered y) E \<and> E \<noteq> 0}\<close>
      and \<open>B = kf_bound \<EE>\<close> 
    for y

  from kf_map_aux[of f \<EE>]
  have bound_has_sum: \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close>
    by (simp_all add: filtered_def flattened_def B_def)

  have nonzero: \<open>0 \<notin> fst ` flattened\<close>
    by (auto intro!: simp: flattened_def)

  from bound_has_sum nonzero show \<open>flattened \<in> Collect kraus_family\<close>
    by (auto simp: kraus_family_iff_summable summable_on_in_def)
qed

lemma
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows kf_apply_map[simp]: \<open>kf_apply (kf_map f \<EE>) = kf_apply \<EE>\<close>
    and kf_map_bound: \<open>kf_bound (kf_map f \<EE>) = kf_bound \<EE>\<close>
    and kf_map_norm[simp]: \<open>kf_norm (kf_map f \<EE>) = kf_norm \<EE>\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  define filtered good flattened B normal \<sigma>
    where \<open>filtered y = kf_filter (\<lambda>x. f x = y) \<EE>\<close>
      and \<open>good = (\<lambda>(E,y). (norm E)\<^sup>2 = kf_element_weight (filtered y) E \<and> E \<noteq> 0)\<close>
      and \<open>flattened = {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (filtered y) E \<and> E \<noteq> 0}\<close>
      and \<open>B = kf_bound \<EE>\<close> 
      and \<open>normal E y = E /\<^sub>R sqrt (kf_element_weight (filtered y) E)\<close>
      and \<open>\<sigma> = \<EE> *\<^sub>k\<^sub>r \<rho>\<close>
    for E y
  have E_inv: \<open>kf_element_weight (filtered y) E \<noteq> 0\<close> if \<open>good (E,y)\<close> for E y
    using that by (auto simp:  good_def)

  from kf_map_aux[of f \<EE>]
  have snd_sigma: \<open>snd ` (SIGMA (E, y):Collect good. kf_similar_elements (filtered y) E)
      = {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
    and inj_snd: \<open>inj_on snd (SIGMA p:Collect good. kf_similar_elements (filtered (snd p)) (fst p))\<close>
    and bound_has_sum: \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close>
    by (simp_all add: good_def filtered_def flattened_def B_def)

  show \<open>kf_apply (kf_map f \<EE>) \<rho> = \<sigma>\<close>
  proof -
    have \<open>(\<lambda>(F,x). sandwich_tc F \<rho>) summable_on Rep_kraus_family \<EE>\<close>
      using kf_apply_summable by (simp add: case_prod_unfold)
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>) (Rep_kraus_family \<EE>)\<close>
      by (simp add: \<sigma>_def kf_apply_def split_def)
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>) {(F,x)\<in>Rep_kraus_family \<EE>. F \<noteq> 0}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by auto
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>)
           (snd ` (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E))\<close>
      by (simp add: snd_sigma)
    then have \<open>((\<lambda>((E,x), (F,y)). sandwich_tc F \<rho>) has_sum \<sigma>)
       (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E)\<close>
      apply (subst (asm) has_sum_reindex)
      by (auto intro!: inj_on_def inj_snd simp: o_def case_prod_unfold)
    then have sum1: \<open>((\<lambda>((E,y), (F,_)). (norm F)\<^sup>2 *\<^sub>R sandwich_tc (normal E y) \<rho>) has_sum \<sigma>)
                (SIGMA (E,y):Collect good. kf_similar_elements (filtered y) E)\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      apply (subgoal_tac \<open>\<And>b a r. (r * norm a)\<^sup>2 = kf_element_weight (filtered b) a \<Longrightarrow>
       a \<noteq> 0 \<Longrightarrow> 0 < r \<Longrightarrow> ((norm a)\<^sup>2 * inverse (kf_element_weight (filtered b) a) * r\<^sup>2) *\<^sub>R sandwich_tc a \<rho> = sandwich_tc a \<rho> \<close>)
       apply (auto intro!: real_vector.scale_one simp: good_def normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          kf_similar_elements_def kf_element_weight_scale)[1]
      by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(5) linorder_not_less more_arith_simps(11) mult_eq_0_iff norm_le_zero_iff order.refl power2_eq_square right_inverse scale_one)
    then have \<open>((\<lambda>(E,y). \<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements (filtered y) E.
                (norm F)\<^sup>2 *\<^sub>R sandwich_tc (normal E y) \<rho>) has_sum \<sigma>) (Collect good)\<close>
      by (auto intro!: has_sum_Sigma'_banach simp add: case_prod_unfold)
    then have \<open>((\<lambda>(E,y). (\<Sum>\<^sub>\<infinity>(F, x)\<in>kf_similar_elements (filtered y) E. (norm F)\<^sup>2) *\<^sub>R sandwich_tc (normal E y) \<rho>)
                        has_sum \<sigma>) (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply simp
      by (smt (verit) Complex_Vector_Spaces.infsum_scaleR_left cblinfun.scaleR_left infsum_cong split_def)
    then have \<open>((\<lambda>(E,y). kf_element_weight (filtered y) E *\<^sub>R sandwich_tc (normal E y) \<rho>) has_sum \<sigma>) (Collect good)\<close>
      by (simp add: kf_element_weight_def)
    then have \<open>((\<lambda>(E,_). sandwich_tc E \<rho>) has_sum \<sigma>) (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      by (auto intro!: simp: normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv)
    then have \<open>((\<lambda>(E,_). sandwich_tc E \<rho>) has_sum \<sigma>) flattened\<close>
      by (simp add: flattened_def good_def)
    then show \<open>kf_map f \<EE> *\<^sub>k\<^sub>r \<rho> = \<sigma>\<close>
      by (simp add: kf_apply.rep_eq kf_map.rep_eq flattened_def
          case_prod_unfold infsumI filtered_def)
  qed

  from bound_has_sum show bound: \<open>kf_bound (kf_map f \<EE>) = B\<close>
    apply (simp add: kf_bound_def flattened_def kf_map.rep_eq B_def filtered_def)
    using has_sum_in_infsum_in has_sum_in_unique hausdorff_cweak_operator_topology summable_on_in_def
    by blast

  from bound show \<open>kf_norm (kf_map f \<EE>) = kf_norm \<EE>\<close>
    by (simp add: kf_norm_def B_def)
qed

abbreviation \<open>kf_flatten \<equiv> kf_map (\<lambda>_. ())\<close>

text \<open>Like \<^const>\<open>kf_map\<close>, but with a much simpler definition.
      However, only makes sense for injective functions.\<close>
lift_definition kf_map_inj :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a, 'b, 'y) kraus_family\<close> is
  \<open>\<lambda>f \<EE>. (\<lambda>(E,x). (E, f x)) ` \<EE>\<close>
proof (rule CollectI, rule kraus_familyI, rename_tac f \<EE>)
  fix f :: \<open>'x \<Rightarrow> 'y\<close> and \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close>
  then obtain B where B: \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>F \<in> {F. finite F \<and> F \<subseteq> \<EE>}\<close> for F
    by (auto simp: kraus_family_def bdd_above_def)
  show \<open>bdd_above ((\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> (\<lambda>(E, x). (E, f x)) ` \<EE>})\<close>
  proof (rule bdd_aboveI2)
    fix F assume \<open>F \<in> {F. finite F \<and> F \<subseteq> (\<lambda>(E, x). (E, f x)) ` \<EE>}\<close>
    then obtain F' where \<open>finite F'\<close> and \<open>F' \<subseteq> \<EE>\<close> and F_F': \<open>F = (\<lambda>(E, x). (E, f x)) ` F'\<close>
      and inj: \<open>inj_on (\<lambda>(E, x). (E, f x)) F'\<close>
      by (metis (no_types, lifting) finite_imageD mem_Collect_eq subset_image_inj)
    have \<open>(\<Sum>(E, x)\<in>F'. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
      by (auto intro!: B \<open>finite F'\<close> \<open>F' \<subseteq> \<EE>\<close>)
    moreover have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> (\<Sum>(E, x)\<in>F'. E* o\<^sub>C\<^sub>L E)\<close>
      apply (simp add: F_F' inj sum.reindex)
      by (simp add: case_prod_beta)
    ultimately show \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
      by simp
  qed
  from \<open>\<EE> \<in> Collect kraus_family\<close>
  show \<open>0 \<notin> fst ` (\<lambda>(E,x). (E, f x)) ` \<EE>\<close>
    by (force simp: kraus_family_def)
qed                            

lemma kf_element_weight_map_inj:
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_element_weight (kf_map_inj f \<EE>) E = kf_element_weight \<EE> E\<close>
proof -
  wlog \<open>E \<noteq> 0\<close>
    using negation by simp
  have inj2: \<open>inj_on (\<lambda>(E, x). (E, f x)) {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> (\<exists>r>0. E = r *\<^sub>R F)}\<close>
  proof (rule inj_onI)
    fix Fy Gx :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> 'a\<close>
    obtain F y G x where [simp]: \<open>Fy = (F,y)\<close> \<open>Gx = (G,x)\<close>
      by (auto simp: prod_eq_iff)
    assume \<open>Fy \<in> {(F, y). (F, y) \<in> Rep_kraus_family \<EE> \<and> (\<exists>r>0. E = r *\<^sub>R F)}\<close> and \<open>Gx \<in> {(G, x). (G, x) \<in> Rep_kraus_family \<EE> \<and> (\<exists>r>0. E = r *\<^sub>R G)}\<close>
    then have Fy_\<EE>: \<open>(F, y) \<in> Rep_kraus_family \<EE>\<close> and ErF: \<open>\<exists>r>0. E = r *\<^sub>R F\<close> and Gx_\<EE>: \<open>(G, x) \<in> Rep_kraus_family \<EE>\<close> and ErG: \<open>\<exists>r>0. E = r *\<^sub>R G\<close>
      by auto
    from ErF \<open>E \<noteq> 0\<close> have \<open>F \<noteq> 0\<close>
      by auto
    with Fy_\<EE> have \<open>y \<in> kf_domain \<EE>\<close>
      by (force simp add: kf_domain.rep_eq)
    from ErG \<open>E \<noteq> 0\<close> have \<open>G \<noteq> 0\<close>
      by auto
    with Gx_\<EE> have \<open>x \<in> kf_domain \<EE>\<close>
      by (force simp add: kf_domain.rep_eq)
    assume \<open>(case Fy of (F, y) \<Rightarrow> (F, f y)) = (case Gx of (G, x) \<Rightarrow> (G, f x))\<close>
    then have [simp]: \<open>F = G\<close> and \<open>f y = f x\<close>
      by auto
    with assms \<open>x \<in> kf_domain \<EE>\<close> \<open>y \<in> kf_domain \<EE>\<close>
    have \<open>y = x\<close>
      by (simp add: inj_onD)
    then show \<open>Fy = Gx\<close>
      by simp
  qed

  have \<open>kf_element_weight (kf_map_inj f \<EE>) E
     = (\<Sum>\<^sub>\<infinity>(F, _)\<in>{(F, x). (F, x) \<in> (\<lambda>(E,x). (E, f x)) ` Rep_kraus_family \<EE> \<and> (\<exists>r>0. E = r *\<^sub>R F)}. (norm F)\<^sup>2)\<close>
    by (simp add: kf_element_weight_def assms kf_similar_elements_def kf_map_inj.rep_eq)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F, _)\<in>(\<lambda>(E,x). (E, f x)) ` {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> (\<exists>r>0. E = r *\<^sub>R F)}. (norm F)\<^sup>2)\<close>
    apply (rule arg_cong2[where f=infsum])
    by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F, _)\<in>{(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> (\<exists>r>0. E = r *\<^sub>R F)}. (norm F)\<^sup>2)\<close>
    apply (subst infsum_reindex)
     apply (rule inj2)
    using assms by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = kf_element_weight \<EE> E\<close>
    by (simp add: kf_element_weight_def assms kf_similar_elements_def)
  finally show ?thesis
    by -
qed

lemma kf_eq_weak_kf_map_left: \<open>kf_map f F =\<^sub>k\<^sub>r G\<close> if \<open>F =\<^sub>k\<^sub>r G\<close>
  using that by (simp add: kf_eq_weak_def kf_apply_map)

lemma kf_eq_weak_kf_map_right: \<open>F =\<^sub>k\<^sub>r kf_map f G\<close> if \<open>F =\<^sub>k\<^sub>r G\<close>
  using that by (simp add: kf_eq_weak_def kf_apply_map)

lemma kf_filter_map:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows \<open>kf_filter P (kf_map f \<EE>) = kf_map f (kf_filter (\<lambda>x. P (f x)) \<EE>)\<close>
proof -
  have \<open>(E,x) \<in> Set.filter (\<lambda>(E, y). P y) {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E \<and> E \<noteq> 0}
   \<longleftrightarrow> (E,x) \<in> {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. f x = y) (kf_filter (\<lambda>x. P (f x)) \<EE>)) E \<and> E \<noteq> 0}\<close>
    for E x and \<EE> :: \<open>('a, 'b, 'x) kraus_family\<close>
  proof (cases \<open>P x\<close>)
    case True
    then show ?thesis
      apply (simp add: kf_filter_twice)
      by (metis (mono_tags, lifting) kf_filter_cong_eq)
  next
    case False
    then have [simp]: \<open>(\<lambda>z. f z = x \<and> P (f z)) = (\<lambda>_. False)\<close>
      by auto
    from False show ?thesis
      apply (simp add: kf_filter_twice)
      by (smt (verit, ccfv_SIG) kf_element_weight_0_left kf_filter_cong_eq kf_filter_false norm_eq_zero zero_eq_power2)
  qed
  then show ?thesis
    apply (transfer' fixing: P f)
    by blast
qed

lemma kf_filter_map_inj:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows \<open>kf_filter P (kf_map_inj f \<EE>) = kf_map_inj f (kf_filter (\<lambda>x. P (f x)) \<EE>)\<close>
  apply (transfer' fixing: P f)
  by (force simp: case_prod_beta image_iff)

lemma kf_map_kf_map_inj_comp:
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_map g (kf_map_inj f \<EE>) = kf_map (g o f) \<EE>\<close>
proof (transfer' fixing: f g \<EE>)
  from assms
  have \<open>inj_on f (kf_domain (kf_filter (\<lambda>x. g (f x) = y) \<EE>))\<close> for y
    apply (rule inj_on_subset) by force
  then show \<open>{(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. g x = y) (kf_map_inj f \<EE>)) E \<and> E \<noteq> 0} =
             {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. (g \<circ> f) x = y) \<EE>) E \<and> E \<noteq> 0}\<close>
    by (simp add: kf_filter_map_inj kf_element_weight_map_inj assms)
qed

(* lemma kf_similar_elements_remove_0[simp]: \<open>kf_similar_elements (kf_remove_0 \<EE>) E = kf_similar_elements \<EE> E\<close> if \<open>E \<noteq> 0\<close>
  using that by (auto simp: kf_similar_elements_def kf_remove_0.rep_eq)

lemma kf_element_weight_remove_0[simp]: \<open>kf_element_weight (kf_remove_0 \<EE>) E = kf_element_weight \<EE> E\<close>
  apply (cases \<open>E = 0\<close>)
   apply (simp add: kf_element_weight_0_right)
  by (simp add: kf_element_weight_def) *)

lemma kf_element_weight_eqweak0:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r 0\<close>
  shows \<open>kf_element_weight \<EE> E = 0\<close>
  apply (subst kf_eq_0_iff_eq_0[THEN iffD1])
  using assms by auto

lemma kf_map_inj_kf_map_comp:
  assumes \<open>inj_on g (f ` kf_domain \<EE>)\<close>
  shows \<open>kf_map_inj g (kf_map f \<EE>) = kf_map (g o f) \<EE>\<close>
proof (transfer' fixing: f g \<EE>, rule Set.set_eqI)
  fix Ex :: \<open>'d \<Rightarrow>\<^sub>C\<^sub>L 'e \<times> 'b\<close>
  obtain E x where [simp]: \<open>Ex = (E,x)\<close>
    by (auto simp: prod_eq_iff)
  have \<open>Ex \<in> (\<lambda>(E, x). (E, g x)) ` {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E \<and> E \<noteq> 0} \<longleftrightarrow>
    (\<exists>y. x = g y \<and> (norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E) \<and> E \<noteq> 0\<close>
    by auto
  also have \<open>\<dots> \<longleftrightarrow> (norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>z. g (f z) = x) \<EE>) E \<and> E \<noteq> 0\<close>
  proof (rule iffI)
    assume asm: \<open>(\<exists>y. x = g y \<and> (norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E) \<and> E \<noteq> 0\<close>
    then obtain y where xy: \<open>x = g y\<close> and weight: \<open>(norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E\<close>
      by auto
    from asm have \<open>E \<noteq> 0\<close>
      by simp
    with weight have \<open>\<not> kf_filter (\<lambda>x. f x = y) \<EE> =\<^sub>k\<^sub>r 0\<close>
      using kf_element_weight_eqweak0 by fastforce
    then have \<open>\<not> kf_filter (\<lambda>x. f x = y \<and> x \<in> kf_domain \<EE>) \<EE> =\<^sub>k\<^sub>r 0\<close>
      by (smt (verit, del_insts) kf_eq_0_iff_eq_0 kf_filter_cong_eq)
    then have \<open>(\<lambda>x. f x = y \<and> x \<in> kf_domain \<EE>) \<noteq> (\<lambda>z. False)\<close>
      using kf_filter_false[of \<EE>]
      by (metis kf_eq_weak_refl0)
    then have yf\<EE>: \<open>y \<in> f ` kf_domain \<EE>\<close>
      by fast
    have \<open>kf_element_weight ((kf_filter (\<lambda>x. f x = y) \<EE>)) E = kf_element_weight ((kf_filter (\<lambda>z. g (f z) = x) \<EE>)) E\<close>
      apply (rule arg_cong2[where f=kf_element_weight, OF _ refl])
      apply (rule kf_filter_cong_eq[OF refl])
      using yf\<EE> assms xy
      by (meson image_eqI inj_onD)
    then
    have \<open>kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E = kf_element_weight (kf_filter (\<lambda>z. g (f z) = x) \<EE>) E\<close>
      by simp
    with weight \<open>E \<noteq> 0\<close>
    show \<open>(norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>z. g (f z) = x) \<EE>) E \<and> E \<noteq> 0\<close>
      by simp
  next
    assume asm: \<open>(norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>z. g (f z) = x) \<EE>) E \<and> E \<noteq> 0\<close>
    then have \<open>E \<noteq> 0\<close>
      by simp
    from asm have \<open>\<not> kf_filter (\<lambda>z. g (f z) = x) \<EE> =\<^sub>k\<^sub>r 0\<close>
      using kf_element_weight_eqweak0 by fastforce
    then have \<open>\<not> kf_filter (\<lambda>z. g (f z) = x \<and> z \<in> kf_domain \<EE>) \<EE> =\<^sub>k\<^sub>r 0\<close>
      by (smt (verit, ccfv_threshold) kf_eq_0_iff_eq_0 kf_filter_cong_eq)
    then have \<open>(\<lambda>z. g (f z) = x \<and> z \<in> kf_domain \<EE>) \<noteq> (\<lambda>z. False)\<close>
      using kf_filter_false[of \<EE>]
      by (metis kf_eq_weak_refl0)
    then obtain z where \<open>z \<in> kf_domain \<EE>\<close> and gfz: \<open>g (f z) = x\<close>
      using kf_filter_false[of \<EE>]
      by auto
    have \<open>kf_element_weight ((kf_filter (\<lambda>x. f x = f z) \<EE>)) E = kf_element_weight ((kf_filter (\<lambda>z. g (f z) = x) \<EE>)) E\<close>
      apply (rule arg_cong2[where f=kf_element_weight, OF _ refl])
      apply (rule kf_filter_cong_eq[OF refl])
      using assms gfz \<open>z \<in> kf_domain \<EE>\<close>
      by (metis image_eqI inj_onD)
    with asm \<open>E \<noteq> 0\<close>
    show \<open>(\<exists>y. x = g y \<and> (norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E) \<and> E \<noteq> 0\<close>
      by (auto intro!: exI[of _ \<open>f z\<close>] simp flip: gfz)
  qed
  also have \<open>\<dots> \<longleftrightarrow> Ex \<in> {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. (g \<circ> f) x = y) \<EE>) E \<and> E \<noteq> 0}\<close>
    by simp
  finally show \<open>Ex \<in> (\<lambda>(E, x). (E, g x)) ` {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. f x = y) \<EE>) E \<and> E \<noteq> 0} \<longleftrightarrow>
         Ex \<in> {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kf_element_weight (kf_filter (\<lambda>x. (g \<circ> f) x = y) \<EE>) E \<and> E \<noteq> 0}\<close>
    by -
qed

lemma kf_apply_map_inj[simp]:
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r \<rho> = \<EE> *\<^sub>k\<^sub>r \<rho>\<close>
proof -
  define EE where \<open>EE = Set.filter (\<lambda>(E,x). E\<noteq>0) (Rep_kraus_family \<EE>)\<close>
  have \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>(E, x). (E, f x)) ` Rep_kraus_family \<EE>. sandwich_tc (fst E) \<rho>)\<close>
    by (simp add: kf_apply.rep_eq kf_map_inj.rep_eq)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>(E, x). (E, f x)) ` EE. sandwich_tc (fst E) \<rho>)\<close>
    apply (rule infsum_cong_neutral)
    by (force simp: EE_def)+
  also have \<open>\<dots> = infsum ((\<lambda>E. sandwich_tc (fst E) \<rho>) \<circ> (\<lambda>(E, x). (E, f x))) EE\<close>
    apply (rule infsum_reindex)
    apply (subgoal_tac \<open>\<And>aa ba b. \<forall>x\<in>Rep_kraus_family \<EE>. \<forall>y\<in>Rep_kraus_family \<EE>. f (snd x) = f (snd y) \<longrightarrow> snd x = snd y \<Longrightarrow>
       (aa, ba) \<in> Rep_kraus_family \<EE> \<Longrightarrow> f b = f ba \<Longrightarrow> (aa, b) \<in> Rep_kraus_family \<EE> \<Longrightarrow> aa \<noteq> 0 \<Longrightarrow> b = ba\<close>)
    using assms
    by (auto intro!: simp: inj_on_def kf_domain.rep_eq EE_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>EE. sandwich_tc E \<rho>)\<close>
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>)\<close>
    apply (rule infsum_cong_neutral)
    by (auto simp: EE_def)
  also have \<open>\<dots> = \<EE> *\<^sub>k\<^sub>r \<rho>\<close>
    by (metis (no_types, lifting) infsum_cong kf_apply.rep_eq prod.case_eq_if)
  finally show \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r \<rho> = \<EE> *\<^sub>k\<^sub>r \<rho>\<close>
    by -
qed

lemma kf_map_inj_eq_kf_map:
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_map_inj f \<EE> \<equiv>\<^sub>k\<^sub>r kf_map f \<EE>\<close>
proof (rule kf_eqI)
  fix x \<rho>
  define \<EE>fx where \<open>\<EE>fx = kf_filter (\<lambda>z. f z = x) \<EE>\<close>
  from assms have inj_\<EE>fx: \<open>inj_on f (kf_domain \<EE>fx)\<close>
    by (simp add: inj_on_def kf_domain.rep_eq \<EE>fx_def kf_filter.rep_eq)
  have \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r @{x} \<rho> = kf_filter (\<lambda>z. z=x) (kf_map_inj f \<EE>) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_apply_on_def)
  also have \<open>\<dots> = kf_map_inj f \<EE>fx *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_apply t \<rho>\<close>])
    unfolding \<EE>fx_def
    apply (transfer' fixing: f)
    by force
  also have \<open>\<dots> = \<EE>fx *\<^sub>k\<^sub>r \<rho>\<close>
    using inj_\<EE>fx by (rule kf_apply_map_inj)
  also have \<open>\<dots> = kf_map f (kf_filter (\<lambda>z. f z = x) \<EE>) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: \<EE>fx_def)
  also have \<open>\<dots> = kf_apply (kf_filter (\<lambda>xa. xa = x) (kf_map f \<EE>)) \<rho>\<close>
    apply (subst kf_filter_map)
    by simp
  also have \<open>\<dots> = kf_map f \<EE> *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by (simp add: kf_apply_on_def)
  finally show \<open>kf_map_inj f \<EE> *\<^sub>k\<^sub>r @{x} \<rho> = kf_map f \<EE> *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by -
qed

lemma kf_map_inj_id[simp]: \<open>kf_map_inj id \<EE> = \<EE>\<close>
  apply transfer' by simp

lemma kf_map_id: \<open>kf_map id \<EE> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
  by (metis inj_on_id kf_eq_sym kf_map_inj_eq_kf_map kf_map_inj_id)

lemma kf_map_inj_bound[simp]:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_bound (kf_map_inj f \<EE>) = kf_bound \<EE>\<close>
  by (metis assms kf_eq_imp_eq_weak kf_map_inj_eq_kf_map kf_bound_cong kf_map_bound)

lemma kf_map_inj_norm[simp]:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_norm (kf_map_inj f \<EE>) = kf_norm \<EE>\<close>
  using assms kf_eq_imp_eq_weak kf_map_inj_eq_kf_map kf_norm_cong by fastforce

lemma kf_map_cong_weak:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_map f \<EE> =\<^sub>k\<^sub>r kf_map g \<FF>\<close>
  by (metis assms kf_eq_weak_def kf_apply_map)

lemma kf_flatten_cong_weak:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_flatten \<EE> =\<^sub>k\<^sub>r kf_flatten \<FF>\<close>
  using assms by (rule kf_map_cong_weak)

lemma kf_flatten_cong:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_flatten \<EE> \<equiv>\<^sub>k\<^sub>r kf_flatten \<FF>\<close>
  by (simp add: assms kf_eq_weak_imp_eq_CARD_1 kf_flatten_cong_weak)

lemma kf_map_twice:
  \<open>kf_map f (kf_map g \<EE>) \<equiv>\<^sub>k\<^sub>r kf_map (f \<circ> g) \<EE>\<close>
  apply (rule kf_eqI)
  by (simp add: kf_filter_map kf_apply_on_def)

lemma kf_map_cong:
  assumes \<open>\<And>x. x \<in> kf_domain \<EE> \<Longrightarrow> f x = g x\<close>
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_map f \<EE> \<equiv>\<^sub>k\<^sub>r kf_map g \<FF>\<close>
proof -
  have \<open>kf_filter (\<lambda>y. f y = x) \<EE> =\<^sub>k\<^sub>r kf_filter (\<lambda>y. g y = x) \<FF>\<close> for x
    apply (rule kf_filter_cong_weak)
    using assms by auto
  then have \<open>\<EE> *\<^sub>k\<^sub>r @(f-`{x}) \<rho> = \<FF> *\<^sub>k\<^sub>r @(g-`{x}) \<rho>\<close> for x \<rho>
    by (auto intro!: kf_apply_eqI simp add: kf_apply_on_def)
  then show ?thesis
    apply (rule_tac kf_eqI)
    by (simp add: kf_apply_on_def kf_filter_map)
qed

lemma kf_map_inj_cong_eq:
  assumes \<open>\<And>x. x \<in> kf_domain \<EE> \<Longrightarrow> f x = g x\<close>
  assumes \<open>\<EE> = \<FF>\<close>
  shows \<open>kf_map_inj f \<EE> = kf_map_inj g \<FF>\<close>
  using assms
  apply transfer'
  by force

(* lemma kf_map_remove_0[simp]:
  \<open>kf_map f (kf_remove_0 \<EE>) = kf_map f \<EE>\<close>
  apply (transfer' fixing: f)
  by (simp add: kf_map.rep_eq kf_filter_remove0)

lemma kf_domain_remove_0[simp]: \<open>kf_domain (kf_remove_0 E) = kf_domain E\<close>
  apply transfer'
  by auto

lemma kf_remove_0_map[simp]:
  \<open>kf_remove_0 (kf_map f \<EE>) = kf_map f \<EE>\<close>
  apply (transfer' fixing: f)
  by auto *)



lemma kf_domain_map[simp]:
  \<open>kf_domain (kf_map f \<EE>) = f ` kf_domain \<EE>\<close>
proof (rule Set.set_eqI, rule iffI)
  fix x assume \<open>x \<in> kf_domain (kf_map f \<EE>)\<close>
  then obtain a where \<open>(norm a)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>xa. f xa = x) \<EE>) a\<close> and \<open>a \<noteq> 0\<close>
    by (auto intro!: simp: kf_domain.rep_eq kf_map.rep_eq)
  then have \<open>kf_element_weight (kf_filter (\<lambda>xa. f xa = x) \<EE>) a \<noteq> 0\<close>
    by force
  then have \<open>(\<Sum>\<^sub>\<infinity>(E, _)\<in>kf_similar_elements (kf_filter (\<lambda>xa. f xa = x) \<EE>) a. (norm E)\<^sup>2) \<noteq> 0\<close>
    by (simp add: kf_element_weight_def)
  from this[unfolded not_def, rule_format, OF infsum_0]
  obtain E x' where rel_ops: \<open>(E,x') \<in> kf_similar_elements (kf_filter (\<lambda>xa. f xa = x) \<EE>) a\<close>
    and \<open>(norm E)\<^sup>2 \<noteq> 0\<close>
    by fast
  then have \<open>E \<noteq> 0\<close>
    by force
  with rel_ops obtain E' where \<open>E' \<noteq> 0\<close> and \<open>(E',x') \<in> Rep_kraus_family (kf_filter (\<lambda>xa. f xa = x) \<EE>)\<close>
    apply atomize_elim
    by (auto simp: kf_similar_elements_def)
  then have \<open>(E',x') \<in> Rep_kraus_family \<EE>\<close> and \<open>f x' = x\<close>
    by (auto simp: kf_filter.rep_eq)
  with \<open>E' \<noteq> 0\<close> have \<open>x' \<in> kf_domain \<EE>\<close>
    by (force simp: kf_domain.rep_eq)
  with \<open>f x' = x\<close>
  show \<open>x \<in> f ` kf_domain \<EE>\<close>
    by fast
next
  fix x assume \<open>x \<in> f ` kf_domain \<EE>\<close>
  then obtain y where \<open>x = f y\<close> and \<open>y \<in> kf_domain \<EE>\<close>
    by blast
  then obtain E where \<open>E \<noteq> 0\<close> and \<open>(E,y) \<in> Rep_kraus_family \<EE>\<close>
    using Rep_kraus_family by (force simp: kf_domain.rep_eq kraus_family_def)
  then have Ey: \<open>(E,y) \<in> Rep_kraus_family (kf_filter (\<lambda>z. f z=x) \<EE>)\<close>
    by (simp add: kf_filter.rep_eq \<open>x = f y\<close>)
  then have \<open>kf_bound (kf_filter (\<lambda>z. f z=x) \<EE>) \<noteq> 0\<close>
  proof -
    define B where \<open>B = kf_bound (kf_filter (\<lambda>z. f z=x) \<EE>)\<close>
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) {(E,y)} (E* o\<^sub>C\<^sub>L E)\<close>
      apply (subst asm_rl[of \<open>E* o\<^sub>C\<^sub>L E = (\<Sum>(E,x)\<in>{(E,y)}. E* o\<^sub>C\<^sub>L E)\<close>], simp)
      apply (rule has_sum_in_finite)
      by auto
    moreover have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (kf_filter (\<lambda>z. f z = x) \<EE>)) B\<close>
      using kf_bound_has_sum B_def by blast
    ultimately have \<open>B \<ge> E* o\<^sub>C\<^sub>L E\<close>
      apply (rule has_sum_mono_neutral_wot)
      using Ey positive_cblinfun_squareI by auto
    then show \<open>B \<noteq> 0\<close>
      by (meson \<open>E \<noteq> 0\<close> basic_trans_rules(24) op_square_nondegenerate positive_cblinfun_squareI)
  qed
  then have \<open>kf_bound (kf_map f (kf_filter (\<lambda>z. f z=x) \<EE>)) \<noteq> 0\<close>
    by (simp add: kf_map_bound)
  then have \<open>kf_bound (kf_filter (\<lambda>z. z=x) (kf_map f \<EE>)) \<noteq> 0\<close>
    by (simp add: kf_filter_map)
  from this[unfolded not_def kf_bound.rep_eq, rule_format, OF infsum_in_0]
  obtain E' x' where \<open>(E',x') \<in> Rep_kraus_family (kf_filter (\<lambda>z. z=x) (kf_map f \<EE>))\<close>
    and \<open>E' \<noteq> 0\<close>
    by fastforce
  then have \<open>(E',x') \<in> Rep_kraus_family (kf_map f \<EE>)\<close> and \<open>x' = x\<close>
    by (auto simp: kf_filter.rep_eq)
  with \<open>E' \<noteq> 0\<close> show \<open>x \<in> kf_domain (kf_map f \<EE>)\<close>
    by (auto simp: kf_domain.rep_eq image_iff Bex_def)
qed


lemma kf_apply_on_map[simp]:
  \<open>(kf_map f E) *\<^sub>k\<^sub>r @X \<rho> = E *\<^sub>k\<^sub>r @(f -` X) \<rho>\<close>
  by (auto intro!: simp: kf_apply_on_def kf_filter_map)

lemma kf_apply_on_map_inj[simp]:
  assumes \<open>inj_on f ((f -` X) \<inter> kf_domain E)\<close>
  shows  \<open>kf_map_inj f E *\<^sub>k\<^sub>r @X \<rho> = E *\<^sub>k\<^sub>r @(f -` X) \<rho>\<close>
proof -
  from assms
  have \<open>inj_on f (Set.filter (\<lambda>x. f x \<in> X) (kf_domain E))\<close>
    by (smt (verit, del_insts) IntI Set.member_filter inj_onD inj_onI vimage_eq)
  then show ?thesis
    by (auto intro!: simp: kf_apply_on_def kf_filter_map_inj)
qed

lemma kf_map0[simp]: \<open>kf_map f 0 = 0\<close>
  apply transfer'
  by auto

lemma kf_map_inj_kr_eq_weak:
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_map_inj f \<EE> =\<^sub>k\<^sub>r \<EE>\<close>
  by (simp add: assms kf_eq_weakI)

lemma kf_map_inj_0[simp]: \<open>kf_map_inj f 0 = 0\<close>
  apply (transfer' fixing: f)
  by simp

lemma kf_domain_map_inj[simp]: \<open>kf_domain (kf_map_inj f \<EE>) = f ` kf_domain \<EE>\<close>
  apply transfer'
  by force

lemma kf_operators_kf_map:
  \<open>kf_operators (kf_map f \<EE>) \<subseteq> span (kf_operators \<EE>)\<close>
proof (rule subsetI)
  fix E
  assume \<open>E \<in> kf_operators (kf_map f \<EE>)\<close>
  then obtain b where \<open>(norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>x. f x = b) \<EE>) E \<and> E \<noteq> 0\<close> 
    by (auto simp add: kf_operators.rep_eq kf_map.rep_eq)
  then have \<open>kf_element_weight (kf_filter (\<lambda>x. f x = b) \<EE>) E \<noteq> 0\<close>
    by force
  then have \<open>E \<in> span (kf_operators (kf_filter (\<lambda>x. f x = b) \<EE>))\<close>
    by (rule kf_element_weight_kf_operators)
  then show \<open>E \<in> span (kf_operators \<EE>)\<close>
    using kf_operators_filter[of \<open>(\<lambda>x. f x = b)\<close> \<EE>]
    by (meson basic_trans_rules(31) span_mono)
qed

lemma kf_operators_kf_map_inj[simp]: \<open>kf_operators (kf_map_inj f \<EE>) = kf_operators \<EE>\<close>
  apply transfer' by force


subsection \<open>Addition\<close>

lift_definition kf_plus :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a,'b,'y) kraus_family \<Rightarrow> ('a,'b,'x+'y) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. (\<lambda>(E,x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F,y). (F, Inr y)) ` \<FF>\<close>
proof (rename_tac \<EE> \<FF>)
  fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close> and \<FF> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'y) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close> and \<open>\<FF> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
    by auto
  then have \<open>kraus_family ((\<lambda>(E, x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F, y). (F, Inr y)) ` \<FF>)\<close>
    by (force intro!: summable_on_Un_disjoint
      summable_on_reindex[THEN iffD2] inj_onI
      simp: kraus_family_iff_summable' o_def case_prod_unfold conj_commute)
  then show \<open>(\<lambda>(E, x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F, y). (F, Inr y)) ` \<FF> \<in> Collect kraus_family\<close>
    by simp
qed

instantiation kraus_family :: (chilbert_space, chilbert_space, type) plus begin
definition plus_kraus_family where \<open>\<EE> + \<FF> = kf_map (\<lambda>xy. case xy of Inl x \<Rightarrow> x | Inr y \<Rightarrow> y) (kf_plus \<EE> \<FF>)\<close>
instance..
end

lemma kf_plus_apply:
  fixes \<EE> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('a, 'b, 'y) kraus_family\<close>
  shows \<open>kf_apply (kf_plus \<EE> \<FF>) \<rho> = kf_apply \<EE> \<rho> + kf_apply \<FF> \<rho>\<close>
proof -
  have \<open>kf_apply (kf_plus \<EE> \<FF>) \<rho> = 
    (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(E,x). (E, Inl x)) ` Rep_kraus_family \<EE> \<union> (\<lambda>(F,y). (F, Inr y)) ` Rep_kraus_family \<FF>. sandwich_tc (fst EF) \<rho>)\<close>
    by (simp add: kf_plus.rep_eq kf_apply_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(E,x). (E, Inl x :: 'x+'y)) ` Rep_kraus_family \<EE>. sandwich_tc (fst EF) \<rho>)
                + (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(F,y). (F, Inr y :: 'x+'y)) ` Rep_kraus_family \<FF>. sandwich_tc (fst EF) \<rho>)\<close>
    apply (subst infsum_Un_disjoint)
    using kf_apply_summable
    by (auto intro!: summable_on_reindex[THEN iffD2] inj_onI
        simp: o_def case_prod_unfold kf_apply_summable)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>Rep_kraus_family \<EE>. sandwich_tc (fst E) \<rho>) + (\<Sum>\<^sub>\<infinity>F\<in>Rep_kraus_family \<FF>. sandwich_tc (fst F) \<rho>)\<close>
    apply (subst infsum_reindex)
     apply (auto intro!: inj_onI)[1]
    apply (subst infsum_reindex)
     apply (auto intro!: inj_onI)[1]
    by (simp add:  o_def case_prod_unfold)
  also have \<open>\<dots> = kf_apply \<EE> \<rho> + kf_apply \<FF> \<rho>\<close>
    by (simp add: kf_apply_def)
  finally show ?thesis
    by -
qed

lemma kf_plus_apply': \<open>(\<EE> + \<FF>) *\<^sub>k\<^sub>r \<rho> = \<EE> *\<^sub>k\<^sub>r \<rho> + \<FF> *\<^sub>k\<^sub>r \<rho>\<close>
  by (simp add: kf_plus_apply plus_kraus_family_def)

lemma kf_plus_0_left[simp]: \<open>kf_plus 0 \<EE> = kf_map_inj Inr \<EE>\<close>
  apply transfer' by auto

lemma kf_plus_0_right[simp]: \<open>kf_plus \<EE> 0 = kf_map_inj Inl \<EE>\<close>
  apply transfer' by auto

lemma kf_plus_0_left'[simp]: \<open>0 + \<EE> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
proof -
  define merge where \<open>merge xy = (case xy of Inl x \<Rightarrow> x | Inr y \<Rightarrow> y)\<close> for xy :: \<open>'c + 'c\<close>
  have \<open>0 + \<EE> = kf_map merge (kf_map_inj Inr \<EE>)\<close>
    by (simp add: plus_kraus_family_def merge_def[abs_def])
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map merge (kf_map Inr \<EE>)\<close>
    by (auto intro!: kf_map_cong kf_map_inj_eq_kf_map)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (merge o Inr) \<EE>\<close>
  by (simp add: kf_map_twice)
  also have \<open>\<dots> = kf_map id \<EE>\<close>
    apply (rule arg_cong2[where f=kf_map])
    by (auto simp: merge_def)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
    by (simp add: kf_map_id)
  finally show ?thesis
    by -
qed

lemma kf_plus_0_right': \<open>\<EE> + 0 \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
proof -
  define merge where \<open>merge xy = (case xy of Inl x \<Rightarrow> x | Inr y \<Rightarrow> y)\<close> for xy :: \<open>'c + 'c\<close>
  have \<open>\<EE> + 0 = kf_map merge (kf_map_inj Inl \<EE>)\<close>
    by (simp add: plus_kraus_family_def merge_def[abs_def])
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map merge (kf_map Inl \<EE>)\<close>
    by (auto intro!: kf_map_cong kf_map_inj_eq_kf_map)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (merge o Inl) \<EE>\<close>
  by (simp add: kf_map_twice)
  also have \<open>\<dots> = kf_map id \<EE>\<close>
    apply (rule arg_cong2[where f=kf_map])
    by (auto simp: merge_def)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r \<EE>\<close>
    by (simp add: kf_map_id)
  finally show ?thesis
    by -
qed

lemma kf_plus_bound: \<open>kf_bound (kf_plus \<EE> \<FF>) = kf_bound \<EE> + kf_bound \<FF>\<close>
proof -
  define l r where \<open>l = (\<lambda>(E::'a\<Rightarrow>\<^sub>C\<^sub>L'b, x) \<Rightarrow> (E, Inl x :: 'c+'d))\<close>
    and \<open>r = (\<lambda>(F::'a\<Rightarrow>\<^sub>C\<^sub>L'b, y) \<Rightarrow> (F, Inr y :: 'c+'d))\<close>
  have \<open>Abs_cblinfun_wot (kf_bound (kf_plus \<EE> \<FF>)) 
    = (\<Sum>\<^sub>\<infinity>(E, x)\<in>l ` Rep_kraus_family \<EE> \<union> r ` Rep_kraus_family \<FF>. compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    by (simp add: kf_bound_def' kf_plus.rep_eq Rep_cblinfun_wot_inverse flip: l_def r_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E, x)\<in>l ` Rep_kraus_family \<EE>. compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))
                + (\<Sum>\<^sub>\<infinity>(E, x)\<in>r ` Rep_kraus_family \<FF>. compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    apply (rule infsum_Un_disjoint)
      apply (metis (no_types, lifting) ext Un_empty_right l_def image_empty kf_bound_summable' kf_plus.rep_eq
        zero_kraus_family.rep_eq) 
     apply (metis (no_types, lifting) ext r_def empty_subsetI image_empty kf_bound_summable' kf_plus.rep_eq
        sup.absorb_iff2 zero_kraus_family.rep_eq) 
    by (auto intro!: simp: l_def r_def)
  also have \<open>\<dots> = Abs_cblinfun_wot (kf_bound (kf_map_inj Inl \<EE> :: (_,_,'c+'d) kraus_family)) + Abs_cblinfun_wot (kf_bound (kf_map_inj Inr \<FF> :: (_,_,'c+'d) kraus_family))\<close>
    by (simp add: kf_bound_def' Rep_cblinfun_wot_inverse l_def r_def kf_map_inj.rep_eq case_prod_unfold)
  also have \<open>\<dots> = Abs_cblinfun_wot (kf_bound \<EE> + kf_bound \<FF>)\<close>
    by (simp add: kf_map_inj_bound plus_cblinfun_wot.abs_eq)
  finally show ?thesis
    by (metis (no_types, lifting) Rep_cblinfun_wot_inverse kf_bound_def' plus_cblinfun_wot.rep_eq)
qed

lemma kf_plus_bound': \<open>kf_bound (\<EE> + \<FF>) = kf_bound \<EE> + kf_bound \<FF>\<close>
  by (simp add: kf_map_bound kf_plus_bound plus_kraus_family_def)

lemma kf_norm_triangle: \<open>kf_norm (kf_plus \<EE> \<FF>) \<le> kf_norm \<EE> + kf_norm \<FF>\<close>
  by (simp add: kf_norm_def kf_plus_bound norm_triangle_ineq)

lemma kf_norm_triangle': \<open>kf_norm (\<EE> + \<FF>) \<le> kf_norm \<EE> + kf_norm \<FF>\<close>
  by (simp add: kf_norm_def kf_plus_bound' norm_triangle_ineq)

lemma kf_plus_map_both:
  \<open>kf_plus (kf_map f \<EE>) (kf_map g \<FF>) = kf_map (map_sum f g) (kf_plus \<EE> \<FF>)\<close>
proof -
  have 1: \<open>kf_filter (\<lambda>x. map_sum f g x = Inl y) (kf_plus \<EE> \<FF>) = 
          kf_map_inj Inl (kf_filter (\<lambda>x. f x = y) \<EE>)\<close> for y
    apply (transfer' fixing: f g y)
    by force
  have 2: \<open>kf_filter (\<lambda>x. map_sum f g x = Inr y) (kf_plus \<EE> \<FF>) = 
          kf_map_inj Inr (kf_filter (\<lambda>x. g x = y) \<FF>)\<close> for y
    apply (transfer' fixing: f g y)
    by force
  show ?thesis
    apply (transfer' fixing: f g \<EE> \<FF>)
    apply (rule Set.set_eqI)
    subgoal for x
      apply (cases \<open>snd x\<close>)
      by (auto intro!: simp: 1 2 kf_element_weight_map_inj split!: sum.split)
    by -
qed


subsection \<open>Composition\<close>

lemma kf_comp_dependent_raw_norm_aux:
  fixes \<EE> :: \<open>'a \<Rightarrow> ('e::chilbert_space, 'f::chilbert_space, 'g) kraus_family\<close>
    and \<FF> :: \<open>('b::chilbert_space, 'e, 'a) kraus_family\<close>
  assumes B: \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> x) \<le> B\<close>
  assumes [simp]: \<open>B \<ge> 0\<close>
  assumes \<open>finite C\<close>
  assumes C_subset: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
  shows \<open>(\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E) \<le> (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
proof -
  define BF :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>BF = kf_norm \<FF> *\<^sub>R id_cblinfun\<close>
  then have \<open>kf_bound \<FF> \<le> BF\<close>
    by (simp add: kf_bound_leq_kf_norm_id)
  then have BF: \<open>(\<Sum>(F, y)\<in>M. (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>M \<subseteq> Rep_kraus_family \<FF>\<close> and \<open>finite M\<close> for M
    using dual_order.trans kf_bound_geq_sum that(1) by blast
  define BE :: \<open>'e \<Rightarrow>\<^sub>C\<^sub>L 'e\<close> where \<open>BE = B *\<^sub>R id_cblinfun\<close>
  define \<FF>x\<EE> where \<open>\<FF>x\<EE> = (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
  have BE: \<open>(\<Sum>(E, x)\<in>M. (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>y \<in> kf_domain \<FF>\<close> and \<open>M \<subseteq> Rep_kraus_family (\<EE> y)\<close> and \<open>finite M\<close> for M y
  proof -
    from B that(1,2)
    have \<open>norm (\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
      by (smt (verit) kf_norm_geq_norm_sum that)
    then show ?thesis
      by (auto intro!: less_eq_scaled_id_norm pos_selfadjoint sum_nonneg intro: positive_cblinfun_squareI simp: BE_def)
  qed

  define A where \<open>A = (\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E)\<close>
  define CE CF where \<open>CE y = (\<lambda>(_,(F,E,y,x)). (E,x)) ` Set.filter (\<lambda>(_,(F,E,y',x)). y'=y) C\<close> 
    and \<open>CF = (\<lambda>(_,(F,E,y,x)). (F,y)) ` C\<close> for y
  with \<open>finite C\<close> have [simp]: \<open>finite (CE y)\<close> \<open>finite CF\<close> for y
    by auto
  have C_C1C2: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):CF. CE y)\<close>
  proof (rule subsetI)
    fix c assume \<open>c \<in> C\<close>
    then obtain EF E F x y where c_def: \<open>c = (EF,(F,E,y,x))\<close>
      by (metis surj_pair)
    from \<open>c \<in> C\<close> have EF_def: \<open>EF = E o\<^sub>C\<^sub>L F\<close>
      using C_subset by (auto intro!: simp: c_def)
    from \<open>c \<in> C\<close> have 1: \<open>(F,y) \<in> CF\<close>
      apply (simp add: CF_def c_def)
      by force
    from \<open>c \<in> C\<close> have 2: \<open>(E,x) \<in> CE y\<close>
      apply (simp add: CE_def c_def)
      by force
    from 1 2 show \<open>c \<in> (\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F, y):CF. CE y)\<close>
      apply (simp add: c_def EF_def)
      by force
  qed

  have CE_sub_\<EE>: \<open>CE y \<subseteq> Rep_kraus_family (\<EE> y)\<close> and \<open>CF \<subseteq> Rep_kraus_family \<FF>\<close> for y
    using C_subset by (auto simp add: CE_def CF_def \<FF>x\<EE>_def case_prod_unfold)
  have CE_BE: \<open>(\<Sum>(E, x)\<in>CE y. (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>y \<in> kf_domain \<FF>\<close> for y
    using BE[where y=y] CE_sub_\<EE>[of y] that
    by auto

  have \<open>A \<le> (\<Sum>(E,x) \<in> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):CF. CE y). E* o\<^sub>C\<^sub>L E)\<close>
    using C_C1C2 by (auto intro!: finite_imageI sum_mono2 positive_cblinfun_squareI simp: A_def simp flip: adj_cblinfun_compose)[1]
  also have \<open>\<dots> = (\<Sum>((F,y), (E,x))\<in>(SIGMA (F,y):CF. CE y). (F* o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L F))\<close>
    apply (subst sum.reindex)
    by (auto intro!: inj_onI simp: case_prod_unfold cblinfun_compose_assoc)
  also have \<open>\<dots> = (\<Sum>(F, y)\<in>CF. sandwich (F*) (\<Sum>(E, x)\<in>CE y. (E* o\<^sub>C\<^sub>L E)))\<close>
    apply (subst sum.Sigma[symmetric])
    by (auto intro!: simp: case_prod_unfold sandwich_apply cblinfun_compose_sum_right cblinfun_compose_sum_left simp flip: )
  also have \<open>\<dots> \<le> (\<Sum>(F, y)\<in>CF. sandwich (F*) BE)\<close>
  proof (rule sum_mono)
    fix i :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'e \<times> 'a\<close> assume \<open>i \<in> CF\<close>
    obtain F y where i: \<open>i = (F,y)\<close>
      by force
    have 1: \<open>sandwich (F*) *\<^sub>V (\<Sum>(E,x)\<in>CE y. E* o\<^sub>C\<^sub>L E) \<le> sandwich (F*) *\<^sub>V BE\<close> if \<open>y \<in> kf_domain \<FF>\<close>
      apply (rule sandwich_mono)
      using that CE_BE by simp
    have \<open>F = 0\<close> if \<open>y \<notin> kf_domain \<FF>\<close>
        using C_subset CF_def \<open>CF \<subseteq> Rep_kraus_family \<FF>\<close> \<open>i \<in> CF\<close> that i
        by (smt (verit, ccfv_SIG) Set.basic_monos(7) Set.member_filter case_prodI image_iff kf_domain.rep_eq prod.sel(2))
    then have 2: \<open>sandwich (F*) *\<^sub>V (\<Sum>(E,x)\<in>CE y. E* o\<^sub>C\<^sub>L E) \<le> sandwich (F*) *\<^sub>V BE\<close> if \<open>y \<notin> kf_domain \<FF>\<close>
      using that by simp
    from 1 2 show \<open>(case i of (F, y) \<Rightarrow> sandwich (F*) *\<^sub>V (\<Sum>(E, x)\<in>CE y. E* o\<^sub>C\<^sub>L E))
         \<le> (case i of (F, y) \<Rightarrow> sandwich (F*) *\<^sub>V BE)\<close>
      by (auto simp: case_prod_unfold i)
  qed
  also have \<open>\<dots> = B *\<^sub>R (\<Sum>(F, y)\<in>CF. F* o\<^sub>C\<^sub>L F)\<close>
    by (simp add: scaleR_sum_right case_prod_unfold sandwich_apply BE_def)
  also have \<open>\<dots> \<le> B *\<^sub>R BF\<close>
    using BF by (simp add: \<open>CF \<subseteq> Rep_kraus_family \<FF>\<close> scaleR_left_mono case_prod_unfold)
  also have \<open>B *\<^sub>R BF = (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
    by (simp add: BF_def)
  finally show \<open>A \<le> (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
    by -
qed

lift_definition kf_comp_dependent_raw :: \<open>('x \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'y) kraus_family) \<Rightarrow> ('a::chilbert_space,'b,'x) kraus_family
                    \<Rightarrow> ('a, 'c, ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> ('b \<Rightarrow>\<^sub>C\<^sub>L 'c) \<times> 'x \<times> 'y) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. if bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>) then
    Set.filter (\<lambda>(EF,_). EF\<noteq>0) ((\<lambda>((F,y), (E::'b\<Rightarrow>\<^sub>C\<^sub>L'c,x::'y)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F::'a\<Rightarrow>\<^sub>C\<^sub>L'b,y::'x):Rep_kraus_family \<FF>. (Rep_kraus_family (\<EE> y))))
    else {}\<close>
proof (rename_tac \<EE> \<FF>)
  fix \<EE> :: \<open>'x \<Rightarrow> ('b, 'c, 'y) kraus_family\<close> and \<FF> :: \<open>('a, 'b, 'x) kraus_family\<close>
  show \<open>(if bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)
        then Set.filter (\<lambda>(EF,_). EF\<noteq>0) ((\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, (F, E, y, x))) ` (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)))
        else {})
       \<in> Collect kraus_family\<close>
  proof (cases \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>)
    case True
    obtain B where \<EE>_uniform: \<open>y \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> y) \<le> B\<close> and \<open>B \<ge> 0\<close> for y
    proof atomize_elim
      from True
      obtain B0 where \<open>y \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> y) \<le> B0\<close> for y
        by (auto simp: bdd_above_def)
      then show \<open>\<exists>B. (\<forall>y. y \<in> kf_domain \<FF> \<longrightarrow> kf_norm (\<EE> y) \<le> B) \<and> 0 \<le> B\<close>
        apply (rule_tac exI[of _ \<open>max 0 B0\<close>])
        by force
    qed
    define \<FF>x\<EE> where \<open>\<FF>x\<EE> = (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    have \<open>bdd_above ((\<lambda>M. \<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) `
            {M. M \<subseteq> Set.filter (\<lambda>(EF, _). EF \<noteq> 0) ((\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` \<FF>x\<EE>) \<and> finite M})\<close>
    proof (rule bdd_aboveI, rename_tac A)
      fix A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
      assume \<open>A \<in> (\<lambda>M. \<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) ` {M. M \<subseteq> Set.filter (\<lambda>(EF, _). EF \<noteq> 0) ((\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` \<FF>x\<EE>) \<and> finite M}\<close>
      then obtain C where A_def: \<open>A = (\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E)\<close>
        and C\<FF>\<EE>: \<open>C \<subseteq> Set.filter (\<lambda>(EF,_). EF \<noteq> 0) ((\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` \<FF>x\<EE>)\<close>
        and [simp]: \<open>finite C\<close>
        by auto
      from kf_comp_dependent_raw_norm_aux[OF \<EE>_uniform \<open>B \<ge> 0\<close> \<open>finite C\<close>]
      show \<open>A \<le> (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
        using C\<FF>\<EE>
        by (force intro!: simp: A_def \<FF>x\<EE>_def)
    qed
    then have \<open>kraus_family (Set.filter (\<lambda>(EF,_). EF\<noteq>0) ((\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))))\<close>
      by (auto intro!: kraus_familyI simp: conj_commute \<FF>x\<EE>_def)
    then show ?thesis
      using True by simp
  next
    case False
    then show ?thesis
      by (auto simp: kraus_family_def)
  qed
qed

lemma kf_comp_dependent_raw_norm_leq:
  fixes \<EE> :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'c::chilbert_space, 'd) kraus_family\<close>
    and \<FF> :: \<open>('e::chilbert_space, 'b, 'a) kraus_family\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> x) \<le> B\<close>
  assumes \<open>B \<ge> 0\<close>
  shows \<open>kf_norm (kf_comp_dependent_raw \<EE> \<FF>) \<le> B * kf_norm \<FF>\<close>
proof -
  wlog not_singleton: \<open>class.not_singleton TYPE('e)\<close>
    using not_not_singleton_kf_norm_0[OF negation, of \<FF>]
    using not_not_singleton_kf_norm_0[OF negation, of \<open>kf_comp_dependent_raw \<EE> \<FF>\<close>]
    by simp
  show ?thesis
  proof (rule kf_norm_sum_leqI)
    fix F assume \<open>finite F\<close> and F_subset: \<open>F \<subseteq> Rep_kraus_family (kf_comp_dependent_raw \<EE> \<FF>)\<close>
    have [simp]: \<open>norm (id_cblinfun :: 'e \<Rightarrow>\<^sub>C\<^sub>L 'e) = 1\<close>
      apply (rule norm_cblinfun_id[internalize_sort' 'a])
      apply (rule complex_normed_vector_axioms)
      by (rule not_singleton)
    from assms have bdd: \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> x)) ` kf_domain \<FF>)\<close>
      by fast
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> (B * kf_norm \<FF>) *\<^sub>R id_cblinfun\<close>
      using assms \<open>finite F\<close> apply (rule kf_comp_dependent_raw_norm_aux)
      using F_subset by (auto simp: kf_comp_dependent_raw.rep_eq bdd)
    then have \<open>norm (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> norm ((B * kf_norm \<FF>) *\<^sub>R (id_cblinfun :: 'e \<Rightarrow>\<^sub>C\<^sub>L 'e))\<close>
      apply (rule norm_cblinfun_mono[rotated])
      using positive_cblinfun_squareI 
      by (auto intro!: sum_nonneg)
    then show \<open>norm (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B * kf_norm \<FF>\<close>
      using \<open>B \<ge> 0\<close> by auto
  qed
qed

hide_fact kf_comp_dependent_raw_norm_aux

definition \<open>kf_comp_dependent \<EE> \<FF> = kf_map (\<lambda>(F,E,y,x). (y,x)) (kf_comp_dependent_raw \<EE> \<FF>)\<close>

definition \<open>kf_comp \<EE> \<FF> = kf_comp_dependent (\<lambda>_. \<EE>) \<FF>\<close>

lemma kf_comp_dependent_norm_leq:
  assumes \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> kf_norm (\<EE> x) \<le> B\<close>
  assumes \<open>B \<ge> 0\<close>
  shows \<open>kf_norm (kf_comp_dependent \<EE> \<FF>) \<le> B * kf_norm \<FF>\<close>
  using assms by (auto intro!: kf_comp_dependent_raw_norm_leq simp: kf_comp_dependent_def)

lemma kf_comp_norm_leq:
  shows \<open>kf_norm (kf_comp \<EE> \<FF>) \<le> kf_norm \<EE> * kf_norm \<FF>\<close>
  by (auto intro!: kf_comp_dependent_norm_leq simp: kf_comp_def)

lemma kf_comp_dependent_raw_apply:
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  assumes \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent_raw \<EE> \<FF> *\<^sub>k\<^sub>r \<rho>
            = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<EE> y *\<^sub>k\<^sub>r sandwich_tc F \<rho>)\<close>
proof -
  have sum2: \<open>(\<lambda>(F, x). sandwich_tc F \<rho>) summable_on (Rep_kraus_family \<FF>)\<close>
    using kf_apply_summable[of \<rho> \<FF>] (* kraus\<FF> *) by (simp add: case_prod_unfold)
  have \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on 
          (Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))))\<close>
    using kf_apply_summable[of _ \<open>kf_comp_dependent_raw \<EE> \<FF>\<close>] assms
    by (simp add: kf_comp_dependent_raw.rep_eq case_prod_unfold)
  then have \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on 
          (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    apply (rule summable_on_cong_neutral[THEN iffD1, rotated -1])
    by force+
  then have sum1: \<open>(\<lambda>((F,y), (E,x)). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>) summable_on (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    apply (subst (asm) summable_on_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  have \<open>kf_comp_dependent_raw \<EE> \<FF> *\<^sub>k\<^sub>r \<rho>
          = (\<Sum>\<^sub>\<infinity>E\<in>(Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)))). sandwich_tc (fst E) \<rho>)\<close>
    using assms by (simp add: kf_apply_def kf_comp_dependent_raw.rep_eq case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)). sandwich_tc (fst E) \<rho>)\<close>
    apply (rule infsum_cong_neutral)
    by force+
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((F,y), (E,x))\<in>(SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family (\<EE> y). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>)\<close>
    apply (subst infsum_Sigma'_banach[symmetric])
    using sum1 by (auto simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family (\<EE> y). sandwich_tc E (sandwich_tc F \<rho>))\<close>
    by (simp add: sandwich_tc_compose)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. kf_apply (\<EE> y) (sandwich_tc F \<rho>))\<close>
    by (simp add: kf_apply_def case_prod_unfold)
  finally show ?thesis
    by -
qed

lemma kf_comp_dependent_apply:
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  assumes \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> *\<^sub>k\<^sub>r \<rho>
      = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<EE> y *\<^sub>k\<^sub>r sandwich_tc F \<rho>)\<close>
  using assms by (simp add: kf_comp_dependent_def kf_apply_map
      kf_comp_dependent_raw_apply)

lemma kf_comp_apply:
  shows \<open>kf_apply (kf_comp \<EE> \<FF>) = kf_apply \<EE> \<circ> kf_apply \<FF>\<close>
proof (rule ext, rename_tac \<rho>)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>

  have sumF: \<open>(\<lambda>(F, y). sandwich_tc F \<rho>) summable_on Rep_kraus_family \<FF>\<close>
    by (rule kf_apply_summable)
  have \<open>kf_comp \<EE> \<FF> *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<EE> *\<^sub>k\<^sub>r sandwich_tc F \<rho>)\<close>
    by (auto intro!: kf_comp_dependent_apply simp: kf_comp_def)
  also have \<open>\<dots> = kf_apply \<EE> (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. sandwich_tc F \<rho>)\<close>
    apply (subst infsum_bounded_linear[symmetric, where h=\<open>kf_apply \<EE>\<close>])
    using sumF by (auto intro!: bounded_clinear.bounded_linear kf_apply_bounded_clinear
        simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (kf_apply \<EE> \<circ> kf_apply \<FF>) \<rho>\<close>
    by (simp add: o_def kf_apply_def case_prod_unfold)
  finally show \<open>kf_apply (kf_comp \<EE> \<FF>) \<rho> = (kf_apply \<EE> \<circ> kf_apply \<FF>) \<rho>\<close>
    by -
qed

lemma kf_comp_cong_weak: \<open>kf_comp F G =\<^sub>k\<^sub>r kf_comp F' G'\<close>
  if \<open>F =\<^sub>k\<^sub>r F'\<close> and \<open>G =\<^sub>k\<^sub>r G'\<close>
  by (metis kf_eq_weak_def kf_comp_apply that)

lemma kf_comp_dependent_raw_assoc: 
  fixes \<EE> :: \<open>'f \<Rightarrow> ('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>'g \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  defines \<open>reorder :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'g \<times> 'f) \<times> 'e
                   \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> 'g \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> 'f \<times> 'e \<equiv>
             \<lambda>(FG::'a \<Rightarrow>\<^sub>C\<^sub>L 'c, E::'c \<Rightarrow>\<^sub>C\<^sub>L 'd, (G::'a \<Rightarrow>\<^sub>C\<^sub>L 'b, F::'b \<Rightarrow>\<^sub>C\<^sub>L 'c, g::'g, f::'f), e::'e). 
              (G, E o\<^sub>C\<^sub>L F, g, F, E, f, e)\<close>
  assumes \<open>bdd_above (range (kf_norm o \<EE>))\<close>
  assumes \<open>bdd_above (range (kf_norm o \<FF>))\<close>
  shows \<open>kf_comp_dependent_raw (\<lambda>g::'g. kf_comp_dependent_raw \<EE> (\<FF> g)) \<GG>
        = kf_map_inj reorder (kf_comp_dependent_raw (\<lambda>(_,_,_,f). \<EE> f) (kf_comp_dependent_raw \<FF> \<GG>))\<close>
    (is \<open>?lhs = ?rhs\<close>)
proof (rule Rep_kraus_family_inject[THEN iffD1])
  from assms have bdd_E: \<open>bdd_above ((kf_norm o \<EE>) ` X)\<close> for X
    by (simp add: bdd_above_mono2)
  from assms have bdd_F: \<open>bdd_above ((kf_norm o \<FF>) ` X)\<close> for X
    by (simp add: bdd_above_mono2)
  have bdd1: \<open>bdd_above ((\<lambda>x. kf_norm (kf_comp_dependent_raw \<EE> (\<FF> x))) ` X)\<close> for X
  proof -
    from bdd_F[where X=UNIV] obtain BF where BF: \<open>kf_norm (\<FF> x) \<le> BF\<close> for x
      by (auto simp: bdd_above_def)
    moreover from bdd_E[where X=UNIV] obtain BE where BE: \<open>kf_norm (\<EE> x) \<le> BE\<close> for x
      by (auto simp: bdd_above_def)
    ultimately have \<open>kf_norm (kf_comp_dependent_raw (\<lambda>x. \<EE> x) (\<FF> x)) \<le> BE * BF\<close> for x
      by (smt (verit, best) kf_comp_dependent_raw_norm_leq kf_norm_geq0 landau_omega.R_mult_left_mono)
    then show ?thesis
      by (auto intro!: bdd_aboveI)
  qed
  have bdd2: \<open>bdd_above ((kf_norm \<circ> (\<lambda>(_::'a \<Rightarrow>\<^sub>C\<^sub>L 'b, _::'b \<Rightarrow>\<^sub>C\<^sub>L 'c, _::'g, y::'f). \<EE> y)) ` X)\<close> for X
    using assms(2) by (auto simp: bdd_above_def)
  define EE FF GG where \<open>EE f = Rep_kraus_family (\<EE> f)\<close> and \<open>FF g = Rep_kraus_family (\<FF> g)\<close> and \<open>GG = Rep_kraus_family \<GG>\<close> for f g
  have \<open>Rep_kraus_family ?lhs
        = (Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((F,y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
          (SIGMA (F, y):GG. Rep_kraus_family (kf_comp_dependent_raw \<EE> (\<FF> y)))))\<close>
    apply (subst kf_comp_dependent_raw.rep_eq)
    using bdd1 by (simp add:  GG_def)
  also have \<open>\<dots> = (Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((G, g), (EF, x)). (EF o\<^sub>C\<^sub>L G, G, EF, g, x)) `
    (SIGMA (G, g):GG. Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((F, f), (E, e)). (E o\<^sub>C\<^sub>L F, F, E, f, e)) ` (SIGMA (F, f):FF g. EE f)))))\<close>
    unfolding EE_def FF_def
    apply (subst kf_comp_dependent_raw.rep_eq)
    using assms bdd_E by (simp add: case_prod_beta)
  also have \<open>\<dots> = (Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((G, g), (EF, x)). (EF o\<^sub>C\<^sub>L G, G, EF, g, x)) `
    (SIGMA (G, g):GG. (\<lambda>((F, f), (E, e)). (E o\<^sub>C\<^sub>L F, F, E, f, e)) ` (SIGMA (F, f):FF g. EE f))))\<close>
    by force
  also have \<open>\<dots> = (Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, reorder (F, E, y, x))) ` 
         (SIGMA (FG, _, _, _, y):(\<lambda>((G, g), (F, f)). (F o\<^sub>C\<^sub>L G, G, F, g, f)) ` (SIGMA (G, g):GG. FF g). EE y)))\<close>
    by (force simp: reorder_def image_iff case_prod_unfold cblinfun_compose_assoc)
  also have \<open>\<dots> = (Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, reorder (F, E, y, x))) ` 
         (SIGMA (FG, _, _, _, y):Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((G, g), (F, f)). (F o\<^sub>C\<^sub>L G, G, F, g, f)) ` (SIGMA (G, g):GG. FF g)). EE y)))\<close>
    by force
  also have \<open>\<dots> = (Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, reorder (F, E, y, x))) `
    (SIGMA (FG, (_, _, _, f)):Rep_kraus_family (kf_comp_dependent_raw \<FF> \<GG>). EE f)))\<close>
    apply (rule arg_cong[where f=\<open>Set.filter _\<close>])
    apply (subst kf_comp_dependent_raw.rep_eq)
    using assms bdd_F
    by (simp add: flip: FF_def GG_def)
  also have \<open>\<dots> = (Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>(E,z). (E, reorder z)) ` (\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
    (SIGMA (FG, (_, _, _, f)):Rep_kraus_family (kf_comp_dependent_raw \<FF> \<GG>). EE f)))\<close>
    by (simp add: image_image case_prod_beta)
  also have \<open>\<dots> = (\<lambda>(E,z). (E, reorder z)) ` (Set.filter (\<lambda>(E,x). E \<noteq> 0) ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
    (SIGMA (FG, (_, _, _, f)):Rep_kraus_family (kf_comp_dependent_raw \<FF> \<GG>). EE f)))\<close>
    by force+
  also have \<open>\<dots> = (\<lambda>(E,x). (E,reorder x)) ` Rep_kraus_family
     (kf_comp_dependent_raw (\<lambda>(_, _, _, y). \<EE> y) (kf_comp_dependent_raw \<FF> \<GG>))\<close>
    apply (subst (2) kf_comp_dependent_raw.rep_eq)
    using bdd2 by (simp add: case_prod_unfold EE_def)
  also have \<open>\<dots> = Rep_kraus_family ?rhs\<close>
    by (simp add: kf_map_inj.rep_eq case_prod_beta)
  finally show \<open>Rep_kraus_family ?lhs = Rep_kraus_family ?rhs\<close>
    by -
qed

lemma kf_filter_comp_dependent:
  fixes \<FF> :: \<open>'e \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'e) kraus_family\<close>
  assumes \<open>bdd_above ((kf_norm o \<FF>) ` kf_domain \<EE>)\<close>
  shows \<open>kf_filter (\<lambda>(e,f). F e f \<and> E e) (kf_comp_dependent \<FF> \<EE>)
      = kf_comp_dependent (\<lambda>e. kf_filter (F e) (\<FF> e)) (kf_filter E \<EE>)\<close>
proof -
  from assms
  have bdd2: \<open>bdd_above ((\<lambda>e. kf_norm (kf_filter (F e) (\<FF> e))) ` kf_domain \<EE>)\<close>
    apply (rule bdd_above_mono2)
    by (auto intro!: kf_norm_filter)
  then have bdd3: \<open>bdd_above ((\<lambda>x. kf_norm (kf_filter (F x) (\<FF> x))) `
                              kf_domain (kf_filter E \<EE>))\<close>
    apply (rule bdd_above_mono2)
    by auto
  show ?thesis
    unfolding kf_comp_dependent_def kf_filter_map
    apply (rule arg_cong[where f=\<open>kf_map _\<close>])
    using assms bdd2 bdd3 apply (transfer' fixing: F E)
    by (auto intro!: simp: kf_filter.rep_eq case_prod_unfold image_iff Bex_def)
qed

lemma kf_comp_assoc_weak: 
  fixes \<EE> :: \<open>('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  shows \<open>kf_comp (kf_comp \<EE> \<FF>) \<GG> =\<^sub>k\<^sub>r kf_comp \<EE> (kf_comp \<FF> \<GG>)\<close>
  apply (rule kf_eq_weakI)
  by (simp add: kf_comp_apply)

lemma kf_comp_dependent_raw_cong_left:
  assumes \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes \<open>bdd_above ((kf_norm o \<EE>') ` kf_domain \<FF>)\<close>
  assumes \<open>\<And>x. x \<in> snd ` Rep_kraus_family \<FF> \<Longrightarrow> \<EE> x = \<EE>' x\<close>
  shows \<open>kf_comp_dependent_raw \<EE> \<FF> = kf_comp_dependent_raw \<EE>' \<FF>\<close>
proof -
  show ?thesis
  apply (rule Rep_kraus_family_inject[THEN iffD1])
    using assms
  by (force simp: kf_comp_dependent_def kf_comp_dependent_raw.rep_eq 
      image_iff case_prod_beta Bex_def) 
qed

(* lemma kf_remove_0_comp_dependent_raw:
  \<open>kf_remove_0 (kf_comp_dependent_raw \<EE> \<FF>) =
      kf_remove_0 (kf_comp_dependent_raw (\<lambda>x. kf_remove_0 (\<EE> x)) (kf_remove_0 \<FF>))\<close>
  apply transfer'
  by (auto intro!: simp: image_iff case_prod_beta kf_remove_0.rep_eq Bex_def) *)

lemma kf_comp_dependent_cong_left:
  assumes \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes \<open>bdd_above ((kf_norm o \<EE>') ` kf_domain \<FF>)\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> \<EE> x = \<EE>' x\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> = kf_comp_dependent \<EE>' \<FF>\<close>
proof -
  have \<open>kf_comp_dependent \<EE> \<FF> = kf_map (\<lambda>(F, E, y). y) (kf_comp_dependent_raw \<EE> \<FF>)\<close>
    by (simp add: kf_comp_dependent_def id_def)
  also have \<open>\<dots> = kf_map (\<lambda>(F, E, y). y) ((kf_comp_dependent_raw (\<lambda>x. (\<EE>' x)) (\<FF>)))\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_map _ t\<close>])
    apply (rule kf_comp_dependent_raw_cong_left[OF assms])
    using assms by (auto intro!: simp: kf_domain.rep_eq)
  also have \<open>\<dots> = kf_comp_dependent \<EE>' \<FF>\<close>
    by (simp add: kf_comp_dependent_def id_def)
  finally show ?thesis
    by -
qed

lemma kf_domain_comp_dependent_raw_subset:
  \<open>kf_domain (kf_comp_dependent_raw \<EE> \<FF>) \<subseteq> UNIV \<times> UNIV \<times> (SIGMA x:kf_domain \<FF>. kf_domain (\<EE> x))\<close>
  by (auto intro!: simp: kf_comp_dependent_raw.rep_eq kf_domain.rep_eq image_iff Bex_def)

lemma kf_domain_comp_dependent_subset:
  \<open>kf_domain (kf_comp_dependent \<EE> \<FF>) \<subseteq> (SIGMA x:kf_domain \<FF>. kf_domain (\<EE> x))\<close>
  apply (simp add: kf_comp_dependent_def kf_domain_map id_def)
  by (auto intro!: simp: kf_comp_dependent_raw.rep_eq kf_domain.rep_eq image_iff Bex_def)

lemma kf_domain_comp_subset: \<open>kf_domain (kf_comp \<EE> \<FF>) \<subseteq> kf_domain \<FF> \<times> kf_domain \<EE>\<close>
  by (metis Sigma_cong kf_comp_def kf_domain_comp_dependent_subset)

lemma kf_apply_comp_dependent_cong:
  fixes \<EE> :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e1) kraus_family\<close>
    and \<EE>' :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e2) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  assumes bdd: \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes bdd': \<open>bdd_above ((kf_norm o \<EE>') ` kf_domain \<FF>')\<close>
  assumes \<open>f \<in> kf_domain \<FF> \<Longrightarrow> kf_apply_on (\<EE> f) E = kf_apply_on (\<EE>' f) E'\<close>
  assumes \<open>kf_apply_on \<FF> {f} = kf_apply_on \<FF>' {f}\<close>
  shows \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({f}\<times>E) = kf_apply_on (kf_comp_dependent \<EE>' \<FF>') ({f}\<times>E')\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>

  have rewrite_comp: \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({f}\<times>E) = 
        kf_apply (kf_comp (kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
                                           (kf_filter (\<lambda>x. x=f) \<FF>))\<close>
    if \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close> 
    for E and \<EE> :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close> 
      and \<FF> :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  proof -
    have bdd_filter: \<open>bdd_above ((kf_norm \<circ> (\<lambda>f. kf_filter (\<lambda>x. x\<in>E) (\<EE> f))) ` kf_domain \<FF>)\<close>
      apply (rule bdd_above_mono2[OF _ subset_refl, rotated])
      using kf_norm_filter apply blast
      using that
      by (metis (mono_tags, lifting) bdd_above_mono2 comp_apply kf_norm_filter order.refl)
    have aux: \<open>(\<lambda>(x,y). y\<in>E \<and> x=f) = (\<lambda>x. x\<in>{f}\<times>E)\<close>
      by auto
    have *: \<open>kf_filter (\<lambda>x. x\<in>{f}\<times>E) (kf_comp_dependent \<EE> \<FF>)
        = kf_comp_dependent (\<lambda>f. kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
               (kf_filter (\<lambda>x. x=f) \<FF>)\<close>
      using kf_filter_comp_dependent[where \<EE>=\<FF> and \<FF>=\<EE> and F=\<open>\<lambda>_ x. x\<in>E\<close> and E=\<open>\<lambda>x. x=f\<close>,
            OF that]
      unfolding aux by auto
    have \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({f}\<times>E)
      = kf_apply (kf_comp_dependent (\<lambda>f. kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
                                                     (kf_filter (\<lambda>x. x=f) \<FF>))\<close>
      by (auto intro!: simp: kf_apply_on_def * )
    also have \<open>\<dots> = kf_apply
     (kf_comp_dependent (\<lambda>_. kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
       (kf_filter (\<lambda>x. x=f) \<FF>))\<close>
      apply (rule arg_cong[where f="\<lambda>z. kf_apply z"])
      apply (rule kf_comp_dependent_cong_left)
      using bdd_filter by auto
    also have \<open>\<dots> = kf_apply (kf_comp (kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
       (kf_filter (\<lambda>x. x=f) \<FF>))\<close>
      by (simp add: kf_comp_def)
    finally show ?thesis
      by -
  qed

  have rew_\<EE>: \<open>kf_apply (kf_filter (\<lambda>x. x\<in>E) (\<EE> f))
      = kf_apply (kf_filter (\<lambda>x. x\<in>E') (\<EE>' f))\<close>
    if \<open>f \<in> kf_domain \<FF>\<close>
    using assms(3)[OF that]
    by (simp add: kf_apply_on_def)
  have rew_\<FF>: \<open>kf_apply (kf_filter (\<lambda>f'. f' = f) \<FF>')
     = kf_apply (kf_filter (\<lambda>f'. f' = f) \<FF>)\<close>
    using assms(4)
    by (simp add: kf_apply_on_def)
  have \<FF>_0: \<open>kf_apply (kf_filter (\<lambda>f'. f' = f) \<FF>) = 0\<close>
    if \<open>f \<notin> kf_domain \<FF>\<close>
  proof -
(*     have *: \<open>(x = f \<and> x \<in> kf_domain \<FF>) \<longleftrightarrow> False\<close> for x
      using that by simp *)

    have \<open>kf_filter (\<lambda>f'. f' = f) \<FF> \<equiv>\<^sub>k\<^sub>r
             kf_filter (\<lambda>f'. f' = f) (kf_filter (\<lambda>x. x \<in> kf_domain \<FF>) \<FF>)\<close>
      by (auto intro!: kf_filter_cong intro: kf_eq_sym simp: kf_filter_to_domain)
    also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r (kf_filter (\<lambda>_. False) \<FF>)\<close>
      using that apply (simp add: kf_filter_twice del: kf_filter_false)
      by (smt (verit) kf_eq_def kf_filter_cong_eq)
    also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r 0\<close>
      by (simp add: kf_filter_false)
    finally show ?thesis
      by (metis kf_apply_0 kf_eq_imp_eq_weak kf_eq_weak_def)
  qed

  show \<open>kf_comp_dependent \<EE> \<FF> *\<^sub>k\<^sub>r @({f} \<times> E) \<rho> =
    kf_comp_dependent \<EE>' \<FF>' *\<^sub>k\<^sub>r @({f} \<times> E') \<rho>\<close>
    apply (cases \<open>f \<in> kf_domain \<FF>\<close>)
    by (auto intro!: ext simp add: rewrite_comp[OF bdd] rewrite_comp[OF bdd']
        kf_comp_apply rew_\<EE> rew_\<FF> \<FF>_0)
qed



lemma kf_comp_dependent_cong_weak:
  fixes \<EE> :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e1) kraus_family\<close>
    and \<EE>' :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e2) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  assumes bdd: \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes eq: \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> \<EE> x =\<^sub>k\<^sub>r \<EE>' x\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> =\<^sub>k\<^sub>r kf_comp_dependent \<EE>' \<FF>'\<close>
proof -
  have \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({f}\<times>UNIV) = kf_apply_on (kf_comp_dependent \<EE>' \<FF>') ({f}\<times>UNIV)\<close> for f
  proof -
    note bdd
    moreover have \<open>bdd_above ((kf_norm \<circ> \<EE>') ` kf_domain \<FF>')\<close>
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) comp_apply image_cong kf_norm_cong kf_domain_cong)
    moreover have \<open>kf_apply_on (\<EE> x) UNIV = kf_apply_on (\<EE>' x) UNIV\<close> if \<open>x \<in> kf_domain \<FF>\<close> for x
      using assms(2) kf_eq_weak_def that
      by (metis kf_apply_on_UNIV)
    moreover have \<open>kf_apply_on \<FF> {f} = kf_apply_on \<FF>' {f}\<close>
      by (meson assms(3) kf_eq_def)
    ultimately show ?thesis
      by (rule kf_apply_comp_dependent_cong)
  qed
  then have \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) (\<Union>f. {f}\<times>UNIV) = kf_apply_on (kf_comp_dependent \<EE>' \<FF>') (\<Union>f. {f}\<times>UNIV)\<close>
    apply (rule_tac ext)
    apply (rule kf_apply_on_union_eqI[where F=\<open>range (\<lambda>f. ({f}\<times>UNIV,{f}\<times>UNIV))\<close>])
    by auto
  moreover have \<open>(\<Union>f. {f} \<times> UNIV) = UNIV\<close>
    by fast
  ultimately show ?thesis
    by (metis kf_eq_weak_def kf_apply_on_UNIV)
qed


lemma kf_comp_dependent_assoc: 
  fixes \<EE> :: \<open>'g \<Rightarrow> 'f \<Rightarrow> ('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>'g \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  assumes bdd_E: \<open>bdd_above ((kf_norm o case_prod \<EE>) ` (SIGMA x:kf_domain \<GG>. kf_domain (\<FF> x)))\<close>
  assumes bdd_F: \<open>bdd_above ((kf_norm o \<FF>) ` kf_domain \<GG>)\<close>
  shows \<open>(kf_comp_dependent (\<lambda>g. kf_comp_dependent (\<EE> g) (\<FF> g)) \<GG>) \<equiv>\<^sub>k\<^sub>r
  kf_map (\<lambda>((g,f),e). (g,f,e)) (kf_comp_dependent (\<lambda>(g,f). \<EE> g f) (kf_comp_dependent \<FF> \<GG>))\<close>
    (is \<open>?lhs \<equiv>\<^sub>k\<^sub>r ?rhs\<close>)
proof (rule kf_eqI)
  fix gfe :: \<open>'g \<times> 'f \<times> 'e\<close> and \<rho>
  obtain g f e where gfe_def: \<open>gfe = (g,f,e)\<close>
    apply atomize_elim
    apply (rule exI[of _ \<open>fst gfe\<close>])
    apply (rule exI[of _ \<open>fst (snd gfe)\<close>])
    apply (rule exI[of _ \<open>snd (snd gfe)\<close>])
    by simp
  have aux: \<open>(\<lambda>x. (fst (fst x), snd (fst x), snd x) = gfe) = (\<lambda>x. x=((g,f),e))\<close>
    by (auto simp: gfe_def)
  have bdd1: \<open>bdd_above ((\<lambda>x. kf_norm (kf_filter (\<lambda>x. x = f) (\<FF> x))) ` kf_domain \<GG>)\<close>
    using kf_norm_filter bdd_F
    by (metis (mono_tags, lifting) bdd_above_mono2 o_apply order.refl)
  from bdd_E have bdd2: \<open>bdd_above ((kf_norm \<circ> \<EE> g) ` kf_domain (\<FF> g))\<close> if \<open>g \<in> kf_domain \<GG>\<close> for g
    apply (rule bdd_above_mono)
    using that
    by (force simp: image_iff)
  from bdd_E have bdd3: \<open>bdd_above ((\<lambda>x. kf_norm (kf_filter (\<lambda>x. x = e) (case_prod \<EE> x))) ` (SIGMA x:kf_domain \<GG>. kf_domain (\<FF> x)))\<close>
    apply (rule bdd_above_mono2)
    by (auto simp: kf_norm_filter)
  then have bdd4: \<open>bdd_above ((\<lambda>x. kf_norm (kf_filter (\<lambda>x. x = e) (\<EE> (fst x) (snd x)))) ` X)\<close>
    if \<open>X \<subseteq> (SIGMA x:kf_domain \<GG>. kf_domain (\<FF> x))\<close> for X
    apply (rule bdd_above_mono2)
    using that by (auto simp: bdd_above_def)
  have bdd5: \<open>bdd_above ((kf_norm \<circ> (\<lambda>g. kf_comp_dependent (\<EE> g) (\<FF> g))) ` X)\<close> 
    if X\<GG>: \<open>X \<subseteq> kf_domain \<GG>\<close> for X
  proof -
    from bdd_E
    obtain BE' where BE': \<open>g \<in> kf_domain \<GG> \<Longrightarrow> x \<in> kf_domain (\<FF> g) \<Longrightarrow> kf_norm (\<EE> g x) \<le> BE'\<close> for g x
      by (auto simp: bdd_above_def)
    define BE where \<open>BE = max BE' 0\<close>
    from BE' have BE: \<open>g \<in> kf_domain \<GG> \<Longrightarrow> x \<in> kf_domain (\<FF> g) \<Longrightarrow> kf_norm (\<EE> g x) \<le> BE\<close> and \<open>BE \<ge> 0\<close> for g x
      by (force simp: BE_def)+
    then have \<open>BE \<ge> 0\<close>
      by (smt (z3) kf_norm_geq0)
    from bdd_F obtain BF where BF: \<open>kf_norm (\<FF> x) \<le> BF\<close> if \<open>x \<in> kf_domain \<GG>\<close> for x
      by (auto simp: bdd_above_def)
    have \<open>kf_norm (kf_comp_dependent (\<EE> g) (\<FF> g))
                  \<le> BE * kf_norm (\<FF> g)\<close> if \<open>g \<in> kf_domain \<GG>\<close> for g
      apply (rule kf_comp_dependent_norm_leq[OF BE \<open>BE \<ge> 0\<close>])
      using that by auto
    then have \<open>kf_norm (kf_comp_dependent (\<EE> g) (\<FF> g)) \<le> BE * BF\<close> if \<open>g \<in> kf_domain \<GG>\<close> for g
      apply (rule order_trans)
      using BF \<open>BE \<ge> 0\<close> that
      by (auto intro!: mult_left_mono)
    with X\<GG> show ?thesis
      by (auto intro!: bdd_aboveI)
  qed

  have \<open>?lhs *\<^sub>k\<^sub>r @{gfe} \<rho>
       = kf_comp_dependent 
            (\<lambda>g. kf_filter (\<lambda>x. x=(f,e)) (kf_comp_dependent (\<EE> g) (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    unfolding kf_apply_on_def
    apply (subst kf_filter_comp_dependent[symmetric])
     apply (rule bdd5, rule order_refl)
    apply (subst asm_rl[of \<open>(\<lambda>(x, y). y = (f, e) \<and> x = g) = (\<lambda>x. x \<in> {gfe})\<close>])
    by (auto simp: gfe_def)
  also have \<open>\<dots> = kf_comp_dependent
            (\<lambda>g. kf_comp_dependent
                       (\<lambda>f. kf_filter (\<lambda>x. x=e) (\<EE> g f)) (kf_filter (\<lambda>x. x=f) (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule kf_apply_eqI)
    apply (rule kf_comp_dependent_cong_weak[OF _ _ kf_eq_refl])
     apply fastforce
    apply (subst kf_filter_comp_dependent[symmetric])
    using bdd2 apply fastforce
    apply (subst asm_rl[of \<open>(\<lambda>(ea, fa). fa = e \<and> ea = f) = (\<lambda>x. x = (f, e))\<close>])
    by auto
  also have \<open>\<dots> = kf_comp_dependent
            (\<lambda>_. kf_comp_dependent
                       (\<lambda>f. kf_filter (\<lambda>x. x=e) (\<EE> g f)) (kf_filter (\<lambda>x. x=f) (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_apply t \<rho>\<close>])
    apply (rule kf_comp_dependent_cong_left)
    by (auto intro!: simp: kf_domain.rep_eq kf_filter.rep_eq)
  also have \<open>\<dots> = kf_comp_dependent
            (\<lambda>_. kf_comp_dependent
                       (\<lambda>_. kf_filter (\<lambda>x. x=e) (\<EE> g f)) (kf_filter (\<lambda>x. x=f) (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_comp_dependent t _ *\<^sub>k\<^sub>r \<rho>\<close>])
    apply (rule ext)
    apply (rule kf_comp_dependent_cong_left)
    by (auto intro!: simp: kf_domain.rep_eq kf_filter.rep_eq)
  also have \<open>\<dots> = kf_comp
            (kf_comp
                       (kf_filter (\<lambda>x. x=e) (\<EE> g f)) (kf_filter (\<lambda>x. x=f) (\<FF> g)))
            (kf_filter (\<lambda>x. x=g) \<GG>) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_comp_def)
  also have \<open>\<dots> = kf_comp (kf_filter (\<lambda>x. x=e) (\<EE> g f))
                          (kf_comp (kf_filter (\<lambda>x. x=f) (\<FF> g)) (kf_filter (\<lambda>x. x=g) \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_comp_assoc_weak[unfolded kf_eq_weak_def])
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>_. kf_filter (\<lambda>x. x=e) (\<EE> g f))
            (kf_comp_dependent (\<lambda>_. kf_filter (\<lambda>x. x=f) (\<FF> g))
                                         (kf_filter (\<lambda>x. x=g) \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_comp_def)
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>(g,f). kf_filter (\<lambda>x. x=e) (\<EE> g f))
            (kf_comp_dependent (\<lambda>_. kf_filter (\<lambda>x. x=f) (\<FF> g))
                                         (kf_filter (\<lambda>x. x=g) \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. t *\<^sub>k\<^sub>r \<rho>\<close>])
    apply (rule kf_comp_dependent_cong_left)
    apply force
    using kf_domain_comp_dependent_subset apply (fastforce intro!: bdd4 simp: o_def case_prod_unfold)
    using kf_domain_comp_dependent_subset[of \<open>(\<lambda>_. kf_filter (\<lambda>x. x = f) (\<FF> g))\<close> \<open>kf_filter (\<lambda>x. x = g) \<GG>\<close>]
    by (auto intro!: simp: kf_filter.rep_eq case_prod_unfold)
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>(g,f). kf_filter (\<lambda>x. x=e) (\<EE> g f))
            (kf_comp_dependent (\<lambda>g. kf_filter (\<lambda>x. x=f) (\<FF> g))
                                         (kf_filter (\<lambda>x. x=g) \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kf_comp_dependent _ t *\<^sub>k\<^sub>r _\<close>])
    apply (rule kf_comp_dependent_cong_left)
    by (auto intro!: simp: kf_domain.rep_eq kf_filter.rep_eq)
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>(g,f). kf_filter (\<lambda>x. x=e) (\<EE> g f))
            (kf_filter (\<lambda>x. x=(g,f)) (kf_comp_dependent \<FF> \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (subst kf_filter_comp_dependent[symmetric])
    using bdd_F apply (simp add: bdd_above_mono2)
    apply (subst asm_rl[of \<open>(\<lambda>(e, fa). fa = f \<and> e = g) = (\<lambda>x. x = (g, f))\<close>])
    by auto
  also have \<open>\<dots> = kf_filter (\<lambda>x. x=((g,f),e))
       (kf_comp_dependent (\<lambda>(g,f). \<EE> g f) (kf_comp_dependent \<FF> \<GG>)) *\<^sub>k\<^sub>r \<rho>\<close>
    unfolding case_prod_beta
    apply (subst kf_filter_comp_dependent[symmetric])
    using bdd_E kf_domain_comp_dependent_subset[of \<FF> \<GG>] apply (fastforce simp: bdd_above_def)
    apply (subst asm_rl[of \<open>(\<lambda>(ea, fa). fa = e \<and> ea = (g, f)) = (\<lambda>x. x = ((g, f), e))\<close>])
    by auto
  also have \<open>\<dots> = kf_filter (\<lambda>x. x=gfe)
        (kf_map (\<lambda>((g, f), e). (g, f, e))
       (kf_comp_dependent (\<lambda>(g,f). \<EE> g f) (kf_comp_dependent \<FF> \<GG>))) *\<^sub>k\<^sub>r \<rho>\<close>
    apply (simp add: kf_filter_map case_prod_beta aux)
    apply (subst aux)
    by simp
  also have \<open>\<dots> = ?rhs *\<^sub>k\<^sub>r @{gfe} \<rho>\<close>
    by (simp add: kf_apply_on_def)
  finally show \<open>?lhs *\<^sub>k\<^sub>r @{gfe} \<rho> = ?rhs *\<^sub>k\<^sub>r @{gfe} \<rho>\<close>
    by -
qed

lemma kf_comp_dependent_assoc_weak:
  fixes \<EE> :: \<open>'g \<Rightarrow> 'f \<Rightarrow> ('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>'g \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  assumes bdd_E: \<open>bdd_above ((kf_norm o case_prod \<EE>) ` (SIGMA x:kf_domain \<GG>. kf_domain (\<FF> x)))\<close>
  assumes bdd_F: \<open>bdd_above ((kf_norm o \<FF>) ` kf_domain \<GG>)\<close>
  shows \<open>kf_comp_dependent (\<lambda>g. kf_comp_dependent (\<EE> g) (\<FF> g)) \<GG> =\<^sub>k\<^sub>r
         kf_comp_dependent (\<lambda>(g,f). \<EE> g f) (kf_comp_dependent \<FF> \<GG>)\<close>
  using kf_comp_dependent_assoc[OF assms, THEN kf_eq_imp_eq_weak]
  by (metis (no_types, lifting) kf_apply_map kf_eq_weak_def)

lemma kf_comp_dependent_comp_assoc_weak:
  fixes \<EE> :: \<open>('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>'g \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  assumes \<open>bdd_above ((kf_norm o \<FF>) ` kf_domain \<GG>)\<close>
  shows \<open>kf_comp_dependent (\<lambda>g. kf_comp \<EE> (\<FF> g)) \<GG> =\<^sub>k\<^sub>r
         kf_comp \<EE> (kf_comp_dependent \<FF> \<GG>)\<close>
  using kf_comp_dependent_assoc_weak[where \<EE>=\<open>\<lambda>_ _. \<EE>\<close> and \<GG>=\<GG>, OF _ assms]
  by (fastforce simp: case_prod_unfold kf_comp_def)

lemma kf_comp_comp_dependent_assoc_weak:
  fixes \<EE> :: \<open>'f \<Rightarrow> ('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  assumes bdd_E: \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp (kf_comp_dependent \<EE> \<FF>) \<GG> =\<^sub>k\<^sub>r
         kf_comp_dependent (\<lambda>(_,f). \<EE> f) (kf_comp \<FF> \<GG>)\<close>
proof -
  from bdd_E have \<open>bdd_above ((kf_norm \<circ> (\<lambda>(g, y). \<EE> y)) ` (kf_domain \<GG> \<times> kf_domain \<FF>))\<close>
    by (auto intro!: simp: bdd_above_def)
  then have \<open>kf_comp_dependent (\<lambda>_. kf_comp_dependent \<EE> \<FF>) \<GG> =\<^sub>k\<^sub>r kf_comp_dependent (\<lambda>(_, f). \<EE> f) (kf_comp_dependent (\<lambda>_. \<FF>) \<GG>)\<close>
    apply (rule kf_comp_dependent_assoc_weak)
    by auto
  then show ?thesis
    by (simp add: case_prod_unfold kf_comp_def)
qed

lemma kf_comp_assoc:
  fixes \<EE> :: \<open>('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  shows \<open>kf_comp (kf_comp \<EE> \<FF>) \<GG> \<equiv>\<^sub>k\<^sub>r
   kf_map (\<lambda>((g,f),e). (g,f,e)) (kf_comp \<EE> (kf_comp \<FF> \<GG>))\<close>
  apply (simp add: kf_comp_def)
  apply (rule kf_eq_trans)
   apply (rule kf_comp_dependent_assoc)
  by (auto simp: case_prod_unfold)

lemma kf_comp_dependent_cong:
  fixes \<EE> \<EE>' :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  assumes bdd: \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  assumes \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> \<EE> x \<equiv>\<^sub>k\<^sub>r \<EE>' x\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> \<equiv>\<^sub>k\<^sub>r kf_comp_dependent \<EE>' \<FF>'\<close>
proof (rule kf_eqI)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  fix x :: \<open>'f \<times> 'e\<close>

  note bdd
  moreover have bdd': \<open>bdd_above ((kf_norm \<circ> \<EE>') ` kf_domain \<FF>')\<close>
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) image_cong kf_eq_imp_eq_weak kf_norm_cong kf_domain_cong o_apply)
  moreover have \<open>kf_apply_on (\<EE> xa) {snd x} = kf_apply_on (\<EE>' xa) {snd x}\<close> if \<open>xa \<in> kf_domain \<FF>\<close> for xa
    by (meson assms(2) kf_eq_def that)
  moreover have \<open>kf_apply_on \<FF> {fst x} = kf_apply_on \<FF>' {fst x}\<close>
    by (meson assms(3) kf_eq_def)
  ultimately have \<open>kf_apply_on (kf_comp_dependent \<EE> \<FF>) ({fst x} \<times> {snd x}) = kf_apply_on (kf_comp_dependent \<EE>' \<FF>') ({fst x} \<times> {snd x})\<close>
    by (rule kf_apply_comp_dependent_cong)
  then show \<open>kf_comp_dependent \<EE> \<FF> *\<^sub>k\<^sub>r @{x} \<rho> = kf_comp_dependent \<EE>' \<FF>' *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by simp
qed


lemma kf_comp_cong:
  fixes \<EE> \<EE>' :: \<open>('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<EE>'\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_comp \<EE> \<FF> \<equiv>\<^sub>k\<^sub>r kf_comp \<EE>' \<FF>'\<close>
  by (auto intro!: kf_comp_dependent_cong assms
      simp add: kf_comp_def)

lemma kf_bound_comp_dependent_raw_of_op:
  shows \<open>kf_bound (kf_comp_dependent_raw \<EE> (kf_of_op U))
       = sandwich (U*) (kf_bound (\<EE> ()))\<close>
proof -
  write compose_wot (infixl "o\<^sub>W" 55)
  define EE where \<open>EE = Rep_kraus_family (\<EE> ())\<close>

  have sum1: \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) EE\<close>
    by (simp add: EE_def kf_bound_summable)
  then have sum2: \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). U* o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E)) EE\<close>
    by (simp add: case_prod_unfold summable_on_in_wot_compose_left)

  have \<open>kf_bound (kf_comp_dependent_raw \<EE> (kf_of_op U)) = 
        infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
          (Set.filter (\<lambda>(EF,_). EF \<noteq> 0) (((\<lambda>((F, y), (E, x)). ((E o\<^sub>C\<^sub>L F, F, E, y, x))) ` (SIGMA (F, y):if U=0 then {} else {(U, ())}. EE))))\<close>
    by (simp add: kf_bound.rep_eq kf_comp_dependent_raw.rep_eq kf_of_op.rep_eq EE_def)
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
          ((\<lambda>((F, y), (E, x)). ((E o\<^sub>C\<^sub>L F, F, E, y, x))) ` (SIGMA (F, y):{(U, ())}. EE))\<close>
    apply (cases \<open>U=0\<close>; rule infsum_in_cong_neutral)
    by force+
  also have \<open>\<dots>  = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
                   ((\<lambda>(E,x). (E o\<^sub>C\<^sub>L U, U, E, (), x)) ` EE)\<close>
    apply (rule arg_cong[where f=\<open>infsum_in _ _\<close>])
    by force
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). (E o\<^sub>C\<^sub>L U)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L U)) EE\<close>
    apply (subst infsum_in_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold infsum_in_reindex)
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). U* o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L U) EE\<close>
    by (metis (no_types, lifting) adj_cblinfun_compose cblinfun_assoc_left(1))
  also have \<open>\<dots> = U* o\<^sub>C\<^sub>L infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) EE o\<^sub>C\<^sub>L U\<close>
    using sum1 sum2 by (simp add: case_prod_unfold infsum_in_wot_compose_right infsum_in_wot_compose_left)
  also have \<open>\<dots> = sandwich (U*) (kf_bound (\<EE> ()))\<close>
    by (simp add: EE_def kf_bound.rep_eq sandwich_apply)
  finally show ?thesis
    by -
qed


lemma kf_bound_comp_dependent_of_op:
  shows \<open>kf_bound (kf_comp_dependent \<EE> (kf_of_op U)) = sandwich (U*) (kf_bound (\<EE> ()))\<close>
  by (simp add: kf_comp_dependent_def kf_map_bound kf_bound_comp_dependent_raw_of_op)

lemma kf_bound_comp_of_op:
  shows \<open>kf_bound (kf_comp \<EE> (kf_of_op U)) = sandwich (U*) (kf_bound \<EE>)\<close>
  by (simp add: kf_bound_comp_dependent_of_op kf_comp_def)

lemma kf_norm_comp_dependent_of_op_coiso:
  assumes \<open>isometry (U*)\<close>
  shows \<open>kf_norm (kf_comp_dependent \<EE> (kf_of_op U)) = kf_norm (\<EE> ())\<close>
  using assms
  by (simp add: kf_bound_comp_dependent_of_op kf_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')


lemma kf_norm_comp_of_op_coiso:
  assumes \<open>isometry (U*)\<close>
  shows \<open>kf_norm (kf_comp \<EE> (kf_of_op U)) = kf_norm \<EE>\<close>
  using assms
  by (simp add: kf_bound_comp_of_op kf_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')

lemma kf_bound_comp_dependend_raw_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_bound (kf_comp_dependent_raw (\<lambda>_. kf_of_op U) \<EE>)
       = kf_bound \<EE>\<close>
proof -
  write compose_wot (infixl "o\<^sub>W" 55)
  define EE where \<open>EE = Rep_kraus_family \<EE>\<close>

  have \<open>bdd_above ((\<lambda>x. (norm U)\<^sup>2) ` kf_domain \<EE>)\<close>
    by auto
  then have \<open>kf_bound (kf_comp_dependent_raw (\<lambda>_. kf_of_op U) \<EE>) = 
        infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
           (Set.filter (\<lambda>(EF, _). EF \<noteq> 0) ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, ())) ` (SIGMA (F, y):EE. if U=0 then {} else {(U, ())})))\<close>
    by (simp add: kf_bound.rep_eq kf_comp_dependent_raw.rep_eq kf_of_op.rep_eq EE_def)
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
           ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, ())) ` (SIGMA (F, y):EE. {(U, ())}))\<close>
    apply (cases \<open>U = 0\<close>; rule infsum_in_cong_neutral)
    by force+
  also have \<open>\<dots>  = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
                   ((\<lambda>(E,x). (U o\<^sub>C\<^sub>L E, E, U, x, ())) ` EE)\<close>
    apply (rule arg_cong[where f=\<open>infsum_in _ _\<close>])
    by force
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). (U o\<^sub>C\<^sub>L E)* o\<^sub>C\<^sub>L (U o\<^sub>C\<^sub>L E)) EE\<close>
    apply (subst infsum_in_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold infsum_in_reindex)
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L (U* o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L E) EE\<close>
    by (metis (no_types, lifting) adj_cblinfun_compose cblinfun_assoc_left(1))
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) EE\<close>
    using assms by simp
  also have \<open>\<dots> = kf_bound \<EE>\<close>
    by (simp add: EE_def kf_bound.rep_eq sandwich_apply)
  finally show ?thesis
    by -
qed

lemma kf_bound_comp_dependent_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_bound (kf_comp_dependent (\<lambda>_. kf_of_op U) \<EE>) = kf_bound \<EE>\<close>
  using assms by (simp add: kf_comp_dependent_def kf_map_bound kf_bound_comp_dependend_raw_iso)

lemma kf_bound_comp_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_bound (kf_comp (kf_of_op U) \<EE>) = kf_bound \<EE>\<close>
  using assms by (simp add: kf_bound_comp_dependent_iso kf_comp_def)

lemma kf_norm_comp_dependent_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_norm (kf_comp_dependent (\<lambda>_. kf_of_op U) \<EE>) = kf_norm \<EE>\<close>
  using assms
  by (simp add: kf_bound_comp_dependent_iso kf_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')

lemma kf_norm_comp_iso:
  assumes \<open>isometry U\<close>
  shows \<open>kf_norm (kf_comp (kf_of_op U) \<EE>) = kf_norm \<EE>\<close>
  using assms
  by (simp add: kf_bound_comp_iso kf_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')


lemma kf_comp_dependent_raw_0_right[simp]: \<open>kf_comp_dependent_raw \<EE> 0 = 0\<close>
  apply transfer'
  by (auto intro!: simp: zero_kraus_family.rep_eq)

lemma kf_comp_dependent_raw_0_left[simp]: \<open>kf_comp_dependent_raw 0 \<EE> = 0\<close>
  apply transfer'
  by (auto intro!: simp: zero_kraus_family.rep_eq)

lemma kf_comp_dependent_0_left[simp]: \<open>kf_comp_dependent (\<lambda>_. 0) E = 0\<close>
proof -
  have \<open>bdd_above ((kf_norm \<circ> 0) ` kf_domain E)\<close>
    by auto
  then have \<open>kf_comp_dependent 0 E =\<^sub>k\<^sub>r 0\<close>
    by (auto intro!: ext simp: kf_eq_weak_def kf_comp_dependent_apply split_def)
  then have \<open>(kf_comp_dependent 0 E) = 0\<close>
    using kf_eq_0_iff_eq_0 by auto
  then show \<open>kf_comp_dependent (\<lambda>_. 0) E = 0\<close>
    by (simp add: kf_comp_dependent_def zero_fun_def)
qed

lemma kf_comp_dependent_0_right[simp]: \<open>kf_comp_dependent E 0 = 0\<close>
  by (auto intro!: ext simp add: kf_eq_weak_def kf_comp_dependent_def)

lemma kf_comp_0_left[simp]: \<open>kf_comp 0 E = 0\<close>
  using kf_comp_dependent_0_left[of E]
  by (simp add: kf_comp_def zero_fun_def)

lemma kf_comp_0_right[simp]: \<open>kf_comp E 0 = 0\<close>
  using kf_comp_dependent_0_right[of \<open>\<lambda>_. E\<close>]
  by (simp add: kf_comp_def)

lemma kf_filter_comp:
  fixes \<FF> :: \<open>('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'e) kraus_family\<close>
  shows \<open>kf_filter (\<lambda>(e,f). F f \<and> E e) (kf_comp \<FF> \<EE>)
      = kf_comp (kf_filter F \<FF>) (kf_filter E \<EE>)\<close>
  unfolding kf_comp_def
  apply (rule kf_filter_comp_dependent)
  by auto

lemma kf_comp_dependent_invalid:
  assumes \<open>\<not> bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> = 0\<close>
  by (metis (no_types, lifting) Rep_kraus_family_inject assms kf_comp_dependent_def kf_comp_dependent_raw.rep_eq kf_map0 zero_kraus_family.rep_eq)

lemma kf_comp_dependent_map_left:
  \<open>kf_comp_dependent (\<lambda>x. kf_map (f x) (E x)) F
     \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x,y). (x, f x y)) (kf_comp_dependent E F)\<close>
proof (cases \<open>bdd_above ((kf_norm \<circ> E) ` kf_domain F)\<close>)
  case True
  show ?thesis
  proof (rule kf_eqI)
    fix xy :: \<open>'c \<times> 'd\<close> and \<rho>
    obtain x y where xy: \<open>xy = (x, y)\<close>
      by force
    define F' where \<open>F' x = kf_filter (\<lambda>x'. x' = x) F\<close> for x
    define E'f where \<open>E'f y e = kf_filter (\<lambda>x. f e x = y) (E e)\<close> for e y
    have bdd2: \<open>bdd_above ((\<lambda>x. kf_norm (E'f y x)) ` kf_domain (F' x))\<close>
      apply (simp add: E'f_def F'_def)
      by fastforce
    have \<open>kf_comp_dependent (\<lambda>x. kf_map (f x) (E x)) F *\<^sub>k\<^sub>r @{xy} \<rho>
        = kf_filter (\<lambda>(x',y'). y'=y \<and> x'=x) (kf_comp_dependent (\<lambda>x. kf_map (f x) (E x)) F) *\<^sub>k\<^sub>r \<rho>\<close>
      (is \<open>?lhs = _\<close>)
      apply (simp add: kf_apply_on_def xy case_prod_unfold)
      by (metis fst_conv prod.collapse snd_conv)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>e. kf_filter (\<lambda>y'. y' = y)
         (kf_map (f e) (E e))) (F' x)) \<rho>\<close>
      using True by (simp add: kf_filter_comp_dependent F'_def)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent
                 (\<lambda>e. kf_map (f e) (E'f y e)) (F' x)) \<rho>\<close>
      by (simp add: kf_filter_map E'f_def)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (E'f y) (F' x)) \<rho>\<close>
      apply (rule kf_apply_eqI)
      apply (rule kf_comp_dependent_cong_weak)
      by (simp_all add: bdd2 kf_eq_weak_def)
    also have \<open>\<dots> = kf_apply 
       (kf_filter (\<lambda>(x',y'). f x' y' = y \<and> x' = x) (kf_comp_dependent E F)) \<rho>\<close>
      apply (subst kf_filter_comp_dependent)
      using True by (simp_all add: o_def F'_def E'f_def[abs_def])
    also have \<open>\<dots> = kf_apply (kf_map (\<lambda>(x,y). (x, f x y))
       (kf_filter (\<lambda>(x',y'). f x' y' = y \<and> x' = x) (kf_comp_dependent E F))) \<rho>\<close>
      by simp
    also have \<open>\<dots>
      = kf_apply (kf_filter (\<lambda>(x',y'). y'=y \<and> x'=x)
       (kf_map (\<lambda>(x,y). (x, f x y)) (kf_comp_dependent E F))) \<rho>\<close>
      by (simp add: kf_filter_map case_prod_unfold)
    also have \<open>\<dots> = kf_map (\<lambda>(x,y). (x, f x y)) (kf_comp_dependent E F) *\<^sub>k\<^sub>r @{xy} \<rho>\<close>
      apply (simp add: kf_apply_on_def xy case_prod_unfold)
      by (metis fst_conv prod.collapse snd_conv)
    finally show \<open>?lhs = \<dots>\<close>
      by -
  qed
next
  case False
  then show ?thesis
    by (simp add: kf_comp_dependent_invalid)
qed

(* lemma kf_comp_dependent_map_left_weak:
  \<open>kf_comp_dependent (\<lambda>x. kf_map (f x) (E x)) F
     =\<^sub>k\<^sub>r kf_comp_dependent E F\<close>
by - *)

lemma kf_comp_dependent_map_right:
  \<open>kf_comp_dependent E (kf_map f F)
     \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x,y). (f x, y)) (kf_comp_dependent (\<lambda>x. E (f x)) F)\<close>
proof (cases \<open>bdd_above ((kf_norm \<circ> E) ` kf_domain (kf_map f F))\<close>)
  case True
  show ?thesis
  proof (rule kf_eqI)
    fix xy :: \<open>'c \<times> 'd\<close> and \<rho>
    obtain x y where xy: \<open>xy = (x, y)\<close>
      by force
    define F'f where \<open>F'f x = kf_filter (\<lambda>xa. f xa = x) F\<close> for x
    define E' where \<open>E' y e = kf_filter (\<lambda>y'. y' = y) (E e)\<close> for e y
    have bdd2: \<open>bdd_above ((kf_norm \<circ> E' y) ` kf_domain (kf_map f (F'f x)))\<close>
      apply (simp add: E'_def F'f_def)
      by fastforce
    have bdd3: \<open>bdd_above ((kf_norm \<circ> (\<lambda>x. E (f x))) ` kf_domain F)\<close>
      by (metis (no_types, lifting) ext True comp_apply image_comp kf_domain_map)
    have bdd4: \<open>bdd_above ((kf_norm \<circ> (\<lambda>_. E' y x)) ` kf_domain (F'f x))\<close>
      by fastforce                                   
    have \<open>kf_comp_dependent E (kf_map f F) *\<^sub>k\<^sub>r @{xy} \<rho>
        = kf_filter (\<lambda>(x',y'). y'=y \<and> x'=x) (kf_comp_dependent E (kf_map f F)) *\<^sub>k\<^sub>r \<rho>\<close>
      (is \<open>?lhs = _\<close>)
      apply (simp add: kf_apply_on_def xy case_prod_unfold)
      by (metis fst_conv prod.collapse snd_conv)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (E' y) (kf_filter (\<lambda>x'. x' = x) (kf_map f F))) \<rho>\<close>
      using True by (simp add: kf_filter_comp_dependent F'f_def E'_def[abs_def])
    also have \<open>\<dots> = kf_apply (kf_comp_dependent
                 (E' y) (kf_map f (F'f x))) \<rho>\<close>
      by (simp add: kf_filter_map F'f_def)
    also have \<open>\<dots> = kf_apply (kf_comp (E' y x) (kf_map f (F'f x))) \<rho>\<close>
      unfolding kf_comp_def
      apply (rule kf_apply_eqI)
      using bdd2 apply (rule kf_comp_dependent_cong_weak)
      by (auto simp: F'f_def)
    also have \<open>\<dots> = kf_apply (E' y x) (kf_apply (F'f x) \<rho>)\<close>
      by (simp add: kf_comp_apply)
    also have \<open>\<dots> = kf_apply (kf_comp (E' y x) (F'f x)) \<rho>\<close>
      by (simp add: kf_comp_apply)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>e. kf_filter (\<lambda>y'. y' = y) (E (f e))) (F'f x)) \<rho>\<close>
      unfolding kf_comp_def
      apply (rule kf_apply_eqI)
      using bdd4 apply (rule kf_comp_dependent_cong_weak)
      by (auto intro!: simp: F'f_def E'_def)
    also have \<open>\<dots> = kf_apply (kf_filter (\<lambda>(x',y'). y' = y \<and> f x' = x) (kf_comp_dependent (\<lambda>x. E (f x)) F)) \<rho>\<close>
      using bdd3 by (simp add: kf_filter_comp_dependent F'f_def[abs_def] E'_def[abs_def])
    also have \<open>\<dots> = kf_apply (kf_filter (\<lambda>(x',y'). y'=y \<and> x'=x)
              (kf_map (\<lambda>(x, y). (f x, y)) (kf_comp_dependent (\<lambda>x. E (f x)) F))) \<rho>\<close>
      by (simp add: kf_filter_map case_prod_unfold)
    also have \<open>\<dots> = kf_map (\<lambda>(x, y). (f x, y)) (kf_comp_dependent (\<lambda>x. E (f x)) F) *\<^sub>k\<^sub>r @{xy} \<rho>\<close>
      apply (simp add: kf_apply_on_def xy case_prod_unfold)
      by (metis fst_conv prod.collapse snd_conv)

    finally show \<open>?lhs = \<dots>\<close>
      by -
  qed
next
  case False
  have not_bdd2: \<open>\<not> bdd_above ((kf_norm \<circ> (\<lambda>x. E (f x))) ` kf_domain F)\<close>
    by (metis (no_types, lifting) False comp_apply image_comp image_cong kf_domain_map)
  show ?thesis
    using False not_bdd2
    by (simp add: kf_comp_dependent_invalid)
qed

lemma kf_comp_dependent_raw_map_inj_right:
  \<open>kf_comp_dependent_raw E (kf_map_inj f F)
     = kf_map_inj (\<lambda>(E,F,x,y). (E, F, f x, y)) (kf_comp_dependent_raw (\<lambda>x. E (f x)) F)\<close>
proof -
  have \<open>(\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) ` (SIGMA (F, y):Rep_kraus_family (kf_map_inj f F). Rep_kraus_family (E y)) =
           (\<lambda>((F, y),(E,x)). (E o\<^sub>C\<^sub>L F, F, E, f y, x)) ` (SIGMA (F, y):Rep_kraus_family F. Rep_kraus_family (E (f y)))\<close>
    by (auto intro!: image_eqI simp: Sigma_image_left kf_map_inj.rep_eq)
  then show ?thesis
    apply (transfer' fixing: f)
    by (simp add: image_image case_prod_unfold filter_image)
qed

lemma kf_comp_dependent_map_inj_right:
  assumes \<open>inj_on f (kf_domain F)\<close>
  shows \<open>kf_comp_dependent E (kf_map_inj f F)
     = kf_map_inj (\<lambda>(x,y). (f x, y)) (kf_comp_dependent (\<lambda>x. E (f x)) F)\<close>
proof -
  have dom: \<open>kf_domain (kf_comp_dependent_raw (\<lambda>x. E (f x)) F) \<subseteq> UNIV \<times> UNIV \<times> kf_domain F \<times> UNIV\<close>
  proof -
    have \<open>kf_domain (kf_comp_dependent_raw (\<lambda>x. E (f x)) F) \<subseteq> UNIV \<times> UNIV \<times> (SIGMA x:kf_domain F. kf_domain (E (f x)))\<close>
      by (rule kf_domain_comp_dependent_raw_subset)
    also have \<open>\<dots> \<subseteq> UNIV \<times> UNIV \<times> kf_domain F \<times> UNIV\<close>
      by auto
    finally show ?thesis
      by -
  qed
  have inj2: \<open>inj_on (\<lambda>(E, F, x, y). (E, F, f x, y)) (kf_domain (kf_comp_dependent_raw (\<lambda>x. E (f x)) F))\<close>
  proof -
    have \<open>inj_on (\<lambda>(E, F, x, y). (E, F, f x, y)) (UNIV \<times> UNIV \<times> kf_domain F \<times> UNIV)\<close>
      using assms by (auto simp: inj_on_def)
    with dom show ?thesis
      by (rule subset_inj_on[rotated])
  qed
  have inj3: \<open>inj_on (\<lambda>(x, y). (f x, y)) ((\<lambda>(F, E, x). x) ` kf_domain (kf_comp_dependent_raw (\<lambda>x. E (f x)) F))\<close>
  proof -
    from dom have \<open>((\<lambda>(F, E, x). x) ` kf_domain (kf_comp_dependent_raw (\<lambda>x. E (f x)) F)) \<subseteq> kf_domain F \<times> UNIV\<close>
      by auto
    moreover have \<open>inj_on (\<lambda>(x, y). (f x, y)) (kf_domain F \<times> UNIV)\<close>
      using assms by (auto simp: o_def inj_on_def)
    ultimately show ?thesis
      by (rule subset_inj_on[rotated])
  qed
  have \<open>kf_comp_dependent E (kf_map_inj f F) = kf_map (\<lambda>(F, E, y). y) (kf_comp_dependent_raw E (kf_map_inj f F))\<close>
    by (simp add: kf_comp_dependent_def id_def)
  also have \<open>\<dots> = kf_map (\<lambda>(F,E,y). y) (kf_map_inj (\<lambda>(E,F,x,y). (E, F, f x, y)) (kf_comp_dependent_raw (\<lambda>x. E (f x)) F))\<close>
    by (simp add: kf_comp_dependent_raw_map_inj_right)
  also have \<open>\<dots> = kf_map (\<lambda>(E,F,x,y). (f x, y)) (kf_comp_dependent_raw (\<lambda>x. E (f x)) F)\<close>
    apply (subst kf_map_kf_map_inj_comp)
     apply (rule inj2)
    using assms by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = kf_map_inj (\<lambda>(x, y). (f x, y)) (kf_map (\<lambda>(F, E, x). x) (kf_comp_dependent_raw (\<lambda>x. E (f x)) F))\<close>
    apply (subst kf_map_inj_kf_map_comp)
     apply (rule inj3)
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = kf_map_inj (\<lambda>(x,y). (f x, y)) (kf_comp_dependent (\<lambda>x. E (f x)) F)\<close>
    by (simp add: kf_comp_dependent_def id_def)
  finally show ?thesis
    by -
qed

lemma kf_comp_dependent_map_right_weak:
  \<open>kf_comp_dependent E (kf_map f F)
     =\<^sub>k\<^sub>r kf_comp_dependent (\<lambda>x. E (f x)) F\<close>
  by (smt (verit) kf_apply_eqI kf_apply_map kf_comp_dependent_cong kf_comp_dependent_invalid kf_comp_dependent_map_right kf_eq_def
      kf_eq_imp_eq_weak kf_eq_weakI)

lemma kf_comp_map_left:
  \<open>kf_comp (kf_map f E) F \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x,y). (x, f y)) (kf_comp E F)\<close>
  by (simp add: kf_comp_def kf_comp_dependent_map_left)

lemma kf_comp_map_right:
  \<open>kf_comp E (kf_map f F) \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x,y). (f x, y)) (kf_comp E F)\<close>
  using kf_comp_dependent_map_right[where E=\<open>\<lambda>_. E\<close> and f=f and F=F]
  by (simp add: kf_comp_def)

lemma kf_comp_map_both:
  \<open>kf_comp (kf_map e E) (kf_map f F) \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x,y). (f x, e y)) (kf_comp E F)\<close>
  apply (rule kf_comp_map_left[THEN kf_eq_trans])
  apply (rule kf_map_cong[THEN kf_eq_trans, OF refl])
  apply (rule kf_comp_map_right)
  apply (rule kf_map_twice[THEN kf_eq_trans])
  by (simp add: o_def case_prod_unfold)

lemma kf_apply_commute:
  assumes \<open>kf_operators \<FF> \<subseteq> commutant (kf_operators \<EE>)\<close>
  shows \<open>kf_apply \<FF> o kf_apply \<EE> = kf_apply \<EE> o kf_apply \<FF>\<close>
proof (rule eq_from_separatingI[OF separating_density_ops[where B=1], rotated 3])
  show \<open>0 < (1 :: real)\<close>
    by simp
  show \<open>clinear ((*\<^sub>k\<^sub>r) \<FF> \<circ> (*\<^sub>k\<^sub>r) \<EE>)\<close>
    by (simp add: clinear_compose)
  show \<open>clinear ((*\<^sub>k\<^sub>r) \<EE> \<circ> (*\<^sub>k\<^sub>r) \<FF>)\<close>
    using clinear_compose by blast
  fix t :: \<open>('a, 'a) trace_class\<close>
  assume \<open>t \<in> {t. 0 \<le> t \<and> norm t \<le> 1}\<close>
  then have \<open>t \<ge> 0\<close>
    by simp
  from assms
  have \<open>\<forall>E \<in> kf_operators \<EE>. \<forall>F \<in> kf_operators \<FF>. E o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L E\<close>
    unfolding commutant_def by auto
  then show \<open>((*\<^sub>k\<^sub>r) \<FF> \<circ> (*\<^sub>k\<^sub>r) \<EE>) t = ((*\<^sub>k\<^sub>r) \<EE> \<circ> (*\<^sub>k\<^sub>r) \<FF>) t\<close>
  proof (transfer fixing: t, tactic \<open>FILTER (fn st => Thm.nprems_of st = 1) all_tac\<close>)
      (* The FILTER tactic forces the transfer method to produce subgoals where the transferring worked *)
    fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a \<times> 'c) set\<close> and \<FF> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a \<times> 'b) set\<close>
    assume \<open>\<FF> \<in> Collect kraus_family\<close> and \<open>\<EE> \<in> Collect kraus_family\<close>
    then have [iff]: \<open>kraus_family \<FF>\<close>  \<open>kraus_family \<EE>\<close>
      by auto
    assume comm: \<open>\<forall>E\<in>fst ` \<EE>. \<forall>F\<in>fst ` \<FF>. E o\<^sub>C\<^sub>L F = F o\<^sub>C\<^sub>L E\<close>
    have sum1: \<open>(\<lambda>E. sandwich_tc (fst E) t) summable_on \<EE>\<close>
      apply (rule abs_summable_summable)
      apply (rule kf_apply_abs_summable[unfolded case_prod_unfold])
      by simp
    have sum2: \<open>(\<lambda>y. sandwich_tc a (sandwich_tc (fst y) t)) summable_on \<EE>\<close> for a
      apply (rule summable_on_bounded_linear[where h=\<open>sandwich_tc _\<close>])
      by (simp_all add: bounded_clinear.bounded_linear bounded_clinear_sandwich_tc sum1)
    have sum3: \<open>(\<lambda>F. sandwich_tc (fst F) t) summable_on \<FF>\<close> for t
      apply (rule abs_summable_summable)
      apply (rule kf_apply_abs_summable[unfolded case_prod_unfold])
      by simp

    have \<open>((\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>F\<in>\<FF>. sandwich_tc (fst F) \<rho>) \<circ> (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>)) t
      = (\<Sum>\<^sub>\<infinity>F\<in>\<FF>. \<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst F) (sandwich_tc (fst E) t))\<close>  (is \<open>?lhs = _\<close>)
      apply (subst infsum_bounded_linear[where h=\<open>sandwich_tc _\<close>])
      by (simp_all add: bounded_clinear.bounded_linear bounded_clinear_sandwich_tc sum1)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>\<EE>. \<Sum>\<^sub>\<infinity>F\<in>\<FF>. sandwich_tc (fst F) (sandwich_tc (fst E) t))\<close>
      apply (rule infsum_swap_positive_tc)
      using \<open>t \<ge> 0\<close> by (simp_all add: sum2 sum3 sandwich_tc_pos)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>\<EE>. \<Sum>\<^sub>\<infinity>F\<in>\<FF>. sandwich_tc (fst E) (sandwich_tc (fst F) t))\<close>
      apply (intro infsum_cong)
      apply (subst sandwich_tc_compose[THEN fun_cong, unfolded o_def, symmetric])+
      using comm
      by simp
    also have \<open>\<dots> = ((\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>F\<in>\<EE>. sandwich_tc (fst F) \<rho>) \<circ> (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>E\<in>\<FF>. sandwich_tc (fst E) \<rho>)) t\<close>
      apply (subst infsum_bounded_linear[where h=\<open>sandwich_tc _\<close>])
      by (simp_all add: bounded_clinear.bounded_linear bounded_clinear_sandwich_tc sum3)
    finally show \<open>?lhs = \<dots>\<close>
      by -
  qed
qed

lemma kf_comp_commute_weak:
  assumes \<open>kf_operators \<FF> \<subseteq> commutant (kf_operators \<EE>)\<close>
  shows \<open>kf_comp \<FF> \<EE> =\<^sub>k\<^sub>r kf_comp \<EE> \<FF>\<close>
  apply (rule kf_eq_weakI)
  apply (simp add: kf_comp_apply)
  using  kf_apply_commute[OF assms, unfolded o_def]
  by meson

lemma kf_comp_commute:
  assumes \<open>kf_operators \<FF> \<subseteq> commutant (kf_operators \<EE>)\<close>
  shows \<open>kf_comp \<FF> \<EE> \<equiv>\<^sub>k\<^sub>r kf_map prod.swap (kf_comp \<EE> \<FF>)\<close>
proof (rule kf_eqI_from_filter_eq_weak)
  fix xy :: \<open>'c \<times> 'b\<close>
  obtain x y where xy: \<open>xy = (x,y)\<close>
    by (simp add: prod_eq_iff)
  have *: \<open>kf_operators (kf_filter ((=) y) \<FF>) \<subseteq> commutant (kf_operators (kf_filter ((=) x) \<EE>))\<close>
    using kf_operators_filter commutant_antimono[OF kf_operators_filter] assms
    by fastforce
  have \<open>kf_filter ((=) xy) (kf_comp \<FF> \<EE>) = kf_comp (kf_filter ((=) y) \<FF>) (kf_filter ((=) x) \<EE>)\<close>
    apply (simp add: xy prod_eq_iff[abs_def] case_prod_unfold flip: kf_filter_comp)
    by meson
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_comp (kf_filter ((=) x) \<EE>) (kf_filter ((=) y) \<FF>)\<close>
    apply (rule kf_comp_commute_weak)
    by (simp add: * )
  also have \<open>\<dots> = kf_filter ((=) (prod.swap xy)) (kf_comp \<EE> \<FF>)\<close>
    apply (simp add: xy prod_eq_iff[abs_def] case_prod_unfold flip: kf_filter_comp)
    by meson
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_filter ((=) xy) (kf_map prod.swap (kf_comp \<EE> \<FF>))\<close>
    apply (simp add: kf_filter_map)
    by (metis (mono_tags, lifting) kf_eq_refl kf_eq_weak_kf_map_right kf_filter_cong_weak swap_swap)
  finally show \<open>kf_filter ((=) xy) (kf_comp \<FF> \<EE>) =\<^sub>k\<^sub>r kf_filter ((=) xy) (kf_map prod.swap (kf_comp \<EE> \<FF>))\<close>
    by -
qed

lemma kf_comp_apply_on_singleton:
  \<open>kf_comp \<EE> \<FF> *\<^sub>k\<^sub>r @{x} \<rho> = \<EE> *\<^sub>k\<^sub>r @{snd x} (\<FF> *\<^sub>k\<^sub>r @{fst x} \<rho>)\<close>
proof -
  have \<open>kf_comp \<EE> \<FF> *\<^sub>k\<^sub>r @{x} \<rho> = kf_filter (\<lambda>(x1,x2). x2 = snd x \<and> x1 = fst x) (kf_comp \<EE> \<FF>) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_apply_on_def prod_eq_iff case_prod_unfold conj_commute)
  also have \<open>\<dots> = kf_comp (kf_filter (\<lambda>x2. x2 = snd x) \<EE>) (kf_filter (\<lambda>x1. x1 = fst x) \<FF>) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_filter_comp)
  also have \<open>\<dots> = \<EE> *\<^sub>k\<^sub>r @{snd x} (\<FF> *\<^sub>k\<^sub>r @{fst x} \<rho>)\<close>
    by (simp add: kf_apply_on_def kf_comp_apply)
  finally show ?thesis
    by -
qed

lemma kf_comp_dependent_apply_on_singleton:
  assumes \<open>bdd_above ((kf_norm \<circ> \<EE>) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent \<EE> \<FF> *\<^sub>k\<^sub>r @{x} \<rho> = \<EE> (fst x) *\<^sub>k\<^sub>r @{snd x} (\<FF> *\<^sub>k\<^sub>r @{fst x} \<rho>)\<close>
proof -
  have \<open>kf_comp_dependent \<EE> \<FF> *\<^sub>k\<^sub>r @{x} \<rho> = kf_comp_dependent \<EE> \<FF> *\<^sub>k\<^sub>r @({fst x}\<times>{snd x}) \<rho>\<close>
    by fastforce
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>_. \<EE> (fst x)) \<FF> *\<^sub>k\<^sub>r @({fst x}\<times>{snd x}) \<rho>\<close>
    apply (rule kf_apply_comp_dependent_cong[THEN fun_cong])
    using assms by auto
  also have \<open>\<dots> = kf_comp (\<EE> (fst x)) \<FF> *\<^sub>k\<^sub>r @({x}) \<rho>\<close>
    by (simp add: kf_comp_def)
  also have \<open>\<dots> = \<EE> (fst x) *\<^sub>k\<^sub>r @{snd x} (\<FF> *\<^sub>k\<^sub>r @{fst x} \<rho>)\<close>
    by (simp add: kf_comp_apply_on_singleton)
  finally show ?thesis
    by -
qed

lemma kf_comp_id_left: \<open>kf_comp kf_id \<EE> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>x. (x,())) \<EE>\<close>
proof (rule kf_eqI_from_filter_eq_weak)
  fix xy :: \<open>'c \<times> unit\<close>
  define x where \<open>x = fst xy\<close>
  then have xy: \<open>xy = (x,())\<close>
    by (auto intro!: prod.expand)
  have \<open>kf_filter ((=) xy) (kf_comp kf_id \<EE>) = kf_comp (kf_filter (\<lambda>_. True) kf_id) (kf_filter ((=)x) \<EE>)\<close>
    by (auto intro!: arg_cong2[where f=kf_filter] simp add: xy simp flip: kf_filter_comp simp del: kf_filter_true)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_filter ((=)x) \<EE>\<close>
    by (simp add: kf_comp_apply kf_eq_weakI)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_map (\<lambda>x. (x,())) (kf_filter ((=)x) \<EE>)\<close>
    by (simp add: kf_eq_weak_def)
  also have \<open>\<dots> = kf_filter ((=) xy) (kf_map (\<lambda>x. (x,())) \<EE>)\<close>
    by (simp add: kf_filter_map xy)
  finally show \<open>kf_filter ((=) xy) (kf_comp kf_id \<EE>) =\<^sub>k\<^sub>r \<dots>\<close>
    by -
qed

lemma kf_comp_id_right: \<open>kf_comp \<EE> kf_id \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>x. ((),x)) \<EE>\<close>
proof (rule kf_eqI_from_filter_eq_weak)
  fix xy :: \<open>unit \<times> 'c\<close>
  define y where \<open>y = snd xy\<close>
  then have xy: \<open>xy = ((),y)\<close>
    by (auto intro!: prod.expand simp: y_def)
  have \<open>kf_filter ((=) xy) (kf_comp \<EE> kf_id) = kf_comp (kf_filter ((=)y) \<EE>) (kf_filter (\<lambda>_. True) kf_id)\<close>
    by (auto intro!: arg_cong2[where f=kf_filter] simp add: xy simp flip: kf_filter_comp simp del: kf_filter_true)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_filter ((=)y) \<EE>\<close>
    by (simp add: kf_comp_apply kf_eq_weakI)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_map (Pair ()) (kf_filter ((=)y) \<EE>)\<close>
    by (simp add: kf_eq_weak_def)
  also have \<open>\<dots> = kf_filter ((=) xy) (kf_map (\<lambda>x. ((),x)) \<EE>)\<close>
    by (simp add: kf_filter_map xy)
  finally show \<open>kf_filter ((=) xy) (kf_comp \<EE> kf_id) =\<^sub>k\<^sub>r \<dots>\<close>
    by -
qed

lemma kf_comp_dependent_raw_kf_plus_left:
  fixes \<DD> :: \<open>'f \<Rightarrow> ('b::chilbert_space, 'c::chilbert_space, 'd) kraus_family\<close>
  fixes \<EE> :: \<open>'f \<Rightarrow> ('b::chilbert_space, 'c::chilbert_space, 'e) kraus_family\<close>
  fixes \<FF> :: \<open>('a::chilbert_space, 'b, 'f) kraus_family\<close>
  assumes \<open>bdd_above ((\<lambda>x. kf_norm (\<DD> x)) ` kf_domain \<FF>)\<close>
  assumes \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> x)) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent_raw (\<lambda>x. kf_plus (\<DD> x) (\<EE> x)) \<FF> =
    kf_map_inj (\<lambda>x. case x of Inl (F,D,f,d) \<Rightarrow> (F, D, f, Inl d) | Inr (F,E,f,e) \<Rightarrow> (F, E, f, Inr e))
               (kf_plus (kf_comp_dependent_raw \<DD> \<FF>) (kf_comp_dependent_raw \<EE> \<FF>))\<close>
proof (rule Rep_kraus_family_inject[THEN iffD1], rule Set.set_eqI, rename_tac tuple)
  fix tuple :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'c) \<times> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> ('b \<Rightarrow>\<^sub>C\<^sub>L 'c) \<times> 'f \<times> ('d + 'e)\<close>
  have [simp]: \<open>bdd_above ((\<lambda>x. kf_norm (kf_plus (\<DD> x) (\<EE> x))) ` kf_domain \<FF>)\<close>
    apply (rule bdd_above_mono2[rotated])
      apply (rule order_refl)
     apply (rule kf_norm_triangle)
    using assms by (rule bdd_above_plus)
  obtain EF F E f y where tuple: \<open>tuple = (EF,F,E,f,y)\<close>
    by (auto simp: prod_eq_iff)
  have \<open>tuple \<in> Rep_kraus_family (kf_comp_dependent_raw (\<lambda>x. kf_plus (\<DD> x) (\<EE> x)) \<FF>)
    \<longleftrightarrow> EF = E o\<^sub>C\<^sub>L F \<and> EF \<noteq> 0 \<and> (F,f) \<in> Rep_kraus_family \<FF> \<and> (E,y) \<in> Rep_kraus_family (kf_plus (\<DD> f) (\<EE> f))\<close>
    by (auto intro!: image_eqI simp add: tuple kf_comp_dependent_raw.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> EF = E o\<^sub>C\<^sub>L F \<and> EF \<noteq> 0 \<and> (F,f) \<in> Rep_kraus_family \<FF> \<and> 
                      (case y of Inl d \<Rightarrow> (E,d) \<in> Rep_kraus_family (\<DD> f)
                               | Inr e \<Rightarrow> (E,e) \<in> Rep_kraus_family (\<EE> f))\<close>
    apply (cases y)
    by (auto simp: kf_plus.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> (case y of Inl d \<Rightarrow> (EF, F, E, f, d) \<in> Rep_kraus_family (kf_comp_dependent_raw \<DD> \<FF>)
                             | Inr e \<Rightarrow> (EF, F, E, f, e) \<in> Rep_kraus_family (kf_comp_dependent_raw \<EE> \<FF>))\<close>
    apply (cases y)
    by (force intro!: simp: kf_comp_dependent_raw.rep_eq assms)+
  also have \<open>\<dots> \<longleftrightarrow> (case y of Inl d \<Rightarrow> (EF, Inl (F, E, f, d)) \<in> Rep_kraus_family (kf_plus (kf_comp_dependent_raw \<DD> \<FF>) (kf_comp_dependent_raw \<EE> \<FF>))
                             | Inr e \<Rightarrow> (EF, Inr (F, E, f, e)) \<in> Rep_kraus_family (kf_plus (kf_comp_dependent_raw \<DD> \<FF>) (kf_comp_dependent_raw \<EE> \<FF>)))\<close>
    apply (cases y)
    by (auto intro!: simp: kf_plus.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow>
       (tuple \<in> Rep_kraus_family (kf_map_inj
              (\<lambda>x. case x of Inl (F, D, f, d) \<Rightarrow> (F, D, f, Inl d) | Inr (F, E, f, e) \<Rightarrow> (F, E, f, Inr e))
              (kf_plus (kf_comp_dependent_raw \<DD> \<FF>) (kf_comp_dependent_raw \<EE> \<FF>))))\<close>
    apply (cases y)
    by (force simp: tuple kf_map_inj.rep_eq split!: sum.split_asm prod.split)+
  finally 
  show \<open>(tuple \<in> Rep_kraus_family (kf_comp_dependent_raw (\<lambda>x. kf_plus (\<DD> x) (\<EE> x)) \<FF>)) \<longleftrightarrow>
       (tuple \<in> Rep_kraus_family (kf_map_inj
              (\<lambda>x. case x of Inl (F, D, f, d) \<Rightarrow> (F, D, f, Inl d) | Inr (F, E, f, e) \<Rightarrow> (F, E, f, Inr e))
              (kf_plus (kf_comp_dependent_raw \<DD> \<FF>) (kf_comp_dependent_raw \<EE> \<FF>))))\<close>
    by -
qed


lemma kf_comp_dependent_kf_plus_left:
  assumes \<open>bdd_above ((\<lambda>x. kf_norm (\<DD> x)) ` kf_domain \<FF>)\<close>
  assumes \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> x)) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent (\<lambda>x. kf_plus (\<DD> x) (\<EE> x)) \<FF> =
    kf_map_inj (\<lambda>x. case x of Inl (f,d) \<Rightarrow> (f, Inl d) | Inr (f,e) \<Rightarrow> (f, Inr e)) (kf_plus (kf_comp_dependent \<DD> \<FF>) (kf_comp_dependent \<EE> \<FF>))\<close>
  apply (simp add: kf_comp_dependent_def kf_comp_dependent_raw_kf_plus_left[OF assms] kf_plus_map_both)
  apply (subst kf_map_kf_map_inj_comp)
   apply (auto simp add: inj_on_def split!: sum.split_asm)[1]
  apply (subst kf_map_inj_kf_map_comp)
   apply (auto simp add: inj_on_def split!: sum.split_asm)[1]
  apply (rule arg_cong2[where f=kf_map])
  by (auto intro!: ext simp add: o_def split!: sum.split)

lemma kf_map_inj_twice:
  shows \<open>kf_map_inj f (kf_map_inj g \<EE>) = kf_map_inj (f o g) \<EE>\<close>
  apply (transfer' fixing: f g)
  by (simp add: image_image case_prod_unfold)


lemma kf_comp_dependent_kf_plus_left':
  assumes \<open>bdd_above ((\<lambda>x. kf_norm (\<DD> x)) ` kf_domain \<FF>)\<close>
  assumes \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> x)) ` kf_domain \<FF>)\<close>
  shows \<open>kf_plus (kf_comp_dependent \<DD> \<FF>) (kf_comp_dependent \<EE> \<FF>) = 
    kf_map_inj (\<lambda>(f,de). case de of Inl d \<Rightarrow> Inl (f,d) | Inr e \<Rightarrow> Inr (f,e)) (kf_comp_dependent (\<lambda>x. kf_plus (\<DD> x) (\<EE> x)) \<FF>)\<close>
  apply (subst kf_comp_dependent_kf_plus_left[OF assms])
  apply (subst kf_map_inj_twice)
  apply (rewrite at \<open>kf_map_inj \<hole> _\<close> to id DEADID.rel_mono_strong)
  by (auto intro!: ext simp: split!: sum.split)


lemma kf_comp_dependent_plus_left:
  assumes \<open>bdd_above ((\<lambda>x. kf_norm (\<DD> x)) ` kf_domain \<FF>)\<close>
  assumes \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> x)) ` kf_domain \<FF>)\<close>
  shows \<open>kf_comp_dependent (\<lambda>x. \<DD> x + \<EE> x) \<FF> \<equiv>\<^sub>k\<^sub>r kf_comp_dependent \<DD> \<FF> + kf_comp_dependent \<EE> \<FF>\<close>
proof -
  have \<open>kf_comp_dependent (\<lambda>x. \<DD> x + \<EE> x) \<FF> \<equiv>\<^sub>k\<^sub>r 
      kf_map (\<lambda>(x, y). (x, case y of Inl x \<Rightarrow> x | Inr y \<Rightarrow> y)) (kf_comp_dependent (\<lambda>x. kf_plus (\<DD> x) (\<EE> x)) \<FF>)\<close>
    unfolding plus_kraus_family_def
    by (rule kf_comp_dependent_map_left)
  also have \<open>\<dots> = kf_map (\<lambda>(x, y). (x, case y of Inl x \<Rightarrow> x | Inr y \<Rightarrow> y))
     (kf_map_inj (case_sum (\<lambda>(f, d). (f, Inl d)) (\<lambda>(f, e). (f, Inr e)))
       (kf_plus (kf_comp_dependent \<DD> \<FF>) (kf_comp_dependent \<EE> \<FF>)))\<close>
    by (simp add: kf_comp_dependent_kf_plus_left[OF assms])
  also have \<open>\<dots> = kf_map (\<lambda>y. case y of Inl x \<Rightarrow> x | Inr y \<Rightarrow> y)
     (kf_plus (kf_comp_dependent \<DD> \<FF>) (kf_comp_dependent \<EE> \<FF>))\<close>
    apply (subst kf_map_kf_map_inj_comp)
     apply (auto intro!: inj_onI split!: sum.split_asm)[1]
    apply (rule arg_cong2[where f=kf_map, OF _ refl])
    by (auto intro!: ext simp add: o_def split!: sum.split)
  also have \<open>\<dots> = kf_comp_dependent \<DD> \<FF> + kf_comp_dependent \<EE> \<FF>\<close>
    by (simp add: plus_kraus_family_def)
  finally show ?thesis
    by -
qed

subsection \<open>Infinite sums\<close>

lift_definition kf_infsum :: \<open>('a \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'x) kraus_family) \<Rightarrow> 'a set \<Rightarrow> ('b,'c,'a\<times>'x) kraus_family\<close> is
  \<open>\<lambda>\<EE> A. if summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A
         then (\<lambda>(a,(E,x)). (E,(a,x))) ` Sigma A (\<lambda>a. Rep_kraus_family (\<EE> a)) else {}\<close>
proof (rule CollectI, rename_tac \<EE> A)
  fix \<EE> :: \<open>'a \<Rightarrow> ('b, 'c, 'x) kraus_family\<close> and A
  define \<EE>' where \<open>\<EE>' a = Rep_kraus_family (\<EE> a)\<close> for a
  show \<open>kraus_family (if summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A 
                      then (\<lambda>(a,(E,x)). (E,(a,x))) ` Sigma A \<EE>'
                      else {})\<close>
  proof (cases \<open>summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>)
    case True
    have \<open>kraus_family ((\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>')\<close>
    proof (intro kraus_familyI bdd_aboveI)
      fix C assume \<open>C \<in> (\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> (\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>'}\<close>
      then obtain F where \<open>finite F\<close> and F_subset: \<open>F \<subseteq> (\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>'\<close>
        and C_def: \<open>C = (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close>
        by blast
      define B F' where \<open>B = infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>
        and \<open>F' = (\<lambda>(E,a,x). (a,E,x)) ` F\<close>

      have [iff]: \<open>finite F'\<close>
        using \<open>finite F\<close> by (auto intro!: simp: F'_def)
      have F'_subset: \<open>F' \<subseteq> Sigma A \<EE>'\<close>
        using F_subset by (auto simp: F'_def)
      have Sigma_decomp: \<open>(SIGMA a:(\<lambda>x. fst x) ` F'. snd ` Set.filter (\<lambda>(a',Ex). a'=a) F') = F'\<close>
        by force

      have \<open>C = (\<Sum>(a, (E, x))\<in>F'. E* o\<^sub>C\<^sub>L E)\<close>
        unfolding F'_def
        apply (subst sum.reindex)
        by (auto intro!: inj_onI simp: C_def case_prod_unfold)
      also have \<open>\<dots> = (\<Sum>a\<in>fst ` F'. \<Sum>(E, x)\<in>snd ` Set.filter (\<lambda>(a',Ex). a'=a) F'. E* o\<^sub>C\<^sub>L E)\<close>
        apply (subst sum.Sigma)
        by (auto intro!: finite_imageI simp: Sigma_decomp)
      also have \<open>\<dots> = (\<Sum>a\<in>fst ` F'. infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (snd ` Set.filter (\<lambda>(a',Ex). a'=a) F'))\<close>
        apply (rule sum.cong[OF refl])
        apply (rule infsum_in_finite[symmetric])
        by auto
      also have \<open>\<dots> \<le> (\<Sum>a\<in>fst ` F'. infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (\<EE>' a))\<close>
      proof (rule sum_mono, rule infsum_mono_neutral_wot)
        fix a assume \<open>a \<in> fst ` F'\<close>
        show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (snd ` Set.filter (\<lambda>(a', Ex). a' = a) F')\<close>
          by (auto intro!: summable_on_in_finite)
        show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (\<EE>' a)\<close>
          using \<EE>'_def[abs_def] kf_bound_has_sum summable_on_in_def by blast
        show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close> for Ex
          by blast
        have \<open>snd ` Set.filter (\<lambda>(a', Ex). a' = a) F' \<le> \<EE>' a\<close>
          using F'_subset by auto
        then show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> 0\<close>
          if \<open>Ex \<in> snd ` Set.filter (\<lambda>(a', Ex). a' = a) F' - \<EE>' a\<close> for Ex
          using that by blast
        show \<open>0 \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close> for Ex
          by (auto intro!: positive_cblinfun_squareI simp: case_prod_unfold)
      qed
      also have \<open>\<dots> = (\<Sum>a\<in>fst ` F'. kf_bound (\<EE> a))\<close>
        unfolding \<EE>'_def
        apply (transfer' fixing: F')
        by simp
      also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) (fst ` F')\<close>
        apply (rule infsum_in_finite[symmetric])
        by auto
      also have \<open>\<dots> \<le> infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>
      proof (rule infsum_mono_neutral_wot)
        show \<open>summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) (fst ` F')\<close>
          by (auto intro!: summable_on_in_finite)
        show \<open>summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>
          using True by blast
        show \<open>kf_bound (\<EE> a) \<le> kf_bound (\<EE> a)\<close> for a
          by blast
        show \<open>kf_bound (\<EE> a) \<le> 0\<close> if \<open>a \<in> fst ` F' - A\<close> for a
          using F'_subset that by auto
        show \<open>0 \<le> kf_bound (\<EE> a)\<close> for a
          by simp
      qed
      also have \<open>\<dots> = B\<close>
        using B_def by blast
      finally show \<open>C \<le> B\<close>
        by -
    next
      show \<open>0 \<notin> fst ` (\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>'\<close>
        using Rep_kraus_family by (force simp: \<EE>'_def kraus_family_def)
    qed
    with True show ?thesis 
      by simp
  next
    case False
    then show ?thesis
      by (auto intro!: bdd_aboveI simp add: kraus_family_def)
  qed
qed

definition kf_summable :: \<open>('a \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'x) kraus_family) \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>kf_summable \<EE> A \<longleftrightarrow> summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>

lemma kf_summable_from_abs_summable:
  assumes sum: \<open>(\<lambda>a. kf_norm (\<EE> a)) summable_on A\<close>
  shows \<open>kf_summable \<EE> A\<close>
  using assms
  by (simp add: summable_imp_wot_summable abs_summable_summable kf_summable_def kf_norm_def)

lemma kf_infsum_apply:
  assumes \<open>kf_summable \<EE> A\<close>
  shows \<open>kf_infsum \<EE> A *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a *\<^sub>k\<^sub>r \<rho>)\<close>
proof -
  from kf_apply_summable[of \<rho> \<open>kf_infsum \<EE> A\<close>]
  have summable: \<open>(\<lambda>(a, E, x). sandwich_tc E \<rho>) summable_on (SIGMA a:A. Rep_kraus_family (\<EE> a))\<close>
    using assms
    by (simp add: kf_summable_def kf_infsum.rep_eq case_prod_unfold summable_on_reindex inj_on_def prod.expand o_def)
  have \<open>kf_infsum \<EE> A *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>(E,ax)\<in>(\<lambda>(a, E, x) \<Rightarrow> (E, a, x)) ` (SIGMA a:A. Rep_kraus_family (\<EE> a)). sandwich_tc E \<rho>)\<close>
    using assms unfolding kf_summable_def
    apply (transfer' fixing: \<EE>)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(a, E, x) \<in> (SIGMA a:A. Rep_kraus_family (\<EE> a)). sandwich_tc E \<rho>)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<Sum>\<^sub>\<infinity>(E, b)\<in>Rep_kraus_family (\<EE> a). sandwich_tc E \<rho>)\<close>
    apply (subst infsum_Sigma'_banach[symmetric])
    using summable by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a *\<^sub>k\<^sub>r \<rho>)\<close>
    by (metis (no_types, lifting) infsum_cong kf_apply.rep_eq split_def)
  finally show ?thesis
    by -
qed

lemma kf_infsum_apply_summable:
  assumes \<open>kf_summable \<EE> A\<close>
  shows \<open>(\<lambda>a. \<EE> a *\<^sub>k\<^sub>r \<rho>) summable_on A\<close>
proof -
  from kf_apply_summable[of \<rho> \<open>kf_infsum \<EE> A\<close>]
  have summable: \<open>(\<lambda>(a, E, x). sandwich_tc E \<rho>) summable_on (SIGMA a:A. Rep_kraus_family (\<EE> a))\<close>
    using assms
    by (simp add: kf_summable_def kf_infsum.rep_eq case_prod_unfold summable_on_reindex inj_on_def prod.expand o_def)
  from summable_on_Sigma_banach[OF this]
  have \<open>(\<lambda>a. \<Sum>\<^sub>\<infinity>(E, x)\<in>Rep_kraus_family (\<EE> a). sandwich_tc E \<rho>) summable_on A\<close>
    by simp
  then show ?thesis
    by (metis (mono_tags, lifting) infsum_cong kf_apply.rep_eq split_def summable_on_cong)
qed

lemma kf_bound_infsum:
  fixes f :: \<open>'a \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'x) kraus_family\<close>
  assumes \<open>kf_summable f A\<close>
  shows \<open>kf_bound (kf_infsum f A) = infsum_in cweak_operator_topology (\<lambda>a. kf_bound (f a)) A\<close>
proof -
  have pos: \<open>0 \<le> compose_wot (adj_wot a) a\<close> for a :: \<open>('b,'c) cblinfun_wot\<close>
    apply transfer'
    using positive_cblinfun_squareI by blast
  have sum3: \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>(E,_)\<in>Rep_kraus_family (f x). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on A\<close>
  proof -
    define b where \<open>b x = kf_bound (f x)\<close> for x
    have \<open>(\<lambda>x. Abs_cblinfun_wot (b x)) summable_on A\<close>
      using assms unfolding kf_summable_def
      apply (subst (asm) b_def[symmetric])
      apply (transfer' fixing: b A)
      by simp
    then show ?thesis
      by (simp add: Rep_cblinfun_wot_inverse kf_bound_def' b_def)
  qed
  have sum2: \<open>(\<lambda>(E, _). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on
         Rep_kraus_family (f x)\<close> if \<open>x \<in> A\<close> for x
    by (rule kf_bound_summable')
  have sum1: \<open>(\<lambda>(_, E, _). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on
    (SIGMA a:A. Rep_kraus_family (f a))\<close>
    apply (rule summable_on_Sigma_wotI)
    using sum3 sum2
    by (auto intro!: pos simp: case_prod_unfold)

  have \<open>Abs_cblinfun_wot (kf_bound (kf_infsum f A)) =
        (\<Sum>\<^sub>\<infinity>(E, x)\<in>Rep_kraus_family (kf_infsum f A).
               compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    by (simp add: kf_bound_def' Rep_cblinfun_wot_inverse)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E, x)\<in>(\<lambda>(a, E, xa). (E, a, xa)) ` (SIGMA a:A. Rep_kraus_family (f a)).
       compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    using assms by (simp add: kf_infsum.rep_eq kf_summable_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(a, E, x)\<in>(SIGMA a:A. Rep_kraus_family (f a)). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<Sum>\<^sub>\<infinity>(E, x)\<in>Rep_kraus_family (f a). compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    apply (subst infsum_Sigma_topological_monoid)
    using sum1 sum2 by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. Abs_cblinfun_wot (kf_bound (f a)))\<close>
    by (simp add: kf_bound_def' Rep_cblinfun_wot_inverse)
  also have \<open>\<dots> = Abs_cblinfun_wot (infsum_in cweak_operator_topology (\<lambda>a. kf_bound (f a)) A)\<close>
    apply (simp only: infsum_euclidean_eq[symmetric])
    apply (transfer' fixing: f A)
    by simp
  finally show ?thesis
    apply (rule Abs_cblinfun_wot_inject[THEN iffD1, rotated -1])
    by simp_all
qed

lemma kf_norm_infsum:
  assumes sum: \<open>(\<lambda>a. kf_norm (\<EE> a)) summable_on A\<close>
  shows \<open>kf_norm (kf_infsum \<EE> A) \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. kf_norm (\<EE> a))\<close>
proof -
  have \<open>kf_norm (kf_infsum \<EE> A) = norm (infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A)\<close>
    unfolding kf_norm_def
    apply (subst kf_bound_infsum)
    by (simp_all add: kf_summable_from_abs_summable assms)
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. norm (kf_bound (\<EE> a)))\<close>
    apply (rule triangle_ineq_wot)
    using sum by (simp add: kf_norm_def)
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. kf_norm (\<EE> a))\<close>
    by (smt (verit, del_insts) infsum_cong kf_norm_def)
  finally show ?thesis
    by -
qed

lemma kf_filter_infsum:
  assumes \<open>kf_summable \<EE> A\<close>
  shows \<open>kf_filter P (kf_infsum \<EE> A) 
           = kf_infsum (\<lambda>a. kf_filter (\<lambda>x. P (a,x)) (\<EE> a)) {a\<in>A. \<exists>x. P (a,x)}\<close>
    (is \<open>?lhs = ?rhs\<close>)
proof -
  have summ: \<open>summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (kf_filter (\<lambda>x. P (a, x)) (\<EE> a)))
      {a \<in> A. \<exists>x. P (a, x)}\<close>
  proof (rule summable_wot_boundedI)
    fix F assume \<open>finite F\<close> and F_subset: \<open>F \<subseteq> {a \<in> A. \<exists>x. P (a, x)}\<close>
    have \<open>(\<Sum>a\<in>F. kf_bound (kf_filter (\<lambda>x. P (a, x)) (\<EE> a)))
        \<le> (\<Sum>a\<in>F. kf_bound (\<EE> a))\<close>
      by (meson kf_bound_filter sum_mono)
    also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) F\<close>
      apply (rule infsum_in_finite[symmetric])
      by (auto intro!: \<open>finite F\<close>)
    also have \<open>\<dots> \<le> infsum_in cweak_operator_topology (\<lambda>a. kf_bound (\<EE> a)) A\<close>
      apply (rule infsum_mono_neutral_wot)
      using F_subset assms
      by (auto intro!: \<open>finite F\<close> intro: summable_on_in_finite simp: kf_summable_def)
    finally show \<open>(\<Sum>a\<in>F. kf_bound (kf_filter (\<lambda>x. P (a, x)) (\<EE> a))) \<le> \<dots>\<close>
      by -
  next
    show \<open>0 \<le> kf_bound (kf_filter (\<lambda>y. P (x, y)) (\<EE> x))\<close> for x
      by simp
  qed
  have \<open>Rep_kraus_family ?lhs = Rep_kraus_family ?rhs\<close>
    using assms by (force simp add: kf_filter.rep_eq kf_infsum.rep_eq assms summ kf_summable_def)
  then show \<open>?lhs = ?rhs\<close>
    by (simp add: Rep_kraus_family_inject)
qed

lemma kf_infsum_empty[simp]: \<open>kf_infsum \<EE> {} = 0\<close>
  apply transfer' by simp

lemma kf_infsum_singleton[simp]: \<open>kf_infsum \<EE> {a} = kf_map_inj (\<lambda>x. (a,x)) (\<EE> a)\<close>
  apply (rule Rep_kraus_family_inject[THEN iffD1])
  by (force simp add: kf_infsum.rep_eq summable_on_in_finite kf_map_inj.rep_eq)

lemma kf_infsum_invalid: 
  assumes \<open>\<not> kf_summable \<EE> A\<close>
  shows \<open>kf_infsum \<EE> A = 0\<close>
  using assms
  apply transfer'
  unfolding kf_summable_def
  by simp


lemma kf_infsum_cong:
  fixes \<EE> \<FF> :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'c::chilbert_space, 'x) kraus_family\<close>
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> \<EE> a \<equiv>\<^sub>k\<^sub>r \<FF> a\<close>
  shows \<open>kf_infsum \<EE> A \<equiv>\<^sub>k\<^sub>r kf_infsum \<FF> A\<close>
proof (cases \<open>kf_summable \<EE> A\<close>)
  case True
  then have True': \<open>kf_summable \<FF> A\<close>
    unfolding kf_summable_def
    apply (rule summable_on_in_cong[THEN iffD1, rotated])
    by (simp add: kf_bound_cong assms kf_eq_imp_eq_weak)
  show ?thesis
  proof (rule kf_eqI)
    fix ax :: \<open>'a \<times> 'x\<close> and \<rho>
    obtain a x where ax_def: \<open>ax = (a,x)\<close>
      by fastforce
    have *: \<open>{a'. a' = a \<and> a' \<in> A} = (if a\<in>A then {a} else {})\<close>
      by auto
    have \<open>kf_infsum \<EE> A *\<^sub>k\<^sub>r @{ax} \<rho> = (if a\<in>A then \<EE> a *\<^sub>k\<^sub>r @{x} \<rho> else 0)\<close>
      by (simp add: ax_def kf_apply_on_def True kf_filter_infsum * 
          kf_apply_map_inj inj_on_def)
    also from assms have \<open>\<dots> = (if a\<in>A then \<FF> a *\<^sub>k\<^sub>r @{x} \<rho> else 0)\<close>
      by (auto intro!: kf_apply_on_eqI)
    also have \<open>\<dots> = kf_infsum \<FF> A *\<^sub>k\<^sub>r @{ax} \<rho>\<close>
      by (simp add: ax_def kf_apply_on_def True' kf_filter_infsum * 
          kf_apply_map_inj inj_on_def)
    finally show \<open>kf_infsum \<EE> A *\<^sub>k\<^sub>r @{ax} \<rho> = kf_infsum \<FF> A *\<^sub>k\<^sub>r @{ax} \<rho>\<close>
      by -
  qed
next
  case False
  then have False': \<open>\<not> kf_summable \<FF> A\<close>
    unfolding kf_summable_def
    apply (subst (asm) assms[THEN kf_eq_imp_eq_weak, 
          THEN kf_bound_cong, THEN summable_on_in_cong])
    by auto
  show ?thesis
    by (simp add: kf_infsum_invalid False False')
qed

subsection \<open>Trace-preserving maps\<close>

definition \<open>kf_trace_preserving \<EE> \<longleftrightarrow> (\<forall>\<rho>. trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc \<rho>)\<close>

definition \<open>kf_trace_reducing \<EE> \<longleftrightarrow> (\<forall>\<rho>\<ge>0. trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) \<le> trace_tc \<rho>)\<close>

lemma kf_trace_reducing_iff_norm_leq1: \<open>kf_trace_reducing \<EE> \<longleftrightarrow> kf_norm \<EE> \<le> 1\<close>
proof (unfold kf_trace_reducing_def, intro iffI allI impI)
  assume assm: \<open>kf_norm \<EE> \<le> 1\<close>
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  assume \<open>\<rho> \<ge> 0\<close>
  have \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = norm (\<EE> *\<^sub>k\<^sub>r \<rho>)\<close>
    by (simp add: \<open>0 \<le> \<rho>\<close> kf_apply_pos norm_tc_pos)
  also have \<open>\<dots> \<le> kf_norm \<EE> * norm \<rho>\<close>
    using \<open>0 \<le> \<rho>\<close> complex_of_real_mono kf_apply_bounded_pos by blast
  also have \<open>\<dots> \<le> norm \<rho>\<close>
    by (metis assm complex_of_real_mono kf_norm_geq0 mult_left_le_one_le norm_ge_zero)
  also have \<open>\<dots> = trace_tc \<rho>\<close>
    by (simp add: \<open>0 \<le> \<rho>\<close> norm_tc_pos)
  finally show \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) \<le> trace_tc \<rho>\<close>
    by -
next
  assume assm[rule_format]: \<open>\<forall>\<rho>\<ge>0. trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) \<le> trace_tc \<rho>\<close>
  have \<open>kf_bound \<EE> \<le> id_cblinfun\<close>
  proof (rule cblinfun_leI)
    fix x
    have \<open>x \<bullet>\<^sub>C kf_bound \<EE> x = trace_tc (\<EE> *\<^sub>k\<^sub>r tc_butterfly x x)\<close>
      by (simp add: kf_bound_from_map)
    also have \<open>\<dots> \<le> trace_tc (tc_butterfly x x)\<close>
      apply (rule assm)
      by simp
    also have \<open>\<dots> = x \<bullet>\<^sub>C id_cblinfun x\<close>
      by (simp add: tc_butterfly.rep_eq trace_butterfly trace_tc.rep_eq)
  finally show \<open>x \<bullet>\<^sub>C kf_bound \<EE> x \<le> x \<bullet>\<^sub>C id_cblinfun x\<close>
      by -
  qed
  then show \<open>kf_norm \<EE> \<le> 1\<close>
    by (smt (verit, best) kf_norm_def kf_bound_pos norm_cblinfun_id_le norm_cblinfun_mono)
qed

lemma kf_trace_preserving_iff_bound_id: \<open>kf_trace_preserving \<EE> \<longleftrightarrow> kf_bound \<EE> = id_cblinfun\<close>
proof (unfold kf_trace_preserving_def, intro iffI allI)
  assume asm[rule_format]: \<open>\<forall>\<rho>. trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc \<rho>\<close>
  have \<open>\<psi> \<bullet>\<^sub>C kf_bound \<EE> \<psi> = \<psi> \<bullet>\<^sub>C id_cblinfun \<psi>\<close> for \<psi>
  proof -
    have \<open>\<psi> \<bullet>\<^sub>C kf_bound \<EE> \<psi> = trace_tc (\<EE> *\<^sub>k\<^sub>r tc_butterfly \<psi> \<psi>)\<close>
      by (simp add: kf_bound_from_map)
    also have \<open>\<dots> = trace_tc (tc_butterfly \<psi> \<psi>)\<close>
      by (simp add: asm)
    also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C id_cblinfun \<psi>\<close>
      by (simp add: tc_butterfly.rep_eq trace_butterfly trace_tc.rep_eq)
    finally show ?thesis
      by -
  qed
  then show \<open>kf_bound \<EE> = id_cblinfun\<close>
    using cblinfun_cinner_eq0I[where a=\<open>kf_bound \<EE> - id_cblinfun\<close>]
    by (simp add: cblinfun.real.diff_left cinner_diff_right)
next
  assume asm: \<open>kf_bound \<EE> = id_cblinfun\<close>
  fix \<rho>
  have \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc (compose_tcr (kf_bound \<EE>) \<rho>)\<close>
    by (rule trace_from_kf_bound)
  also have \<open>\<dots> = trace_tc \<rho>\<close>
    using asm by fastforce
  finally show \<open>trace_tc (\<EE> *\<^sub>k\<^sub>r \<rho>) = trace_tc \<rho>\<close>
    by -
qed

lemma kf_trace_norm_preserving: \<open>kf_norm \<EE> \<le> 1\<close> if \<open>kf_trace_preserving \<EE>\<close>
  apply (rule kf_trace_reducing_iff_norm_leq1[THEN iffD1])
  using that
  by (simp add: kf_trace_preserving_def kf_trace_reducing_def)

lemma kf_trace_norm_preserving_eq: 
  fixes \<EE> :: \<open>('a::{chilbert_space,not_singleton}, 'b::chilbert_space, 'c) kraus_family\<close>
  assumes \<open>kf_trace_preserving \<EE>\<close>
  shows \<open>kf_norm \<EE> = 1\<close>
  using assms by (simp add: kf_trace_preserving_iff_bound_id kf_norm_def)

lemma kf_trace_preserving_map[simp]: \<open>kf_trace_preserving (kf_map f \<EE>) \<longleftrightarrow> kf_trace_preserving \<EE>\<close>
  by (simp add: kf_map_bound kf_trace_preserving_iff_bound_id)

lemma kf_trace_reducing_map[simp]: \<open>kf_trace_reducing (kf_map f \<EE>) \<longleftrightarrow> kf_trace_reducing \<EE>\<close>
  by (simp add: kf_trace_reducing_iff_norm_leq1)

lemma kf_trace_preserving_id[iff]: \<open>kf_trace_preserving kf_id\<close>
  by (simp add: kf_trace_preserving_iff_bound_id)

lemma kf_trace_reducing_id[iff]: \<open>kf_trace_reducing kf_id\<close>
  by (simp add: kf_norm_id_leq1 kf_trace_reducing_iff_norm_leq1)

subsection \<open>Sampling\<close>

lift_definition kf_sample :: \<open>('x \<Rightarrow> real) \<Rightarrow> ('a::chilbert_space, 'a, 'x) kraus_family\<close> is
  \<open>\<lambda>p. if (\<forall>x. p x \<ge> 0) \<and> p summable_on UNIV then Set.filter (\<lambda>(E,_). E\<noteq>0) (range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x))) else {}\<close>
proof -
  fix p :: \<open>'x \<Rightarrow> real\<close>
  show \<open>?thesis p\<close>
  proof (cases \<open>(\<forall>x. p x \<ge> 0) \<and> p summable_on UNIV\<close>)
    case True
    then have \<open>p abs_summable_on UNIV\<close>
      by simp
    from abs_summable_iff_bdd_above[THEN iffD1, OF this]
    obtain B where F_B: \<open>finite F \<Longrightarrow> (\<Sum>x\<in>F. p x) \<le> B\<close> for F
      apply atomize_elim
      using True by (auto simp: bdd_above_def)
    have \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B *\<^sub>R id_cblinfun\<close>
      if \<open>finite F\<close> and \<open>F \<subseteq> Set.filter (\<lambda>(E,_). E\<noteq>0) (range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x)))\<close>
      for F :: \<open>('a\<Rightarrow>\<^sub>C\<^sub>L'a \<times> 'x) set\<close>
    proof -
      from that
      obtain F' where \<open>finite F'\<close> and F_def: \<open>F = (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x)) ` F'\<close>
        using finite_subset_filter_image
        by meson
      then have \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>F'. (sqrt (p x) *\<^sub>R id_cblinfun)* o\<^sub>C\<^sub>L (sqrt (p x) *\<^sub>R id_cblinfun))\<close>
        by (simp add: sum.reindex inj_on_def)
      also have \<open>\<dots> = (\<Sum>x\<in>F'. p x *\<^sub>R id_cblinfun)\<close>
        using True by simp
      also have \<open>\<dots> = (\<Sum>x\<in>F'. p x) *\<^sub>R id_cblinfun\<close>
        by (metis scaleR_left.sum)
      also have \<open>\<dots> \<le> B *\<^sub>R id_cblinfun\<close>
        using \<open>\<And>F. finite F \<Longrightarrow> (\<Sum>x\<in>F. p x) \<le> B\<close> \<open>finite F'\<close> positive_id_cblinfun scaleR_right_mono by blast
      finally show ?thesis
        by -
    qed
    then have \<open>kraus_family (Set.filter (\<lambda>(E,_). E\<noteq>0) (range (\<lambda>x. (sqrt (p x) *\<^sub>R (id_cblinfun ::'a\<Rightarrow>\<^sub>C\<^sub>L_), x))))\<close>
      by (force intro!: bdd_aboveI[where M=\<open>B *\<^sub>R id_cblinfun\<close>] simp: kraus_family_def case_prod_unfold)
    then show ?thesis
      using True by simp
  next
    case False
    then show ?thesis
      by auto
  qed
qed

lemma kf_sample_norm:
  fixes p :: \<open>'x \<Rightarrow> real\<close>
  assumes \<open>\<And>x. p x \<ge> 0\<close>
  assumes \<open>p summable_on UNIV\<close>
  shows \<open>kf_norm (kf_sample p :: ('a::{chilbert_space,not_singleton},'a,'x) kraus_family)
             = (\<Sum>\<^sub>\<infinity>x. p x)\<close>
proof -
  define B :: \<open>'a\<Rightarrow>\<^sub>C\<^sub>L'a\<close> where \<open>B = kf_bound (kf_sample p)\<close>
  obtain \<psi> :: 'a where \<open>norm \<psi> = 1\<close>
    using ex_norm1_not_singleton by blast

  have \<open>\<psi> \<bullet>\<^sub>C (B *\<^sub>V \<psi>) = \<psi> \<bullet>\<^sub>C ((\<Sum>\<^sub>\<infinity>x. p x) *\<^sub>R id_cblinfun *\<^sub>V \<psi>)\<close> 
    if \<open>norm \<psi> = 1\<close> for \<psi>
  proof -
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (kf_sample p)) B\<close>
      using B_def kf_bound_has_sum by blast
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Set.filter (\<lambda>(E,_). E\<noteq>0) (range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x)))) B\<close>
      by (simp add: kf_sample.rep_eq assms)
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x))) B\<close>
      apply (rule has_sum_in_cong_neutral[THEN iffD1, rotated -1])
      by auto
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>x. norm (p x) *\<^sub>R id_cblinfun) UNIV B\<close>
      by (simp add: has_sum_in_reindex inj_on_def o_def)
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>x. p x *\<^sub>R id_cblinfun) UNIV B\<close>
      apply (rule has_sum_in_cong[THEN iffD1, rotated])
      by (simp add: assms(1))
    then have \<open>has_sum_in euclidean (\<lambda>x. \<psi> \<bullet>\<^sub>C (p x *\<^sub>R id_cblinfun) \<psi>) UNIV (\<psi> \<bullet>\<^sub>C B \<psi>)\<close>
      apply (rule has_sum_in_comm_additive[rotated 3, OF cweak_operator_topology_cinner_continuous, unfolded o_def])
      by (simp_all add: Modules.additive_def cblinfun.add_left cinner_simps)
    then have \<open>((\<lambda>x. of_real (p x)) has_sum (\<psi> \<bullet>\<^sub>C B \<psi>)) UNIV\<close>
      apply (simp add: scaleR_scaleC has_sum_euclidean_iff)
      using \<open>norm \<psi> = 1\<close> cnorm_eq_1 by force
    then have \<open>\<psi> \<bullet>\<^sub>C B \<psi> = (\<Sum>\<^sub>\<infinity>x. of_real (p x))\<close>
      by (simp add: infsumI)
    also have \<open>\<dots> = of_real (\<Sum>\<^sub>\<infinity>x. p x)\<close>
      by (metis infsum_of_real)
    also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C ((\<Sum>\<^sub>\<infinity>x. p x) *\<^sub>R id_cblinfun) \<psi>\<close>
      using \<open>norm \<psi> = 1\<close> by (simp add: scaleR_scaleC cnorm_eq_1)
    finally show ?thesis
      by -
  qed
  then have \<open>B = (\<Sum>\<^sub>\<infinity>x. p x) *\<^sub>R id_cblinfun\<close>
    by (rule cblinfun_cinner_eqI)
  then have \<open>norm B = norm (\<Sum>\<^sub>\<infinity>x. p x)\<close>
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. p x)\<close>
    by (simp add: abs_of_nonneg assms infsum_nonneg)
  finally show ?thesis
    by (simp add: kf_norm_def B_def)
qed

subsection \<open>Trace\<close>

lift_definition kf_trace :: \<open>'a set \<Rightarrow> ('a::chilbert_space, 'b::one_dim, 'a) kraus_family\<close> is
  \<open>\<lambda>B. if is_onb B then (\<lambda>x. (vector_to_cblinfun x*, x)) ` B else {}\<close>
proof (rename_tac B)
  fix B :: \<open>'a set\<close>
  define family :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'a) set\<close> where \<open>family = (\<lambda>x. (vector_to_cblinfun x*, x)) ` B\<close>
  have \<open>kraus_family family\<close> if \<open>is_onb B\<close>
  proof -
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> id_cblinfun\<close> if \<open>finite F\<close> and FB: \<open>F \<subseteq> family\<close> for F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'a) set\<close>
    proof -
      obtain G where \<open>finite G\<close> and \<open>G \<subseteq> B\<close> and FG: \<open>F = (\<lambda>x. (vector_to_cblinfun x*, x)) ` G\<close>
        apply atomize_elim
        using \<open>finite F\<close> and FB
        apply (simp add: family_def)
        by (meson finite_subset_image)
      from \<open>G \<subseteq> B\<close> have [simp]: \<open>is_ortho_set G\<close>
        by (meson \<open>is_onb B\<close> is_onb_def is_ortho_set_antimono)
      from \<open>G \<subseteq> B\<close> have [simp]: \<open>e \<in> G \<Longrightarrow> norm e = 1\<close> for e
        by (meson Set.basic_monos(7) \<open>is_onb B\<close> is_onb_def)
      have [simp]: \<open>inj_on (\<lambda>x. (vector_to_cblinfun x*, x)) G\<close>
        by (meson inj_onI prod.inject)
      have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>G. selfbutter x)\<close>
        by (simp add: FG sum.reindex flip: butterfly_def_one_dim)
      also have \<open>(\<Sum>x\<in>G. selfbutter x) \<le> id_cblinfun\<close>
        apply (rule sum_butterfly_leq_id)
        by auto
      finally show ?thesis
        by -
    qed
    moreover have \<open>0 \<notin> fst ` family\<close>
      apply (simp add: family_def image_image)
      using \<open>is_onb B\<close> apply (simp add: is_onb_def)
      by (smt (verit) adj_0 double_adj imageE norm_vector_to_cblinfun norm_zero)
    ultimately show ?thesis
      by (auto intro!: bdd_aboveI[where M=id_cblinfun] kraus_familyI)
  qed
  then
  show \<open>(if is_onb B then family else {}) \<in> Collect kraus_family\<close>
    by auto
qed

lemma kf_trace_is_trace: 
  assumes \<open>is_onb B\<close>
  shows \<open>kf_trace B *\<^sub>k\<^sub>r \<rho> = one_dim_iso (trace_tc \<rho>)\<close>
proof -
  define \<rho>' where \<open>\<rho>' = from_trace_class \<rho>\<close>
  have \<open>kf_apply (kf_trace B) \<rho> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (vector_to_cblinfun x*) \<rho>)\<close>
    apply (simp add: kf_apply.rep_eq kf_trace.rep_eq assms)
    apply (subst infsum_reindex)
     apply (meson inj_onI prod.simps(1))
    by (simp add: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. one_dim_iso (x \<bullet>\<^sub>C (\<rho>' x)))\<close>
    apply (intro infsum_cong from_trace_class_inject[THEN iffD1])
    apply (subst from_trace_class_sandwich_tc)
    by (simp add: sandwich_apply flip: \<rho>'_def)
  also have \<open>\<dots> = one_dim_iso (\<Sum>\<^sub>\<infinity>x\<in>B. (x \<bullet>\<^sub>C (\<rho>' x)))\<close>
    by (metis (mono_tags, lifting) \<rho>'_def infsum_cblinfun_apply infsum_cong assms one_cblinfun.rep_eq trace_class_from_trace_class trace_exists)
  also have \<open>\<dots> = one_dim_iso (trace \<rho>')\<close>
    by (metis \<rho>'_def trace_class_from_trace_class trace_alt_def[OF assms])
  also have \<open>\<dots> = one_dim_iso (trace_tc \<rho>)\<close>
    by (simp add: \<rho>'_def trace_tc.rep_eq)
  finally show ?thesis
    by -
qed

lemma kf_eq_weak_kf_trace:
  assumes \<open>is_onb A\<close> and \<open>is_onb B\<close>
  shows \<open>kf_trace A =\<^sub>k\<^sub>r kf_trace B\<close>
  by (auto simp: kf_eq_weak_def kf_trace_is_trace assms)

lemma trace_is_kf_trace:
  assumes \<open>is_onb B\<close>
  shows \<open>trace_tc t = one_dim_iso (kf_trace B *\<^sub>k\<^sub>r t)\<close>
  by (simp add: kf_trace_is_trace assms)

lemma kf_trace_bound[simp]:
  assumes \<open>is_onb B\<close>
  shows \<open>kf_bound (kf_trace B) = id_cblinfun\<close>
  using assms
  by (auto intro!: cblinfun_cinner_eqI simp: kf_bound_from_map kf_trace_is_trace trace_tc_butterfly)

lemma kf_trace_norm_eq1[simp]:
  fixes B :: \<open>'a::{chilbert_space, not_singleton} set\<close>
  assumes \<open>is_onb B\<close>
  shows \<open>kf_norm (kf_trace B) = 1\<close>
  using assms by (simp add: kf_trace_bound kf_norm_def)

lemma kf_trace_norm_leq1[simp]:
  fixes B :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb B\<close>
  shows \<open>kf_norm (kf_trace B) \<le> 1\<close>
  by (simp add: assms kf_norm_def norm_cblinfun_id_le)

subsection \<open>Constant maps\<close>


lift_definition kf_constant_onedim :: \<open>('b,'b) trace_class \<Rightarrow> ('a::one_dim, 'b::chilbert_space, unit) kraus_family\<close> is
  \<open>\<lambda>t::('b,'b) trace_class. if t \<ge> 0 then
    Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>v. (vector_to_cblinfun v,())) ` spectral_dec_vecs_tc t)
  else {}\<close>
proof (rule CollectI, rename_tac t)
  fix t :: \<open>('b,'b) trace_class\<close>
  show \<open>kraus_family (if t \<ge> 0 then Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>v. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b,())) ` spectral_dec_vecs_tc t) else {})\<close>
  proof (cases \<open>t \<ge> 0\<close>)
    case True
    have \<open>kraus_family (Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>v. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b,())) ` spectral_dec_vecs_tc t))\<close>
    proof (intro kraus_familyI bdd_aboveI, rename_tac E)
      fix E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
      assume \<open>E \<in> (\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc t)}\<close>
      then obtain F where E_def: \<open>E = (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close> and \<open>finite F\<close> and \<open>F \<subseteq> Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc t)\<close>
        by blast
      then obtain F' where F_def: \<open>F = (\<lambda>v. (vector_to_cblinfun v, ())) ` F'\<close> and \<open>finite F'\<close> and F'_subset: \<open>F' \<subseteq> spectral_dec_vecs_tc t\<close>
        by (meson finite_subset_filter_image)
      have inj: \<open>inj_on (\<lambda>v. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b, ())) F'\<close>
      proof (rule inj_onI, rule ccontr)
        fix x y
        assume \<open>x \<in> F'\<close> and \<open>y \<in> F'\<close>
        assume eq: \<open>(vector_to_cblinfun x :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b, ()) = (vector_to_cblinfun y, ())\<close>
        assume \<open>x \<noteq> y\<close>
        have ortho: \<open>is_ortho_set (spectral_dec_vecs (from_trace_class t))\<close>
          using True
          by (auto intro!: spectral_dec_vecs_ortho trace_class_compact pos_selfadjoint
              simp: selfadjoint_tc.rep_eq from_trace_class_pos)
        with \<open>x \<noteq> y\<close> F'_subset \<open>x \<in> F'\<close> \<open>y \<in> F'\<close>
        have \<open>x \<bullet>\<^sub>C y = 0\<close>
          by (auto simp: spectral_dec_vecs_tc.rep_eq is_ortho_set_def)
        then have \<open>(vector_to_cblinfun x :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b)* o\<^sub>C\<^sub>L (vector_to_cblinfun y :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b) = 0\<close>
          by simp
        with eq have \<open>(vector_to_cblinfun x :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b)= 0\<close>
          by force
        then have \<open>norm x = 0\<close>
          by (smt (verit, del_insts) norm_vector_to_cblinfun norm_zero)
        with ortho F'_subset \<open>x \<in> F'\<close> show False
          by (auto simp: spectral_dec_vecs_tc.rep_eq is_ortho_set_def)
      qed
      have \<open>E = (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close>
        by (simp add: E_def)
      also have \<open>\<dots> = (\<Sum>v\<in>F'. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b)* o\<^sub>C\<^sub>L vector_to_cblinfun v)\<close>
        unfolding F_def
        apply (subst sum.reindex)
        by (auto intro!: inj)
      also have \<open>\<dots> = (\<Sum>v\<in>F'. ((norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1)\<close>
        by (auto intro!: sum.cong simp: power2_norm_eq_cinner scaleR_scaleC)
      also have \<open>\<dots> = (\<Sum>v\<in>F'. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        by (metis scaleR_left.sum)
      also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>v\<in>F'. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        using \<open>finite F'\<close> by force
      also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>v\<in>spectral_dec_vecs_tc t. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        apply (intro scaleR_right_mono infsum_mono_neutral)
        using F'_subset
        by (auto intro!: one_dim_cblinfun_one_pos spectral_dec_vec_tc_norm_summable True
            simp: \<open>finite F'\<close> )
      finally show \<open>E \<le> (\<Sum>\<^sub>\<infinity>v\<in>spectral_dec_vecs_tc t. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        by -
    next
      show \<open>0 \<notin> fst ` Set.filter (\<lambda>(E, _). E \<noteq> 0) ((\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc t)\<close>
        by auto
    qed
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
qed

definition kf_constant :: \<open>('b,'b) trace_class \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, unit) kraus_family\<close> where
  \<open>kf_constant \<rho> = kf_flatten (kf_comp (kf_constant_onedim \<rho> :: (complex,_,_) kraus_family) (kf_trace some_chilbert_basis))\<close>

lemma kf_constant_onedim_invalid: \<open>\<not> \<rho> \<ge> 0 \<Longrightarrow> kf_constant_onedim \<rho> = 0\<close>
  apply transfer'
  by simp

lemma kf_constant_invalid: \<open>\<not> \<rho> \<ge> 0 \<Longrightarrow> kf_constant \<rho> = 0\<close>
  by (simp add: kf_constant_def kf_constant_onedim_invalid)

lemma kf_constant_onedim_apply: 
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_apply (kf_constant_onedim \<rho>) \<sigma> = one_dim_iso \<sigma> *\<^sub>C \<rho>\<close>
proof -
  have \<open>kf_apply (kf_constant_onedim \<rho>) \<sigma>
         = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc \<rho>). sandwich_tc E \<sigma>)\<close>
    by (simp add: assms kf_apply.rep_eq kf_constant_onedim.rep_eq case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>(\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc \<rho>. sandwich_tc E \<sigma>)\<close>
    apply (rule infsum_cong_neutral)
    by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>v \<in> spectral_dec_vecs_tc \<rho>. sandwich_tc (vector_to_cblinfun v) \<sigma>)\<close>
    apply (subst infsum_reindex)
    using vector_to_cblinfun_inj[of UNIV]
    by (auto simp: o_def inj_on_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>v \<in> spectral_dec_vecs_tc \<rho>. one_dim_iso \<sigma> *\<^sub>C tc_butterfly v v)\<close>
    apply (rule infsum_cong)
    apply (subst one_dim_scaleC_1[symmetric])
    apply (rule from_trace_class_inject[THEN iffD1])
    apply (simp only: sandwich_tc_def compose_tcl.rep_eq compose_tcr.rep_eq scaleC_trace_class.rep_eq
        tc_butterfly.rep_eq cblinfun_compose_scaleC_right cblinfun_compose_scaleC_left)
    by (simp flip: butterfly_def_one_dim)
  also have \<open>\<dots> = one_dim_iso \<sigma> *\<^sub>C (\<Sum>\<^sub>\<infinity>v \<in> spectral_dec_vecs_tc \<rho>. tc_butterfly v v)\<close>
    using infsum_scaleC_right by fastforce
  also have \<open>\<dots> = one_dim_iso \<sigma> *\<^sub>C \<rho>\<close>
    by (simp add: assms butterfly_spectral_dec_vec_tc_has_sum infsumI)
  finally show ?thesis
    by -
qed

lemma kf_constant_apply: 
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_apply (kf_constant \<rho>) \<sigma> = trace_tc \<sigma> *\<^sub>C \<rho>\<close>
  using assms by (simp add: kf_constant_def kf_comp_apply kf_trace_is_trace kf_constant_onedim_apply)

lemma kf_bound_constant_onedim[simp]: 
  fixes \<rho> :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_bound (kf_constant_onedim \<rho>) = norm \<rho> *\<^sub>R id_cblinfun\<close>
proof (rule cblinfun_cinner_eqI)
  fix \<psi> :: 'b assume \<open>norm \<psi> = 1\<close>
  have \<open>\<psi> \<bullet>\<^sub>C kf_bound (kf_constant_onedim \<rho>) \<psi> = trace_tc (kf_apply (kf_constant_onedim \<rho>) (tc_butterfly \<psi> \<psi>))\<close>
    by (rule kf_bound_from_map)
  also have \<open>\<dots> = trace_tc (trace_tc (tc_butterfly \<psi> \<psi>) *\<^sub>C \<rho>)\<close>
    by (simp add: kf_constant_onedim_apply assms)
  also have \<open>\<dots> = trace_tc \<rho>\<close>
    by (metis \<open>norm \<psi> = 1\<close> cinner_complex_def complex_cnj_one complex_vector.vector_space_assms(4) norm_mult norm_one norm_tc_butterfly norm_tc_pos of_real_hom.hom_one one_cinner_one tc_butterfly_pos)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C (trace_tc \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by (metis \<open>norm \<psi> = 1\<close> cblinfun.scaleC_left cinner_scaleC_right cnorm_eq_1 id_apply id_cblinfun.rep_eq of_complex_def one_dim_iso_id one_dim_iso_is_of_complex scaleC_conv_of_complex)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>R id_cblinfun) \<psi>\<close>
    by (simp add: assms norm_tc_pos scaleR_scaleC)
  finally show \<open>\<psi> \<bullet>\<^sub>C kf_bound (kf_constant_onedim \<rho>) \<psi> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>R id_cblinfun) \<psi>\<close>
    by -
qed

lemma kf_bound_constant[simp]: 
  fixes \<rho> :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_bound (kf_constant \<rho>) = norm \<rho> *\<^sub>R id_cblinfun\<close>
  apply (rule cblinfun_cinner_eqI)
  using assms
  by (simp add: kf_bound_from_map kf_constant_apply trace_tc_butterfly norm_tc_pos scaleR_scaleC trace_tc_scaleC)
  
lemma kf_norm_constant_onedim[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_norm (kf_constant_onedim \<rho>) = norm \<rho>\<close>
  using assms
  by (simp add: kf_bound_constant kf_norm_def)

lemma kf_norm_constant:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_norm (kf_constant \<rho> :: ('a::{chilbert_space,not_singleton},'b::chilbert_space,_) kraus_family) = norm \<rho>\<close>
  using assms by (simp add: kf_norm_def norm_cblinfun_id)

lemma kf_norm_constant_leq:
  shows \<open>kf_norm (kf_constant \<rho>) \<le> norm \<rho>\<close>
  apply (cases \<open>\<rho> \<ge> 0\<close>)
   apply (simp add: kf_norm_def)
   apply (metis Groups.mult_ac(2) mult_cancel_right1 mult_left_mono norm_cblinfun_id_le norm_ge_zero)
  by (simp add: kf_constant_invalid)

lemma kf_comp_constant_right:
  assumes [iff]: \<open>t \<ge> 0\<close>
  shows \<open>kf_map fst (kf_comp E (kf_constant t)) \<equiv>\<^sub>k\<^sub>r kf_constant (E *\<^sub>k\<^sub>r t)\<close>
proof (rule kf_eqI)
  fix \<rho> :: \<open>('b, 'b) trace_class\<close> assume [iff]: \<open>\<rho> \<ge> 0\<close>
  have [simp]: \<open>fst -` {()} = UNIV\<close>
    by auto
  have [simp]: \<open>{()} = UNIV\<close>
    by auto
  fix x
  have \<open>kf_map fst (kf_comp E (kf_constant t)) *\<^sub>k\<^sub>r @{x} \<rho> = kf_comp E (kf_constant t) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_apply_on_map)
  also have \<open>\<dots> = E *\<^sub>k\<^sub>r trace_tc \<rho> *\<^sub>C t\<close>
    by (simp add: kf_comp_apply kf_constant_apply)
  also have \<open>\<dots> = kf_constant (E *\<^sub>k\<^sub>r t) *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by (simp add: kf_constant_apply kf_apply_pos kf_apply_scaleC)
  finally show \<open>kf_map fst (kf_comp E (kf_constant t)) *\<^sub>k\<^sub>r @{x} \<rho> = kf_constant (E *\<^sub>k\<^sub>r t) *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by -
qed

lemma kf_comp_constant_right_weak:
  assumes [iff]: \<open>t \<ge> 0\<close>
  shows \<open>kf_comp E (kf_constant t) =\<^sub>k\<^sub>r kf_constant (E *\<^sub>k\<^sub>r t)\<close>
  by (metis assms kf_apply_map kf_comp_constant_right kf_eq_imp_eq_weak kf_eq_weak_def)


subsection \<open>Tensor products\<close>

lemma kf_tensor_raw_bound_aux:
  fixes \<EE> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) set\<close> and \<FF> :: \<open>('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y) set\<close>
  assumes \<open>\<And>S. finite S \<Longrightarrow> S \<subseteq> \<EE> \<Longrightarrow> (\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
  assumes \<open>\<And>S. finite S \<Longrightarrow> S \<subseteq> \<FF> \<Longrightarrow> (\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> C\<close>
  assumes \<open>finite U\<close>
  assumes \<open>U \<subseteq> ((\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) ` (\<EE> \<times> \<FF>))\<close>
  shows \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> B \<otimes>\<^sub>o C\<close>
proof -
  from assms(1)[where S=\<open>{}\<close>] have [simp]: \<open>B \<ge> 0\<close>
    by simp
  define f :: \<open>(('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) \<times> ('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y)) \<Rightarrow> _\<close>
    where \<open>f = (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y)))\<close>
  from assms
  obtain V where V_subset: \<open>V \<subseteq> \<EE> \<times> \<FF>\<close> and [simp]: \<open>finite V\<close> and \<open>U = f ` V\<close>
    apply (simp flip: f_def)
    by (meson finite_subset_image)
  define W where \<open>W = fst ` V \<times> snd ` V\<close>
  have \<open>inj_on f W\<close>
    by (auto intro!: inj_onI simp: f_def)
  from \<open>finite V\<close> have [simp]: \<open>finite W\<close>
    using W_def by blast
  have \<open>W \<supseteq> V\<close>
    by (auto intro!: image_eqI simp: W_def)
  have \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> (\<Sum>(G, z)\<in>f ` W. G* o\<^sub>C\<^sub>L G)\<close>
    using \<open>U = f ` V\<close> \<open>V \<subseteq> W\<close>
    by (auto intro!: sum_mono2 positive_cblinfun_squareI)
  also have \<open>\<dots> = (\<Sum>((E,x),(F,y))\<in>W. (E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F))\<close>
    apply (subst sum.reindex)
    using \<open>inj_on f W\<close>
    by (auto simp: case_prod_unfold f_def)
  also have \<open>\<dots> = (\<Sum>((E,x),(F,y))\<in>W. (E* o\<^sub>C\<^sub>L E) \<otimes>\<^sub>o (F* o\<^sub>C\<^sub>L F))\<close>
    by (simp add: comp_tensor_op tensor_op_adjoint)
  also have \<open>\<dots> = (\<Sum>(E,x)\<in>fst`V. E* o\<^sub>C\<^sub>L E) \<otimes>\<^sub>o (\<Sum>(F,y)\<in>snd`V. F* o\<^sub>C\<^sub>L F)\<close>
    unfolding W_def
    apply (subst sum.Sigma[symmetric])
      apply simp
     apply simp
    apply (simp add: case_prod_beta tensor_op_cbilinear.sum_left) 
    by (simp add:  tensor_op_cbilinear.sum_right)
  also have \<open>\<dots> \<le> B \<otimes>\<^sub>o C\<close>
    using V_subset
    by (auto intro!: tensor_op_mono assms sum_nonneg intro: positive_cblinfun_squareI)
  finally show ?thesis
    by-
qed


lift_definition kf_tensor_raw :: \<open>('a ell2, 'b ell2, 'x) kraus_family \<Rightarrow> ('c ell2, 'd ell2, 'y) kraus_family \<Rightarrow> 
          (('a\<times>'c) ell2, ('b\<times>'d) ell2, (('a ell2\<Rightarrow>\<^sub>C\<^sub>L'b ell2)\<times>('c ell2\<Rightarrow>\<^sub>C\<^sub>L'd ell2)\<times>'x\<times>'y)) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y))) ` (\<EE>\<times>\<FF>)\<close>
proof (rename_tac \<EE> \<FF>, intro CollectI)
  fix \<EE> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) set\<close> and \<FF> :: \<open>('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close> and \<open>\<FF> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
    by auto
  define tensor where \<open>tensor = ((\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) ` (\<EE> \<times> \<FF>))\<close>
  show \<open>kraus_family tensor\<close>
  proof (intro kraus_familyI)
    from \<open>kraus_family \<EE>\<close>
    obtain B where B: \<open>(\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite S\<close> and \<open>S \<subseteq> \<EE>\<close> for S
      apply atomize_elim
      by (auto simp: kraus_family_def bdd_above_def)
    from B[where S=\<open>{}\<close>] have [simp]: \<open>B \<ge> 0\<close>
      by simp
    from \<open>kraus_family \<FF>\<close>
    obtain C where C: \<open>(\<Sum>(F, x)\<in>T. F* o\<^sub>C\<^sub>L F) \<le> C\<close> if \<open>finite T\<close> and \<open>T \<subseteq> \<FF>\<close> for T
      apply atomize_elim
      by (auto simp: kraus_family_def bdd_above_def)
    have \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> B \<otimes>\<^sub>o C\<close> if \<open>finite U\<close> and \<open>U \<subseteq> tensor\<close> for U
      using that by (auto intro!: kf_tensor_raw_bound_aux B C simp: tensor_def)
    then show \<open>bdd_above ((\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> tensor})\<close>
      by fast
    show \<open>0 \<notin> fst ` tensor\<close>
    proof (rule notI)
      assume \<open>0 \<in> fst ` tensor\<close>
      then obtain E F x y where EF0: \<open>E \<otimes>\<^sub>o F = 0\<close> and Ex: \<open>(E,x) \<in> \<EE>\<close> and Fy: \<open>(F,y) \<in> \<FF>\<close>
        by (auto intro!: simp: tensor_def)
      from \<open>kraus_family \<EE>\<close> Ex
      have \<open>E \<noteq> 0\<close>
        by (force simp: kraus_family_def)
      from \<open>kraus_family \<FF>\<close> Fy
      have \<open>F \<noteq> 0\<close>
        by (force simp: kraus_family_def)
      from \<open>E \<noteq> 0\<close> \<open>F \<noteq> 0\<close> have \<open>E \<otimes>\<^sub>o F \<noteq> 0\<close>
        using tensor_op_nonzero by blast
      with EF0 show False
        by simp
    qed
  qed
qed

lemma kf_apply_tensor_raw_as_infsum:
  \<open>kf_tensor_raw \<EE> \<FF> *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) \<rho>)\<close>
proof -
  have inj: \<open>inj_on (\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>)\<close>
    by (auto intro!: inj_onI)
  show \<open>kf_apply (kf_tensor_raw \<EE> \<FF>) \<rho>
      = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) \<rho>)\<close>
    apply (simp add: kf_apply.rep_eq kf_tensor_raw.rep_eq infsum_reindex inj o_def)
    by (simp add: case_prod_unfold)
qed

lemma kf_apply_tensor_raw:
  shows \<open>kf_tensor_raw \<EE> \<FF> *\<^sub>k\<^sub>r tc_tensor \<rho> \<sigma> = tc_tensor (\<EE> *\<^sub>k\<^sub>r \<rho>) (\<FF> *\<^sub>k\<^sub>r \<sigma>)\<close>
proof -
  have inj: \<open>inj_on (\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>)\<close>
    by (auto intro!: inj_onI)
  have [simp]: \<open>bounded_linear (\<lambda>x. tc_tensor x (kf_apply \<FF> \<sigma>))\<close>
    by (intro bounded_linear_intros)
  have [simp]: \<open>bounded_linear (tc_tensor (sandwich_tc E \<rho>))\<close> for E
    by (intro bounded_linear_intros)
  have sum2: \<open>(\<lambda>(E, x). sandwich_tc E \<rho>) summable_on Rep_kraus_family \<EE>\<close>
    using kf_apply_summable by blast
  have sum3: \<open>(\<lambda>(F, y). sandwich_tc F \<sigma>) summable_on Rep_kraus_family \<FF>\<close>
    using kf_apply_summable by blast

  from kf_apply_summable[of _ \<open>kf_tensor_raw \<EE> \<FF>\<close>]
  have sum1: \<open>(\<lambda>((E, x), F, y). sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>)) summable_on Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>\<close>
    apply (simp add: kf_apply.rep_eq kf_tensor_raw.rep_eq summable_on_reindex inj o_def)
    by (simp add: case_prod_unfold)

  have \<open>kf_apply (kf_tensor_raw \<EE> \<FF>) (tc_tensor \<rho> \<sigma>)
      = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    by (rule kf_apply_tensor_raw_as_infsum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    apply (subst infsum_Sigma_banach[symmetric])
    using sum1 by (auto intro!: simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. tc_tensor (sandwich_tc E \<rho>) (sandwich_tc F \<sigma>))\<close>
    by (simp add: sandwich_tc_tensor)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. (sandwich_tc F \<sigma>)))\<close>
    apply (subst infsum_bounded_linear[where h=\<open>tc_tensor (sandwich_tc _ \<rho>)\<close>, symmetric])
      apply (auto intro!: sum3)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) (kf_apply \<FF> \<sigma>))\<close>
    by (simp add: kf_apply_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>) (kf_apply \<FF> \<sigma>)\<close>
    apply (subst infsum_bounded_linear[where h=\<open>\<lambda>x. tc_tensor x (kf_apply \<FF> \<sigma>)\<close>, symmetric])
      apply (auto intro!: sum2)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (kf_apply \<EE> \<rho>) (kf_apply \<FF> \<sigma>)\<close>
    by (simp add: kf_apply_def case_prod_unfold)
  finally show ?thesis
    by -
qed

hide_fact kf_tensor_raw_bound_aux

definition \<open>kf_tensor \<EE> \<FF> = kf_map (\<lambda>(E, F, x, y). (x,y)) (kf_tensor_raw \<EE> \<FF>)\<close>

lemma kf_apply_tensor:
  \<open>kf_tensor \<EE> \<FF> *\<^sub>k\<^sub>r tc_tensor \<rho> \<sigma> = tc_tensor (\<EE> *\<^sub>k\<^sub>r \<rho>) (\<FF> *\<^sub>k\<^sub>r \<sigma>)\<close>
  by (auto intro!: simp: kf_tensor_def kf_apply_map kf_apply_tensor_raw)

lemma kf_apply_tensor_as_infsum:
  \<open>kf_tensor \<EE> \<FF> *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) \<rho>)\<close>
  by (simp add: kf_tensor_def kf_apply_tensor_raw_as_infsum)


lemma kf_bound_tensor_raw:
  \<open>kf_bound (kf_tensor_raw \<EE> \<FF>) = kf_bound \<EE> \<otimes>\<^sub>o kf_bound \<FF>\<close>
proof (rule cblinfun_cinner_tensor_eqI)
  fix \<psi> \<phi>

  from kf_bound_summable[of \<open>kf_tensor_raw \<EE> \<FF>\<close>]
  have sum1: \<open>summable_on_in cweak_operator_topology (\<lambda>((E,x),(F,y)). (E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F))
     (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>)\<close>
    unfolding kf_tensor_raw.rep_eq
    apply (subst (asm) summable_on_in_reindex)
    by (auto simp add: kf_tensor_raw.rep_eq case_prod_unfold inj_on_def o_def)
  have sum4: \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
    using kf_bound_summable by blast
  have sum5: \<open>summable_on_in cweak_operator_topology (\<lambda>(F,y). F* o\<^sub>C\<^sub>L F) (Rep_kraus_family \<FF>)\<close>
    using kf_bound_summable by blast
  have sum2: \<open>(\<lambda>(E, x). \<psi> \<bullet>\<^sub>C ((E* o\<^sub>C\<^sub>L E) *\<^sub>V \<psi>)) abs_summable_on Rep_kraus_family \<EE>\<close>
    using kf_bound_summable by (auto intro!: summable_on_in_cweak_operator_topology_pointwise 
        simp add: case_prod_unfold simp flip: summable_on_iff_abs_summable_on_complex
        simp del: cblinfun_apply_cblinfun_compose)
  have sum3: \<open>(\<lambda>(F,y). \<phi> \<bullet>\<^sub>C ((F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) abs_summable_on Rep_kraus_family \<FF>\<close>
    using kf_bound_summable by (auto intro!: summable_on_in_cweak_operator_topology_pointwise
        simp add: case_prod_unfold simp flip: summable_on_iff_abs_summable_on_complex
        simp del: cblinfun_apply_cblinfun_compose)

  have \<open>(\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (kf_bound (kf_tensor_raw \<EE> \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>)
      = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C
        (infsum_in cweak_operator_topology ((\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) \<circ> (\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)))
          (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>) *\<^sub>V
         \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    unfolding kf_bound.rep_eq kf_tensor_raw.rep_eq
    apply (subst infsum_in_reindex)
    by (auto simp add: inj_on_def case_prod_unfold)
  also have \<open>\<dots> = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C
        (infsum_in cweak_operator_topology (\<lambda>((E,x),(F,y)). (E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F))
            (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>) *\<^sub>V
         \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y)) \<in> Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>.
                         (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C ((E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F)) (\<psi> \<otimes>\<^sub>s \<phi>))\<close>
    apply (subst infsum_in_cweak_operator_topology_pointwise)
    using sum1 by (auto intro!: simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y)) \<in> Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>.
                     (\<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<psi>) * (\<phi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>))\<close>
    apply (rule infsum_cong)
    by (simp_all add: tensor_op_adjoint tensor_op_ell2)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x) \<in> Rep_kraus_family \<EE>. \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<psi>)
                      * (\<Sum>\<^sub>\<infinity>(F,y) \<in> Rep_kraus_family \<FF>. \<phi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>)\<close>
    apply (subst infsum_product')
    using sum2 sum3 by (simp_all add: case_prod_unfold)
  also have \<open>\<dots> = (\<psi> \<bullet>\<^sub>C kf_bound \<EE> \<psi>) * (\<phi> \<bullet>\<^sub>C kf_bound \<FF> \<phi>)\<close>
    unfolding kf_bound.rep_eq case_prod_unfold
    apply (subst infsum_in_cweak_operator_topology_pointwise[symmetric])
    using sum4 apply (simp add: case_prod_unfold)
    apply (subst infsum_in_cweak_operator_topology_pointwise[symmetric])
    using sum5 apply (simp add: case_prod_unfold)
    by (rule refl)
  also have \<open>\<dots> = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C ((kf_bound \<EE> \<otimes>\<^sub>o kf_bound \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    by (simp add: tensor_op_ell2)
  finally show \<open>(\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (kf_bound (kf_tensor_raw \<EE> \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>) =
       (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C ((kf_bound \<EE> \<otimes>\<^sub>o kf_bound \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    by -
qed


lemma kf_bound_tensor:
  \<open>kf_bound (kf_tensor \<EE> \<FF>) = kf_bound \<EE> \<otimes>\<^sub>o kf_bound \<FF>\<close>
  by (simp add: kf_tensor_def kf_map_bound kf_bound_tensor_raw) 

lemma kf_norm_tensor:
  \<open>kf_norm (kf_tensor \<EE> \<FF>) = kf_norm \<EE> * kf_norm \<FF>\<close>
  by (auto intro!: norm_cblinfun_mono
      simp add: kf_norm_def kf_bound_tensor
      simp flip: tensor_op_norm)

lemma kf_tensor_cong_weak:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<EE>'\<close>
  assumes \<open>\<FF> =\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_tensor \<EE> \<FF> =\<^sub>k\<^sub>r kf_tensor \<EE>' \<FF>'\<close>
proof (rule kf_eq_weakI)
  show \<open>kf_apply (kf_tensor \<EE> \<FF>) \<rho> = kf_apply (kf_tensor \<EE>' \<FF>') \<rho>\<close> for \<rho>
  proof (rule eq_from_separatingI2x[where x=\<rho>, OF separating_set_bounded_clinear_tc_tensor])
    show \<open>bounded_clinear (kf_apply (kf_tensor \<EE> \<FF>))\<close>
      by (simp add: kf_apply_bounded_clinear)
    show \<open>bounded_clinear (kf_apply (kf_tensor \<EE>' \<FF>'))\<close>
      by (simp add: kf_apply_bounded_clinear)
    have \<EE>\<EE>': \<open>kf_apply \<EE> \<rho> = kf_apply \<EE>' \<rho>\<close> for \<rho>
      by (metis assms(1) kf_eq_weak_def)
    have \<FF>\<FF>': \<open>kf_apply \<FF> \<rho> = kf_apply \<FF>' \<rho>\<close> for \<rho>
      by (metis assms(2) kf_eq_weak_def)
    fix \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('e ell2, 'e ell2) trace_class\<close>
    show \<open>kf_apply (kf_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>) = kf_apply (kf_tensor \<EE>' \<FF>') (tc_tensor \<rho> \<sigma>)\<close>
      by (auto intro!: simp: kf_apply_tensor \<EE>\<EE>' \<FF>\<FF>'
          simp flip: tensor_ell2_ket tensor_tc_butterfly)
  qed
qed

lemma kf_filter_tensor:
  \<open>kf_filter (\<lambda>(x,y). P x \<and> Q y) (kf_tensor \<EE> \<FF>) = kf_tensor (kf_filter P \<EE>) (kf_filter Q \<FF>)\<close>
  apply (simp add: kf_tensor_def kf_filter_map)
  apply (rule arg_cong[where f=\<open>kf_map _\<close>])
  apply transfer
  by (force simp add: image_iff case_prod_unfold)

lemma kf_filter_tensor_singleton:
  \<open>kf_filter ((=) x) (kf_tensor \<EE> \<FF>) = kf_tensor (kf_filter ((=) (fst x)) \<EE>) (kf_filter ((=) (snd x)) \<FF>)\<close>
  by (simp add: kf_filter_tensor[symmetric] case_prod_unfold prod_eq_iff)

lemma kf_tensor_cong:
  fixes \<EE> \<EE>' :: \<open>('a ell2, 'b ell2, 'x) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('c ell2, 'd ell2, 'y) kraus_family\<close>
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<EE>'\<close>
  assumes \<open>\<FF> \<equiv>\<^sub>k\<^sub>r \<FF>'\<close>
  shows \<open>kf_tensor \<EE> \<FF> \<equiv>\<^sub>k\<^sub>r kf_tensor \<EE>' \<FF>'\<close>
proof (rule kf_eqI)
  fix xy :: \<open>'x \<times> 'y\<close> and \<rho>
  obtain x y where [simp]: \<open>xy = (x,y)\<close>
    by fastforce
  have aux1: \<open>(\<lambda>xy'. xy' = (x, y)) = (\<lambda>(x', y'). x' = x \<and> y' = y)\<close>
    by auto
  have \<open>kf_apply_on (kf_tensor \<EE> \<FF>) {xy}
         = kf_apply (kf_tensor (kf_filter (\<lambda>z. z = x) \<EE>) (kf_filter (\<lambda>z. z = y) \<FF>))\<close>
    apply (simp add: kf_apply_on_def aux1 kf_filter_tensor)
    apply (subst aux1)
    by (simp add: kf_apply_on_def aux1 kf_filter_tensor)
  also have \<open>\<dots> = kf_apply (kf_tensor (kf_filter (\<lambda>z. z = x) \<EE>') (kf_filter (\<lambda>z. z = y) \<FF>'))\<close>
    apply (rule ext)
    apply (rule kf_apply_eqI)
    apply (rule kf_tensor_cong_weak)
    by (auto intro!: kf_filter_cong_weak assms)
  also have \<open>\<dots> = kf_apply_on (kf_tensor \<EE>' \<FF>') {xy}\<close>
    apply (simp add: kf_apply_on_def aux1 kf_filter_tensor)
    apply (subst aux1)
    by (simp add: kf_apply_on_def aux1 kf_filter_tensor)
  finally show \<open>kf_tensor \<EE> \<FF> *\<^sub>k\<^sub>r @{xy} \<rho> = kf_tensor \<EE>' \<FF>' *\<^sub>k\<^sub>r @{xy} \<rho>\<close>
    by simp
qed


lemma kf_tensor_compose_distrib_weak:
  shows \<open>kf_tensor (kf_comp \<EE> \<FF>) (kf_comp \<GG> \<HH>)
     =\<^sub>k\<^sub>r kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>)\<close>
  by (auto intro!: eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor]
      kf_apply_bounded_clinear comp_bounded_clinear
      simp: kf_eq_weak_def kf_apply_tensor kf_comp_apply)

lemma kf_tensor_compose_distrib:
  shows \<open>kf_tensor (kf_comp \<EE> \<FF>) (kf_comp \<GG> \<HH>)
     \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>((e,g),(f,h)). ((e,f),(g,h))) (kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>))\<close>
proof (rule kf_eqI_from_filter_eq_weak)
  fix efgh :: \<open>('e \<times> 'f) \<times> ('g \<times> 'h)\<close>
  obtain e f g h where efgh: \<open>efgh = ((e,f),(g,h))\<close>
    apply atomize_elim
    apply (cases efgh)
    by auto
  have \<open>kf_filter ((=) efgh) (kf_tensor (kf_comp \<EE> \<FF>) (kf_comp \<GG> \<HH>))
         =\<^sub>k\<^sub>r kf_filter (\<lambda>(x,y). (e,f)=x \<and> (g,h)=y) (kf_tensor (kf_comp \<EE> \<FF>) (kf_comp \<GG> \<HH>))\<close>
    by (smt (verit, best) case_prod_unfold kf_eq_def kf_filter_cong_weak split_pairs2 efgh)
  also have \<open>\<dots> = kf_tensor (kf_filter ((=) (e,f)) (kf_comp \<EE> \<FF>)) (kf_filter ((=) (g,h)) (kf_comp \<GG> \<HH>))\<close>
    by (simp add: kf_filter_tensor)
  also have \<open>\<dots> = kf_tensor (kf_filter (\<lambda>(e',f'). f=f' \<and> e=e') (kf_comp \<EE> \<FF>)) (kf_filter (\<lambda>(g',h'). h=h' \<and> g=g') (kf_comp \<GG> \<HH>))\<close>
    apply (intro arg_cong2[where f=kf_tensor] arg_cong2[where f=kf_filter])
    by auto
  also have \<open>\<dots> = kf_tensor (kf_comp (kf_filter ((=) f) \<EE>) (kf_filter ((=) e) \<FF>)) (kf_comp (kf_filter ((=) h) \<GG>) (kf_filter ((=) g) \<HH>))\<close>
    by (simp add: kf_filter_comp)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_comp (kf_tensor (kf_filter ((=) f) \<EE>) (kf_filter ((=) h) \<GG>)) (kf_tensor (kf_filter ((=) e) \<FF>) (kf_filter ((=) g) \<HH>))\<close>
    by (rule kf_tensor_compose_distrib_weak)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_filter (\<lambda>((e',g'), (f',h')). (f = f' \<and> h = h') \<and> (e = e' \<and> g = g')) (kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>))\<close>
    by (simp add: case_prod_unfold flip: kf_filter_tensor kf_filter_comp)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_map (\<lambda>((e,g),(f,h)). ((e,f),(g,h))) (kf_filter (\<lambda>((e',g'), (f',h')). (f = f' \<and> h = h') \<and> (e = e' \<and> g = g')) (kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>)))\<close>
    by (simp add: kf_eq_weak_def)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_filter (\<lambda>((e',f'), (g',h')). (f = f' \<and> h = h') \<and> (e = e' \<and> g = g')) (kf_map (\<lambda>((e,g),(f,h)). ((e,f),(g,h))) (kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>)))\<close>
    by (simp add: kf_filter_map case_prod_unfold)
  also have \<open>\<dots> = kf_filter ((=) efgh) (kf_map (\<lambda>((e,g),(f,h)). ((e,f),(g,h))) (kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>)))\<close>
    apply (rule arg_cong2[where f=\<open>kf_filter\<close>])
    by (auto simp: efgh)
  finally show \<open>kf_filter ((=) efgh) (kf_tensor (kf_comp \<EE> \<FF>) (kf_comp \<GG> \<HH>)) =\<^sub>k\<^sub>r \<dots>\<close>
    by -
qed

lemma kf_tensor_compose_distrib':
  shows \<open>kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>)
     \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>((e,f),(g,h)). ((e,g),(f,h))) (kf_tensor (kf_comp \<EE> \<FF>) (kf_comp \<GG> \<HH>))\<close>
proof -
  have aux: \<open>((\<lambda>((e,f),(g,h)). ((e,g),(f,h))) o (\<lambda>((e,g),(f,h)). ((e,f),(g,h)))) = id\<close>
    by auto
  have \<open>kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>) \<equiv>\<^sub>k\<^sub>r kf_map ((\<lambda>((e,f),(g,h)). ((e,g),(f,h))) o (\<lambda>((e,g),(f,h)). ((e,f),(g,h)))) (kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>))\<close>
    by (simp add: aux kf_eq_sym kf_map_id)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>((e,f),(g,h)). ((e,g),(f,h))) (kf_map (\<lambda>((e,g),(f,h)). ((e,f),(g,h))) (kf_comp (kf_tensor \<EE> \<GG>) (kf_tensor \<FF> \<HH>)))\<close>
    using kf_eq_sym kf_map_twice by blast
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>((e,f),(g,h)). ((e,g),(f,h))) (kf_tensor (kf_comp \<EE> \<FF>) (kf_comp \<GG> \<HH>))\<close>
    using kf_eq_sym kf_map_cong[OF refl] kf_tensor_compose_distrib by blast
  finally show ?thesis
    by -
qed


definition kf_tensor_right :: \<open>('extra ell2, 'extra ell2) trace_class \<Rightarrow> ('qu ell2, ('qu\<times>'extra) ell2, unit) kraus_family\<close> where
  \<comment> \<open>\<^term>\<open>kf_tensor_right \<rho>\<close> maps \<^term>\<open>\<sigma>\<close> to \<^term>\<open>\<sigma> \<otimes>\<^sub>o \<rho>\<close>\<close>
  \<open>kf_tensor_right \<rho> = kf_map_inj (\<lambda>_. ()) (kf_comp (kf_tensor kf_id (kf_constant_onedim \<rho>)) (kf_of_op (tensor_ell2_right (ket ()))))\<close>
definition kf_tensor_left :: \<open>('extra ell2, 'extra ell2) trace_class \<Rightarrow> ('qu ell2, ('extra\<times>'qu) ell2, unit) kraus_family\<close> where
  \<comment> \<open>\<^term>\<open>kf_tensor_right \<rho>\<close> maps \<^term>\<open>\<sigma>\<close> to \<^term>\<open>\<rho> \<otimes>\<^sub>o \<sigma>\<close>\<close>
  \<open>kf_tensor_left \<rho> = kf_map_inj (\<lambda>_. ()) (kf_comp (kf_tensor (kf_constant_onedim \<rho>) kf_id) (kf_of_op (tensor_ell2_left (ket ()))))\<close>

lemma kf_apply_tensor_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_tensor_right \<rho> *\<^sub>k\<^sub>r \<sigma> = tc_tensor \<sigma> \<rho>\<close>
proof -
  have *: \<open>sandwich_tc (tensor_ell2_right (ket ())) \<sigma> = tc_tensor \<sigma> (tc_butterfly (ket()) (ket()))\<close>
    apply transfer'
    using sandwich_tensor_ell2_right' by blast
  show ?thesis
    by (simp add: kf_tensor_right_def kf_apply_map_inj inj_on_def kf_comp_apply
        kf_of_op_apply * kf_apply_tensor kf_constant_onedim_apply assms trace_tc_butterfly
        flip: trace_tc_one_dim_iso)
qed
lemma kf_apply_tensor_left[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_tensor_left \<rho> *\<^sub>k\<^sub>r \<sigma> = tc_tensor \<rho> \<sigma>\<close>
proof -
  have *: \<open>sandwich_tc (tensor_ell2_left (ket ())) \<sigma> = tc_tensor (tc_butterfly (ket()) (ket())) \<sigma>\<close>
    apply transfer'
    using sandwich_tensor_ell2_left' by blast
  show ?thesis
    by (simp add: kf_tensor_left_def kf_apply_map_inj inj_on_def kf_comp_apply
        kf_of_op_apply * kf_apply_tensor kf_constant_onedim_apply assms trace_tc_butterfly
        flip: trace_tc_one_dim_iso)
qed

lemma kf_bound_tensor_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_bound (kf_tensor_right \<rho>) = norm \<rho> *\<^sub>C id_cblinfun\<close>
proof (rule cblinfun_cinner_eqI)
  fix \<psi> :: \<open>'b ell2\<close>
  have \<open>\<psi> \<bullet>\<^sub>C kf_bound (kf_tensor_right \<rho>) \<psi> = trace_tc (kf_tensor_right \<rho> *\<^sub>k\<^sub>r tc_butterfly \<psi> \<psi>)\<close>
    by (simp add: kf_bound_from_map)
  also have \<open>\<dots> = trace_tc (tc_tensor (tc_butterfly \<psi> \<psi>) \<rho>)\<close>
    using assms by (simp add: kf_apply_tensor_right)
  also have \<open>\<dots> = trace_tc (tc_butterfly \<psi> \<psi>) * trace_tc \<rho>\<close>
    by (metis (no_types, lifting) assms norm_tc_pos norm_tc_tensor of_real_mult tc_butterfly_pos tc_tensor_pos)
  also have \<open>\<dots> = norm \<rho> * trace_tc (tc_butterfly \<psi> \<psi>)\<close>
    by (simp add: assms norm_tc_pos)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by (simp add: trace_tc_butterfly)
  finally show \<open>\<psi> \<bullet>\<^sub>C (kf_bound (kf_tensor_right \<rho>)) \<psi> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by -
qed
lemma kf_bound_tensor_left[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_bound (kf_tensor_left \<rho>) = norm \<rho> *\<^sub>C id_cblinfun\<close>
proof (rule cblinfun_cinner_eqI)
  fix \<psi> :: \<open>'b ell2\<close>
  have \<open>\<psi> \<bullet>\<^sub>C kf_bound (kf_tensor_left \<rho>) \<psi> = trace_tc (kf_tensor_left \<rho> *\<^sub>k\<^sub>r tc_butterfly \<psi> \<psi>)\<close>
    by (simp add: kf_bound_from_map)
  also have \<open>\<dots> = trace_tc (tc_tensor \<rho> (tc_butterfly \<psi> \<psi>))\<close>
    using assms by (simp add: kf_apply_tensor_left)
  also have \<open>\<dots> = trace_tc \<rho> * trace_tc (tc_butterfly \<psi> \<psi>)\<close>
    by (metis (no_types, lifting) assms norm_tc_pos norm_tc_tensor of_real_mult tc_butterfly_pos tc_tensor_pos)
  also have \<open>\<dots> = norm \<rho> * trace_tc (tc_butterfly \<psi> \<psi>)\<close>
    by (simp add: assms norm_tc_pos)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by (simp add: trace_tc_butterfly)
  finally show \<open>\<psi> \<bullet>\<^sub>C (kf_bound (kf_tensor_left \<rho>)) \<psi> = \<psi> \<bullet>\<^sub>C (norm \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by -
qed


lemma kf_norm_tensor_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_norm (kf_tensor_right \<rho>) = norm \<rho>\<close>
  using assms by (simp add: kf_norm_def)
lemma kf_norm_tensor_left[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kf_norm (kf_tensor_left \<rho>) = norm \<rho>\<close>
  using assms by (simp add: kf_norm_def)


lemma kf_trace_preserving_tensor:
  assumes \<open>kf_trace_preserving \<EE>\<close> and \<open>kf_trace_preserving \<FF>\<close>
  shows \<open>kf_trace_preserving (kf_tensor \<EE> \<FF>)\<close>
  by (metis assms(1,2) kf_bound_tensor kf_trace_preserving_iff_bound_id tensor_id)

lemma kf_trace_reducing_tensor:
  assumes \<open>kf_trace_reducing \<EE>\<close> and \<open>kf_trace_reducing \<FF>\<close>
  shows \<open>kf_trace_reducing (kf_tensor \<EE> \<FF>)\<close>
  using assms 
  by (auto intro!: mult_le_one simp: kf_trace_reducing_iff_norm_leq1 kf_norm_tensor kf_norm_geq0)

lemma kf_tensor_map_left:
  \<open>kf_tensor (kf_map f \<EE>) \<FF> \<equiv>\<^sub>k\<^sub>r kf_map (apfst f) (kf_tensor \<EE> \<FF>)\<close>
proof (rule kf_eqI_from_filter_eq_weak)
  fix xy :: \<open>'e \<times> 'f\<close>
  obtain x y where xy: \<open>xy = (x,y)\<close>
    apply atomize_elim
    by (auto intro!: prod.exhaust)
  have \<open>kf_filter ((=) xy) (kf_tensor (kf_map f \<EE>) \<FF>) = kf_tensor (kf_filter ((=)x) (kf_map f \<EE>)) (kf_filter ((=)y) \<FF>)\<close>
    by (auto intro!: arg_cong2[where f=kf_filter] simp add: xy simp flip: kf_filter_tensor)
  also have \<open>\<dots> = kf_tensor (kf_map f (kf_filter (\<lambda>x'. x = f x') \<EE>)) (kf_filter ((=) y) \<FF>)\<close>
    by (simp add: kf_filter_map)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_tensor (kf_filter (\<lambda>x'. x = f x') \<EE>) (kf_filter ((=) y) \<FF>)\<close>
    apply (rule kf_tensor_cong_weak)
    by (simp_all add: kf_eq_weak_def)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_filter (\<lambda>(x',y'). x = f x' \<and> y = y') (kf_tensor \<EE> \<FF>)\<close>
    by (auto intro!: arg_cong2[where f=kf_filter] simp add: xy simp flip: kf_filter_tensor)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_map (apfst f) (kf_filter (\<lambda>(x',y'). x = f x' \<and> y = y') (kf_tensor \<EE> \<FF>))\<close>
    by (simp add: kf_eq_weak_def)
  also have \<open>\<dots> = kf_filter ((=) xy) (kf_map (apfst f) (kf_tensor \<EE> \<FF>))\<close>
    by (auto intro!: arg_cong2[where f=kf_map] arg_cong2[where f=kf_filter] simp add: xy kf_filter_map simp flip: )
  finally show \<open>kf_filter ((=) xy) (kf_tensor (kf_map f \<EE>) \<FF>) =\<^sub>k\<^sub>r \<dots>\<close>
    by -
qed

lemma kf_tensor_map_right:
  \<open>kf_tensor \<EE> (kf_map f \<FF>) \<equiv>\<^sub>k\<^sub>r kf_map (apsnd f) (kf_tensor \<EE> \<FF>)\<close>
proof (rule kf_eqI_from_filter_eq_weak)
  fix xy :: \<open>'e \<times> 'f\<close>
  obtain x y where xy: \<open>xy = (x,y)\<close>
    apply atomize_elim
    by (auto intro!: prod.exhaust)
  have \<open>kf_filter ((=) xy) (kf_tensor \<EE> (kf_map f \<FF>)) = kf_tensor (kf_filter ((=)x) \<EE>) (kf_filter ((=)y) (kf_map f \<FF>))\<close>
    by (auto intro!: arg_cong2[where f=kf_filter] simp add: xy simp flip: kf_filter_tensor)
  also have \<open>\<dots> = kf_tensor (kf_filter ((=)x) \<EE>) (kf_map f (kf_filter (\<lambda>y'. y = f y') \<FF>))\<close>
    by (simp add: kf_filter_map)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_tensor (kf_filter ((=)x) \<EE>) (kf_filter (\<lambda>y'. y = f y') \<FF>)\<close>
    apply (rule kf_tensor_cong_weak)
    by (simp_all add: kf_eq_weak_def)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_filter (\<lambda>(x',y'). x = x' \<and> y = f y') (kf_tensor \<EE> \<FF>)\<close>
    by (auto intro!: arg_cong2[where f=kf_filter] simp add: xy simp flip: kf_filter_tensor)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_map (apsnd f) (kf_filter (\<lambda>(x',y'). x = x' \<and> y = f y') (kf_tensor \<EE> \<FF>))\<close>
    by (simp add: kf_eq_weak_def)
  also have \<open>\<dots> = kf_filter ((=) xy) (kf_map (apsnd f) (kf_tensor \<EE> \<FF>))\<close>
    by (auto intro!: arg_cong2[where f=kf_map] arg_cong2[where f=kf_filter] simp add: xy kf_filter_map simp flip: )
  finally show \<open>kf_filter ((=) xy) (kf_tensor \<EE> (kf_map f \<FF>)) =\<^sub>k\<^sub>r \<dots>\<close>
    by -
qed

lemma kf_tensor_map_both:
  \<open>kf_tensor (kf_map f \<EE>) (kf_map g \<FF>) \<equiv>\<^sub>k\<^sub>r kf_map (map_prod f g) (kf_tensor \<EE> \<FF>)\<close>
  apply (rule kf_tensor_map_left[THEN kf_eq_trans])
  apply (rule kf_map_cong[THEN kf_eq_trans, OF refl])
   apply (rule kf_tensor_map_right)
  apply (rule kf_map_twice[THEN kf_eq_trans])
  by (simp add: o_def map_prod_def case_prod_unfold)

lemma kf_tensor_raw_map_inj_both:
  \<open>kf_tensor_raw (kf_map_inj f \<EE>) (kf_map_inj g \<FF>) = kf_map_inj (\<lambda>(E,F,x,y). (E,F,f x,g y)) (kf_tensor_raw \<EE> \<FF>)\<close>
  apply (transfer' fixing: f g)
  by force

lemma kf_domain_tensor_raw_subset:
  \<open>kf_domain (kf_tensor_raw \<EE> \<FF>) \<subseteq> kf_operators \<EE> \<times> kf_operators \<FF> \<times> kf_domain \<EE> \<times> kf_domain \<FF>\<close>
  apply transfer'
  by force

lemma kf_tensor_map_inj_both:
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  assumes \<open>inj_on g (kf_domain \<FF>)\<close>
  shows \<open>kf_tensor (kf_map_inj f \<EE>) (kf_map_inj g \<FF>) = kf_map_inj (map_prod f g) (kf_tensor \<EE> \<FF>)\<close>
proof -
  from assms
  have inj1: \<open>inj_on (\<lambda>(E, F, x, y). (E, F, f x, g y)) (kf_domain (kf_tensor_raw \<EE> \<FF>))\<close>
    using kf_domain_tensor_raw_subset[of \<EE> \<FF>]
    apply (simp add: inj_on_def ball_def split!: prod.split)
    by blast+
  from assms
  have inj2: \<open>inj_on (map_prod f g) ((\<lambda>(E, F, x). x) ` kf_domain (kf_tensor_raw \<EE> \<FF>))\<close>
    using kf_domain_tensor_raw_subset[of \<EE> \<FF>]
    apply (simp add: inj_on_def ball_def split!: prod.split)
    by blast+
  have \<open>kf_tensor (kf_map_inj f \<EE>) (kf_map_inj g \<FF>) = kf_map (\<lambda>(E, F, y). y) (kf_map_inj (\<lambda>(E, F, x, y). (E, F, f x, g y)) (kf_tensor_raw \<EE> \<FF>))\<close>
    by (simp add: kf_tensor_def kf_tensor_raw_map_inj_both id_def)
  also have \<open>\<dots> = kf_map (\<lambda>(E, F, x, y). (f x, g y)) (kf_tensor_raw \<EE> \<FF>)\<close>
    apply (subst kf_map_kf_map_inj_comp)
     apply (rule inj1)
    by (simp add: case_prod_unfold o_def)
  also have \<open>\<dots> = kf_map_inj (map_prod f g) (kf_map (\<lambda>(E, F, x). x) (kf_tensor_raw \<EE> \<FF>))\<close>
    apply (subst kf_map_inj_kf_map_comp)
    apply (rule inj2)
    by (simp add: o_def case_prod_unfold map_prod_def)
  also have \<open>\<dots> = kf_map_inj (map_prod f g) (kf_tensor \<EE> \<FF>)\<close>
    by (simp add: kf_tensor_def kf_tensor_raw_map_inj_both id_def)
  finally show ?thesis
    by -
qed

lemma kf_operators_tensor_raw:
  shows \<open>kf_operators (kf_tensor_raw \<EE> \<FF>) = {E \<otimes>\<^sub>o F | E F. E \<in> kf_operators \<EE> \<and> F \<in> kf_operators \<FF>}\<close>
  apply (simp add: kf_operators.rep_eq kf_tensor_raw.rep_eq)
  by (force simp: case_prod_unfold)

lemma kf_operators_tensor:
  shows \<open>kf_operators (kf_tensor \<EE> \<FF>) \<subseteq> span {E \<otimes>\<^sub>o F | E F. E \<in> kf_operators \<EE> \<and> F \<in> kf_operators \<FF>}\<close>
proof -
  have \<open>kf_operators (kf_tensor \<EE> \<FF>) \<subseteq> span (kf_operators (kf_tensor_raw \<EE> \<FF>))\<close>
    by (simp add: kf_operators_kf_map kf_tensor_def)
  also have \<open>\<dots> = span {E \<otimes>\<^sub>o F | E F. E \<in> kf_operators \<EE> \<and> F \<in> kf_operators \<FF>}\<close>
    by (metis kf_operators_tensor_raw)
  finally show ?thesis
    by -
qed

lemma kf_domain_tensor: \<open>kf_domain (kf_tensor \<EE> \<FF>) = kf_domain \<EE> \<times> kf_domain \<FF>\<close>
proof (intro Set.set_eqI iffI)
  fix xy assume xy_dom: \<open>xy \<in> kf_domain (kf_tensor \<EE> \<FF>)\<close>
  obtain x y where xy: \<open>xy = (x,y)\<close>
    by (auto simp: prod_eq_iff)
  from xy_dom obtain E F where \<open>(E,F,x,y) \<in> kf_domain (kf_tensor_raw \<EE> \<FF>)\<close>
    by (force simp add: kf_tensor_def xy)
  then obtain EF where EFEFxy: \<open>(EF,E,F,x,y) \<in> Rep_kraus_family (kf_tensor_raw \<EE> \<FF>)\<close>
    by (auto simp: kf_domain_def)
  then have \<open>EF = E \<otimes>\<^sub>o F\<close>
    by (force simp: kf_tensor_raw.rep_eq case_prod_unfold)
  from EFEFxy have \<open>EF \<noteq> 0\<close>
    using Rep_kraus_family
    by (force simp: kraus_family_def)
  with  \<open>EF = E \<otimes>\<^sub>o F\<close> have \<open>E \<noteq> 0\<close> and \<open>F \<noteq> 0\<close>
    by fastforce+
  from EFEFxy have \<open>(E,x) \<in> Rep_kraus_family \<EE>\<close>
    apply (transfer' fixing: E x)
    by auto
  with \<open>E \<noteq> 0\<close> have \<open>x \<in> kf_domain \<EE>\<close>
    apply (transfer' fixing: E x)
    by force
  from EFEFxy have \<open>(F,y) \<in> Rep_kraus_family \<FF>\<close>
    apply (transfer' fixing: F y)
    by auto
  with \<open>F \<noteq> 0\<close> have \<open>y \<in> kf_domain \<FF>\<close>
    apply (transfer' fixing: F y)
    by force
  from  \<open>x \<in> kf_domain \<EE>\<close>  \<open>y \<in> kf_domain \<FF>\<close>
  show \<open>xy \<in> kf_domain \<EE> \<times> kf_domain \<FF>\<close>
    by (simp add: xy)
next
  fix xy assume xy_dom: \<open>xy \<in> kf_domain \<EE> \<times> kf_domain \<FF>\<close>
  then obtain x y where xy: \<open>xy = (x,y)\<close> and xE: \<open>x \<in> kf_domain \<EE>\<close> and yF: \<open>y \<in> kf_domain \<FF>\<close>
    by (auto simp: prod_eq_iff)
  from xE obtain E where Ex: \<open>(E,x) \<in> Rep_kraus_family \<EE>\<close>
    by (auto simp: kf_domain_def)
  from yF obtain F where Fy: \<open>(F,y) \<in> Rep_kraus_family \<FF>\<close>
    by (auto simp: kf_domain_def)
  from Ex Fy have \<open>(E \<otimes>\<^sub>o F, E, F, x, y) \<in> Rep_kraus_family (kf_tensor_raw \<EE> \<FF>)\<close>
    by (force simp: kf_tensor_raw.rep_eq case_prod_unfold)
  moreover 
  have \<open>E \<noteq> 0\<close> and \<open>F \<noteq> 0\<close>
    using Ex Fy Rep_kraus_family
    by (force simp: kraus_family_def)+
  then have \<open>E \<otimes>\<^sub>o F \<noteq> 0\<close>
    by (simp add: tensor_op_nonzero)
  ultimately have \<open>(E, F, x, y) \<in> kf_domain (kf_tensor_raw \<EE> \<FF>)\<close>
    by (force simp: kf_domain_def)
  then show \<open>xy \<in> kf_domain (kf_tensor \<EE> \<FF>)\<close>
    by (force simp: kf_tensor_def xy case_prod_unfold)
qed

lemma kf_tensor_raw_0_left[simp]: \<open>kf_tensor_raw 0 \<EE> = 0\<close>
  apply transfer'
  by simp

lemma kf_tensor_raw_0_right[simp]: \<open>kf_tensor_raw \<EE> 0 = 0\<close>
  apply transfer'
  by simp

lemma kf_tensor_0_left[simp]: \<open>kf_tensor 0 \<EE> = 0\<close>
  by (simp add: kf_tensor_def)

lemma kf_tensor_0_right[simp]: \<open>kf_tensor \<EE> 0 = 0\<close>
  by (simp add: kf_tensor_def)

lemma kf_tensor_of_op:
  \<open>kf_tensor (kf_of_op A) (kf_of_op B) = kf_map (\<lambda>(). ((),())) (kf_of_op (A \<otimes>\<^sub>o B))\<close>
proof -
  wlog Aneq0: \<open>A \<noteq> 0\<close>
    using negation
    by simp
  wlog Bneq0: \<open>B \<noteq> 0\<close> keeping Aneq0
    using negation
    by simp
  have [simp]: \<open>(\<lambda>(). ((), ())) = Pair ()\<close>
    by auto
  have \<open>kf_tensor_raw (kf_of_op A) (kf_of_op B) = kf_map_inj (\<lambda>(). (A, B, (), ())) (kf_of_op (A \<otimes>\<^sub>o B))\<close>
    apply (transfer' fixing: A B)
    by (simp add: case_unit_Unity tensor_op_nonzero)
  then show ?thesis
    by (simp add: kf_tensor_def kf_map_kf_map_inj_comp inj_on_def o_def case_unit_Unity)
qed


subsection \<open>Partial trace\<close>

definition kf_partial_trace_right :: \<open>(('a\<times>'b) ell2, 'a ell2, 'b) kraus_family\<close> where
  \<open>kf_partial_trace_right = kf_map (\<lambda>((_,b),_). inv ket b)
  (kf_comp (kf_of_op (tensor_ell2_right (ket ())*))
   (kf_tensor kf_id (kf_trace (range ket))))\<close>

definition kf_partial_trace_left :: \<open>(('a\<times>'b) ell2, 'b ell2, 'a) kraus_family\<close> where
  \<open>kf_partial_trace_left = kf_map_inj snd (kf_comp kf_partial_trace_right (kf_of_op swap_ell2))\<close>

lemma partial_trace_is_kf_partial_trace: 
  fixes t :: \<open>(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close>
  shows \<open>partial_trace t = kf_partial_trace_right *\<^sub>k\<^sub>r t\<close>
proof -
  have \<open>partial_trace t = kf_apply (kf_of_op (tensor_ell2_right (ket ())*))
    (kf_apply (kf_tensor kf_id (kf_trace (range ket))) t)\<close>
  proof (rule eq_from_separatingI2x[where x=t, OF separating_set_bounded_clinear_tc_tensor])
    show \<open>bounded_clinear partial_trace\<close>
      by simp
    show \<open>bounded_clinear
     (\<lambda>t. kf_apply (kf_of_op (tensor_ell2_right (ket ())*))
           (kf_apply (kf_tensor kf_id (kf_trace (range ket))) t))\<close>
      by (intro bounded_linear_intros)
    fix \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('b ell2, 'b ell2) trace_class\<close>
    have \<open>trace (from_trace_class \<sigma>) *\<^sub>C from_trace_class \<rho> =
      tensor_ell2_right (ket ())* o\<^sub>C\<^sub>L from_trace_class \<rho> \<otimes>\<^sub>o of_complex (trace (from_trace_class \<sigma>)) o\<^sub>C\<^sub>L tensor_ell2_right (ket ())\<close>
      by (auto intro!: cblinfun_eqI simp: tensor_op_ell2 ket_CARD_1_is_1)
    then show \<open>partial_trace (tc_tensor \<rho> \<sigma>) =
           kf_apply (kf_of_op (tensor_ell2_right (ket ())*))
            (kf_apply (kf_tensor kf_id (kf_trace (range ket))) (tc_tensor \<rho> \<sigma>))\<close>
      by (auto intro!: from_trace_class_inject[THEN iffD1]
          simp: partial_trace_tensor kf_apply_tensor kf_trace_is_trace kf_of_op_apply
          from_trace_class_sandwich_tc sandwich_apply trace_tc.rep_eq tc_tensor.rep_eq scaleC_trace_class.rep_eq)
  qed
  then show ?thesis
    by (simp add: kf_partial_trace_right_def kf_comp_apply)
qed

lemma partial_trace_ignores_kraus_family:
  assumes \<open>kf_trace_preserving \<EE>\<close>
  shows \<open>partial_trace (kf_tensor \<FF> \<EE> *\<^sub>k\<^sub>r \<rho>) = \<FF> *\<^sub>k\<^sub>r partial_trace \<rho>\<close>
proof (rule eq_from_separatingI2x[where x=\<rho>, OF separating_set_bounded_clinear_tc_tensor])
  show \<open>bounded_clinear (\<lambda>a. partial_trace (kf_tensor \<FF> \<EE> *\<^sub>k\<^sub>r a))\<close>
    by (intro bounded_linear_intros)
  show \<open>bounded_clinear (\<lambda>a. \<FF> *\<^sub>k\<^sub>r partial_trace a)\<close>
    by (intro bounded_linear_intros)
  fix \<rho> :: \<open>('e ell2, 'e ell2) trace_class\<close> and \<sigma> :: \<open>('a ell2, 'a ell2) trace_class\<close>
  from assms
  show \<open>partial_trace (kf_tensor \<FF> \<EE> *\<^sub>k\<^sub>r tc_tensor \<rho> \<sigma>) =
           \<FF> *\<^sub>k\<^sub>r partial_trace (tc_tensor \<rho> \<sigma>)\<close>
    by (simp add: kf_apply_tensor partial_trace_tensor kf_trace_preserving_def kf_apply_scaleC)
qed

lemma kf_partial_trace_bound[simp]:
  shows \<open>kf_bound kf_partial_trace_right = id_cblinfun\<close>
  by (simp add: kf_partial_trace_right_def kf_map_bound
      unitary_tensor_ell2_right_CARD_1 kf_bound_comp_iso kf_bound_tensor
      kf_trace_bound)

lemma kf_partial_trace_norm[simp]:
  shows \<open>kf_norm kf_partial_trace_right = 1\<close>
  by (simp add: kf_norm_def)

lemma kf_partial_trace_right_apply_singleton:
    \<open>kf_partial_trace_right *\<^sub>k\<^sub>r @{x} \<rho> = sandwich_tc (tensor_ell2_right (ket x)*) \<rho>\<close>
proof -
  have \<open>kf_partial_trace_right *\<^sub>k\<^sub>r @{x} (tc_tensor (tc_butterfly (ket a) (ket b)) (tc_butterfly (ket c) (ket d))) =
       sandwich_tc (tensor_ell2_right (ket x)*) (tc_tensor (tc_butterfly (ket a) (ket b)) (tc_butterfly (ket c) (ket d)))\<close> for a b :: 'a and c d :: 'b
  proof -
    have aux1: \<open>(\<lambda>xa. (case xa of (x, xa) \<Rightarrow> (case x of (uu_, b) \<Rightarrow> \<lambda>_. inv ket b) xa) \<in> {x}) = (\<lambda>(e,f). True \<and> inv ket (snd e) = x)\<close>
      by auto
    have aux2: \<open>(\<lambda>e. inv ket (snd e) = x) = (\<lambda>(a,b). True \<and> inv ket b = x)\<close>
      by auto
    have \<open>kf_partial_trace_right *\<^sub>k\<^sub>r @{x} (tc_tensor (tc_butterfly (ket a) (ket b)) (tc_butterfly (ket c) (ket d))) =
       sandwich_tc (tensor_ell2_right (ket ())*)
        (tc_tensor (tc_butterfly (ket a) (ket b)) (kf_apply (kf_filter (\<lambda>b. inv ket b = x) (kf_trace (range ket))) (tc_butterfly (ket c) (ket d))))\<close>
      by (auto simp only: kf_apply_on_def kf_partial_trace_right_def
          kf_filter_map aux1 kf_filter_comp kf_of_op_apply
          kf_filter_true kf_filter_tensor aux2 kf_apply_map
          kf_comp_apply o_def kf_apply_tensor kf_id_apply)
    also have \<open>\<dots> = sandwich_tc (tensor_ell2_right (ket ())*) (tc_tensor (tc_butterfly (ket a) (ket b)) (of_bool (x=c \<and> x=d) *\<^sub>R tc_butterfly (ket ()) (ket ())))\<close>
    proof (rule arg_cong[where f=\<open>\<lambda>x. sandwich_tc _ (tc_tensor _ x)\<close>])
      have \<open>kf_apply (kf_filter (\<lambda>b. inv ket b = x) (kf_trace (range ket))) (tc_butterfly (ket c) (ket d))
         = sandwich_tc (vector_to_cblinfun (ket x)*) (tc_butterfly (ket c) (ket d))\<close>
        apply (transfer' fixing: x)
        apply (subst infsum_single[where i=\<open>((vector_to_cblinfun (ket x))*, ket x)\<close>])
        by auto
      also have \<open>\<dots> = of_bool (x=c \<and> x=d) *\<^sub>R tc_butterfly (ket ()) (ket ())\<close>
        by (auto simp add: sandwich_tc_butterfly ket_CARD_1_is_1 cinner_ket)
      finally show \<open>kf_apply (kf_filter (\<lambda>b. inv ket b = x) (kf_trace (range ket))) (tc_butterfly (ket c) (ket d))
           = of_bool (x=c \<and> x=d) *\<^sub>R tc_butterfly (ket ()) (ket ())\<close>
        by -
    qed
    also have \<open>\<dots> = sandwich_tc (tensor_ell2_right (ket x)*) (tc_tensor (tc_butterfly (ket a) (ket b)) (tc_butterfly (ket c) (ket d)))\<close>
      by (auto simp: tensor_tc_butterfly sandwich_tc_butterfly)
    finally show ?thesis
      by -
  qed
  then show ?thesis
    apply (rule_tac eq_from_separatingI2x[where x=\<rho>])
       apply (rule separating_set_bounded_clinear_tc_tensor_nested)
        apply (rule separating_set_tc_butterfly_nested)
         apply (rule separating_set_ket)
        apply (rule separating_set_ket)
       apply (rule separating_set_tc_butterfly_nested)
        apply (rule separating_set_ket)
       apply (rule separating_set_ket)
    by (auto intro!: kf_apply_on_bounded_clinear bounded_clinear_sandwich_tc separating_set_tc_butterfly_nested simp: )
qed

lemma kf_partial_trace_left_apply_singleton:
  \<open>kf_partial_trace_left *\<^sub>k\<^sub>r @{x} \<rho> = sandwich_tc (tensor_ell2_left (ket x)*) \<rho>\<close>
proof -
  have aux1: \<open>(\<lambda>xa. snd xa = x) = (\<lambda>(e,f). f=x \<and> True)\<close>
    by auto
  have aux2: \<open>(\<lambda>xa. xa \<in> {x}) = (\<lambda>xa. xa = x)\<close>
    by auto
  have inj_snd: \<open>inj_on (snd :: unit\<times>'b \<Rightarrow> 'b) X\<close> for X
    by (auto intro!: inj_onI)
  have aux3: \<open>tensor_ell2_right (ket x)* *\<^sub>V ket (b, a) = of_bool (x=a) *\<^sub>R ket b\<close> for x a :: 'x and b :: 'y
    by (smt (verit) cinner_ket_same of_bool_eq(1) of_bool_eq(2) of_real_1 of_real_hom.hom_0_iff orthogonal_ket scaleR_scaleC tensor_ell2_ket tensor_ell2_right_adj_apply)
  have aux4: \<open>tensor_ell2_left (ket x)* *\<^sub>V ket (a, b) = of_bool (x=a) *\<^sub>R ket b\<close> for x a :: 'x and b :: 'y
    by (smt (verit, del_insts) cinner_ket_same of_bool_eq(1) of_bool_eq(2) of_real_1 of_real_hom.hom_0_iff orthogonal_ket scaleR_scaleC tensor_ell2_ket tensor_ell2_left_adj_apply)
  have aux5: \<open>tensor_ell2_right (ket x)* o\<^sub>C\<^sub>L swap_ell2 = tensor_ell2_left (ket x)*\<close>
    apply (rule equal_ket)
    by (auto intro!: simp: aux3 aux4)
  have \<open>kf_partial_trace_left *\<^sub>k\<^sub>r @{x} \<rho>
     = kf_partial_trace_right *\<^sub>k\<^sub>r @{x} (sandwich_tc swap_ell2 \<rho>)\<close>
    by (simp only: kf_partial_trace_left_def kf_apply_on_def kf_filter_map_inj
        aux1 kf_filter_comp kf_apply_map_inj inj_snd kf_filter_true
        kf_comp_apply o_def kf_of_op_apply aux2)
  also have \<open>\<dots> = sandwich_tc (tensor_ell2_left (ket x)*) \<rho>\<close>
    by (auto intro!: arg_cong[where f=\<open>\<lambda>x. sandwich_tc x _\<close>]
        simp: kf_partial_trace_right_apply_singleton aux5
        simp flip: sandwich_tc_compose[unfolded o_def, THEN fun_cong])
  finally show ?thesis
    by -
qed

lemma kf_domain_partial_trace_right[simp]: \<open>kf_domain kf_partial_trace_right = UNIV\<close>
proof (intro Set.set_eqI iffI UNIV_I)
  fix x :: 'a and y :: 'b

  have \<open>kf_partial_trace_right *\<^sub>k\<^sub>r @{x} (tc_tensor (tc_butterfly (ket y) (ket y)) (tc_butterfly (ket x) (ket x)))
      = tc_butterfly (ket y) (ket y)\<close>
    by (simp add: kf_partial_trace_right_apply_singleton tensor_tc_butterfly sandwich_tc_butterfly)
  also have \<open>\<dots> \<noteq> 0\<close>
  proof -
    have \<open>norm (tc_butterfly (ket y) (ket y)) = 1\<close>
      by (simp add: norm_tc_butterfly)
    then show ?thesis
      by auto
  qed
 finally have \<open>kf_apply_on (kf_partial_trace_right :: (('b\<times>'a) ell2, 'b ell2, 'a) kraus_family) {x} \<noteq> 0\<close>
    by auto
  then show \<open>x \<in> kf_domain (kf_partial_trace_right :: (('b\<times>'a) ell2, 'b ell2, 'a) kraus_family)\<close>
    by (rule in_kf_domain_iff_apply_nonzero[THEN iffD2])
qed


lemma kf_domain_partial_trace_left[simp]: \<open>kf_domain kf_partial_trace_left = UNIV\<close>
proof (intro Set.set_eqI iffI UNIV_I)
  fix x :: 'a and y :: 'b

  have \<open>kf_partial_trace_left *\<^sub>k\<^sub>r @{x} (tc_tensor (tc_butterfly (ket x) (ket x)) (tc_butterfly (ket y) (ket y)))
      = tc_butterfly (ket y) (ket y)\<close>
    by (simp add: kf_partial_trace_left_apply_singleton tensor_tc_butterfly sandwich_tc_butterfly)
  also have \<open>\<dots> \<noteq> 0\<close>
  proof -
    have \<open>norm (tc_butterfly (ket y) (ket y)) = 1\<close>
      by (simp add: norm_tc_butterfly)
    then show ?thesis
      by auto
  qed
 finally have \<open>kf_apply_on (kf_partial_trace_left :: (('a\<times>'b) ell2, 'b ell2, 'a) kraus_family) {x} \<noteq> 0\<close>
    by auto
  then show \<open>x \<in> kf_domain (kf_partial_trace_left :: (('a\<times>'b) ell2, 'b ell2, 'a) kraus_family)\<close>
    by (rule in_kf_domain_iff_apply_nonzero[THEN iffD2])
qed


subsection \<open>Complete measurement\<close>

lemma complete_measurement_aux:
  fixes B and F :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a \<times> 'a) set\<close>
  defines \<open>family \<equiv> (\<lambda>x. (selfbutter (sgn x), x)) ` B\<close>
  assumes \<open>finite F\<close> and FB: \<open>F \<subseteq> family\<close> and \<open>is_ortho_set B\<close>
  shows \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> id_cblinfun\<close>
proof -
  obtain G where \<open>finite G\<close> and \<open>G \<subseteq> B\<close> and FG: \<open>F = (\<lambda>x. (selfbutter (sgn x), x)) ` G\<close>
    apply atomize_elim
    using \<open>finite F\<close> and FB
    apply (simp add: family_def)
    by (meson finite_subset_image)
  from \<open>G \<subseteq> B\<close> have [simp]: \<open>is_ortho_set G\<close>
    by (simp add: \<open>is_ortho_set B\<close> is_ortho_set_antimono)
  then have [simp]: \<open>e \<in> G \<Longrightarrow> norm (sgn e) = 1\<close> for e
    apply (simp add: is_ortho_set_def)
    by (metis norm_sgn)
  have [simp]: \<open>inj_on (\<lambda>x. (selfbutter (sgn x), x)) G\<close>
    by (meson inj_onI prod.inject)
  have [simp]: \<open>inj_on sgn G\<close>
  proof (rule inj_onI, rule ccontr)
    fix x y assume \<open>x \<in> G\<close> and \<open>y \<in> G\<close> and sgn_eq: \<open>sgn x = sgn y\<close> and \<open>x \<noteq> y\<close>
    with \<open>is_ortho_set G\<close> have \<open>is_orthogonal x y\<close>
      by (meson is_ortho_set_def)
    then have \<open>is_orthogonal (sgn x) (sgn y)\<close>
      by fastforce
    with sgn_eq have \<open>sgn x = 0\<close>
      by force
    with \<open>x \<in> G\<close> \<open>is_ortho_set G\<close> show False
      by (metis \<open>x \<noteq> y\<close> local.sgn_eq sgn_zero_iff)
  qed
  have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>G. selfbutter (sgn x))\<close>
    by (simp add: FG sum.reindex cdot_square_norm)
  also 
  have \<open>(\<Sum>x\<in>G. selfbutter (sgn x)) \<le> id_cblinfun\<close>
    apply (subst sum.reindex[where h=sgn, unfolded o_def, symmetric])
     apply simp
    apply (subgoal_tac \<open>\<And>x y. \<forall>x\<in>G. \<forall>y\<in>G. x \<noteq> y \<longrightarrow> is_orthogonal x y \<Longrightarrow>
           0 \<notin> G \<Longrightarrow> x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> sgn x \<noteq> sgn y \<Longrightarrow> is_orthogonal x y\<close>)
    using \<open>is_ortho_set G\<close>
     apply (auto intro!: sum_butterfly_leq_id simp: is_ortho_set_def sgn_zero_iff)[1]
    by fast
  finally show ?thesis
    by -
qed

lemma complete_measurement_is_kraus_family:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kraus_family ((\<lambda>x. (selfbutter (sgn x), x)) ` B)\<close>
proof (rule kraus_familyI)
  show \<open>bdd_above (sum (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> (\<lambda>x. (selfbutter (sgn x), x)) ` B})\<close>
    using complete_measurement_aux[OF _ _ assms]
    by (auto intro!: bdd_aboveI[where M=id_cblinfun] kraus_familyI)
  have \<open>selfbutter (sgn x) = 0 \<Longrightarrow> x = 0\<close> for x
    by (smt (verit, best) mult_cancel_right1 norm_butterfly norm_sgn norm_zero)
  then show \<open>0 \<notin> fst ` (\<lambda>x. (selfbutter (sgn x), x)) ` B\<close>
    using assms by (force simp: is_ortho_set_def)
qed

lift_definition kf_complete_measurement :: \<open>'a set \<Rightarrow> ('a::chilbert_space, 'a, 'a) kraus_family\<close> is
  \<open>\<lambda>B. if is_ortho_set B then (\<lambda>x. (selfbutter (sgn x), x)) ` B else {}\<close>
  by (auto intro!: complete_measurement_is_kraus_family)

definition kf_complete_measurement_ket :: \<open>('a ell2, 'a ell2, 'a) kraus_family\<close> where
  \<open>kf_complete_measurement_ket = kf_map_inj (inv ket) (kf_complete_measurement (range ket))\<close>

lemma kf_complete_measurement_domain[simp]:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kf_domain (kf_complete_measurement B) = B\<close>
  apply (transfer fixing: B)
  using assms by (auto simp: image_image)

lemma kf_complete_measurement_ket_domain[simp]:
  \<open>kf_domain kf_complete_measurement_ket = UNIV\<close>
  by (simp add: kf_complete_measurement_ket_def)

lemma kf_complete_measurement_ket_kf_map:
  \<open>kf_complete_measurement_ket \<equiv>\<^sub>k\<^sub>r kf_map (inv ket) (kf_complete_measurement (range ket))\<close>
  unfolding kf_complete_measurement_ket_def
  apply (rule kf_map_inj_eq_kf_map)
  using inj_on_inv_into by fastforce+



lemma kf_bound_complete_measurement:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kf_bound (kf_complete_measurement B) \<le> id_cblinfun\<close>
  apply (rule kf_bound_leqI)
  by (simp add: assms complete_measurement_aux kf_complete_measurement.rep_eq)

lemma kf_norm_complete_measurement:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kf_norm (kf_complete_measurement B) \<le> 1\<close>
  by (smt (verit, ccfv_SIG) assms kf_norm_def kf_bound_complete_measurement kf_bound_pos norm_cblinfun_id_le norm_cblinfun_mono)

lemma kf_complete_measurement_invalid:
  assumes \<open>\<not> is_ortho_set B\<close>
  shows \<open>kf_complete_measurement B = 0\<close>
  apply (transfer' fixing: B)
  using assms by simp

lemma kf_complete_measurement_idem:
  \<open>kf_comp (kf_complete_measurement B) (kf_complete_measurement B)
      \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>b. (b,b)) (kf_complete_measurement B)\<close>
proof -
  wlog [iff]: \<open>is_ortho_set B\<close>
    using negation 
    by (simp add: kf_complete_measurement_invalid)
  define f where \<open>f b = (selfbutter (sgn b), selfbutter (sgn b), b, b)\<close> for b :: 'a
  have b2: \<open>sgn b \<bullet>\<^sub>C sgn b = 1\<close> if \<open>b \<in> B\<close> for b
    by (metis \<open>b \<in> B\<close> \<open>is_ortho_set B\<close> cnorm_eq_1 is_ortho_set_def norm_sgn)
  have 1: \<open>(E o\<^sub>C\<^sub>L F, F, E, b, c) \<in> (\<lambda>x. (selfbutter (sgn x), f x)) ` B\<close>
    if \<open>E o\<^sub>C\<^sub>L F \<noteq> 0\<close> and \<open>(F, b) \<in> Rep_kraus_family (kf_complete_measurement B)\<close> and \<open>(E, c) \<in> Rep_kraus_family (kf_complete_measurement B)\<close>
    for E F b c
  proof -
    from that have \<open>b \<in> B\<close> and \<open>c \<in> B\<close> and E_def: \<open>E = selfbutter (sgn c)\<close> and F_def: \<open>F = selfbutter (sgn b)\<close>
      by (auto simp add: kf_complete_measurement.rep_eq)
    have \<open>E o\<^sub>C\<^sub>L F = (sgn c \<bullet>\<^sub>C sgn b) *\<^sub>C butterfly (sgn c) (sgn b)\<close>
      by (simp add: E_def F_def)
    with that have \<open>c \<bullet>\<^sub>C b \<noteq> 0\<close>
      by fastforce
    with \<open>b \<in> B\<close> \<open>c \<in> B\<close> \<open>is_ortho_set B\<close>
    have \<open>c = b\<close>
      using is_ortho_setD by blast
    then have \<open>(E o\<^sub>C\<^sub>L F, F, E, b, c) = (\<lambda>x. (selfbutter (sgn x), f x)) c\<close>
      by (simp add: b2 \<open>b \<in> B\<close> f_def E_def F_def)
    with \<open>c \<in> B\<close> show ?thesis
      by blast
  qed
  have 2: \<open>x \<in> B \<Longrightarrow> selfbutter (sgn x) \<noteq> 0\<close> for x
    by (smt (verit) \<open>is_ortho_set B\<close> inverse_1 is_ortho_set_def norm_butterfly norm_sgn norm_zero right_inverse)
  have 3: \<open>(selfbutter (sgn x), f x) \<in> (\<lambda>((F,y),(E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
          (Rep_kraus_family (kf_complete_measurement B) \<times> Rep_kraus_family (kf_complete_measurement B))\<close>
    if \<open>x \<in> B\<close> and \<open>(E, F, c, b) = f x\<close>
    for E F c b x
    apply (rule image_eqI[where x=\<open>((selfbutter (sgn x),x),(selfbutter (sgn x),x))\<close>])
    by (auto intro!: simp: b2 that f_def kf_complete_measurement.rep_eq)
  have raw: \<open>(kf_comp_dependent_raw (\<lambda>_. kf_complete_measurement B) (kf_complete_measurement B))
      = kf_map_inj f (kf_complete_measurement B)\<close>
    apply (transfer' fixing: f B)
    using 1 2 3
    by (auto simp: image_image case_prod_unfold)
  have \<open>kf_comp (kf_complete_measurement B) (kf_complete_measurement B)
     \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(F, E, y). y) ((kf_comp_dependent_raw (\<lambda>_. kf_complete_measurement B) (kf_complete_measurement B)))\<close>
    by (simp add: kf_comp_def kf_comp_dependent_def id_def)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(F, E, y). y) (kf_map_inj f (kf_complete_measurement B))\<close>
    by (simp add: raw)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(F, E, y). y) (kf_map f (kf_complete_measurement B))\<close>
    by (auto intro!: kf_map_cong kf_map_inj_eq_kf_map inj_onI simp: f_def)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>b. (b, b)) (kf_complete_measurement B)\<close>
    apply (rule kf_map_twice[THEN kf_eq_trans])
    by (simp add: f_def o_def)
  finally show ?thesis
    by -
qed

lemma kf_complete_measurement_idem_weak:
  \<open>kf_comp (kf_complete_measurement B) (kf_complete_measurement B)
      =\<^sub>k\<^sub>r kf_complete_measurement B\<close>
  by (metis (no_types, lifting) kf_apply_map kf_complete_measurement_idem kf_eq_imp_eq_weak kf_eq_weak_def)

lemma kf_complete_measurement_ket_idem:
  \<open>kf_comp kf_complete_measurement_ket kf_complete_measurement_ket
      \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>b. (b,b)) kf_complete_measurement_ket\<close>
proof -
  have \<open>kf_comp kf_complete_measurement_ket kf_complete_measurement_ket
    \<equiv>\<^sub>k\<^sub>r kf_comp (kf_map (inv ket) (kf_complete_measurement (range ket))) (kf_map (inv ket) (kf_complete_measurement (range ket)))\<close>
    by (intro kf_comp_cong kf_complete_measurement_ket_kf_map)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x, y). (x, inv ket y))
     (kf_map (\<lambda>(x, y). (inv ket x, y)) (kf_comp (kf_complete_measurement (range ket)) (kf_complete_measurement (range ket))))\<close>
    by (intro kf_comp_map_left[THEN kf_eq_trans] kf_map_cong kf_comp_map_right refl)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>(x, y). (x, inv ket y))
     (kf_map (\<lambda>(x, y). (inv ket x, y)) (kf_map (\<lambda>b. (b, b)) (kf_complete_measurement (range ket))))\<close>
    by (intro kf_map_cong kf_complete_measurement_idem refl)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>x. (inv ket x, inv ket x)) (kf_complete_measurement (range ket))\<close>
    apply (intro kf_map_twice[THEN kf_eq_trans])
    by (simp add: o_def)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>b. (b, b)) (kf_map (inv ket) (kf_complete_measurement (range ket)))\<close>
    apply (rule kf_eq_sym)
    apply (rule kf_map_twice[THEN kf_eq_trans])
    by (simp add: o_def)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>b. (b, b)) kf_complete_measurement_ket\<close>
    using kf_complete_measurement_ket_kf_map kf_eq_sym kf_map_cong by fastforce
  finally show ?thesis
    by -
qed

lemma kf_complete_measurement_ket_idem_weak:
  \<open>kf_comp kf_complete_measurement_ket kf_complete_measurement_ket
      =\<^sub>k\<^sub>r kf_complete_measurement_ket\<close>
  by (metis (no_types, lifting) kf_apply_map kf_complete_measurement_ket_idem kf_eq_imp_eq_weak kf_eq_weak_def)

(* lemma kf_complete_measurement_ket_idem[simp]:
  \<open>kf_complete_measurement_ket *\<^sub>k\<^sub>r kf_complete_measurement_ket *\<^sub>k\<^sub>r \<rho>
      = kf_complete_measurement_ket *\<^sub>k\<^sub>r \<rho>\<close>
try0
sledgehammer [dont_slice]
by -

  by (metis kf_apply_map kf_apply_on_UNIV kf_apply_on_eqI kf_complete_measurement_idem kf_complete_measurement_ket_kf_map) *)

lemma kf_complete_measurement_apply:
  assumes [simp]: \<open>is_ortho_set B\<close>
  shows \<open>kf_complete_measurement B *\<^sub>k\<^sub>r t = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) t)\<close>
proof -
  have \<open>kf_complete_measurement B *\<^sub>k\<^sub>r t = 
      (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) t)\<close>
    apply (transfer' fixing: B t)
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) t)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def)
  finally show ?thesis
    by -
qed

lemma kf_complete_measurement_has_sum:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>((\<lambda>x. sandwich_tc (selfbutter (sgn x)) \<rho>) has_sum kf_complete_measurement B *\<^sub>k\<^sub>r \<rho>) B\<close>
  using kf_apply_has_sum[of _ \<open>kf_complete_measurement B\<close>] assms
  by (simp add: kf_complete_measurement_apply kf_complete_measurement.rep_eq
      has_sum_reindex inj_on_def o_def)

lemma kf_complete_measurement_has_sum_onb:
  assumes \<open>is_onb B\<close>
  shows \<open>((\<lambda>x. sandwich_tc (selfbutter x) \<rho>) has_sum kf_complete_measurement B *\<^sub>k\<^sub>r \<rho>) B\<close>
proof -
  have \<open>is_ortho_set B\<close>
    using assms by (simp add: is_onb_def)
  have sgnx: \<open>sgn x = x\<close> if \<open>x \<in> B\<close> for x
    using assms that
    by (simp add: is_onb_def sgn_div_norm)
  from kf_complete_measurement_has_sum[OF \<open>is_ortho_set B\<close>]
  show ?thesis
    apply (rule has_sum_cong[THEN iffD1, rotated])
    by (simp add: sgnx)
qed

lemma kf_complete_measurement_ket_has_sum:
   \<open>((\<lambda>x. sandwich_tc (selfbutter (ket x)) \<rho>) has_sum kf_complete_measurement_ket *\<^sub>k\<^sub>r \<rho>) UNIV\<close>
proof -
  from kf_complete_measurement_has_sum_onb
  have \<open>((\<lambda>x. sandwich_tc (selfbutter x) \<rho>) has_sum kf_complete_measurement (range ket) *\<^sub>k\<^sub>r \<rho>) (range ket)\<close>
    by force
  then have \<open>((\<lambda>x. sandwich_tc (selfbutter (ket x)) \<rho>) has_sum kf_complete_measurement (range ket) *\<^sub>k\<^sub>r \<rho>) UNIV\<close>
    apply (subst (asm) has_sum_reindex)
    by (simp_all add: o_def)
  then have \<open>((\<lambda>x. sandwich_tc (selfbutter (ket x)) \<rho>) has_sum kf_map (inv ket) (kf_complete_measurement (range ket)) *\<^sub>k\<^sub>r \<rho>) UNIV\<close>
    by simp
  then show ?thesis
    by (metis (no_types, lifting) kf_apply_on_UNIV kf_apply_on_eqI kf_complete_measurement_ket_kf_map)
qed

lemma kf_complete_measurement_apply_onb:
  assumes \<open>is_onb B\<close>
  shows \<open>kf_complete_measurement B *\<^sub>k\<^sub>r t = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter x) t)\<close>
  using kf_complete_measurement_has_sum_onb[OF assms]
  by (metis (lifting) infsumI)

lemma kf_complete_measurement_ket_apply: \<open>kf_complete_measurement_ket *\<^sub>k\<^sub>r t = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) t)\<close>
proof -
  have \<open>kf_complete_measurement_ket *\<^sub>k\<^sub>r t = kf_complete_measurement (range ket) *\<^sub>k\<^sub>r t\<close>
    by (metis kf_apply_map kf_apply_on_UNIV kf_apply_on_eqI kf_complete_measurement_ket_kf_map)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>range ket. sandwich_tc (selfbutter x) t)\<close>
    by (simp add: kf_complete_measurement_apply_onb)
  also have \<open>\<dots>  = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) t)\<close>
    by (simp add: infsum_reindex o_def)
  finally show ?thesis
    by -
qed


lemma kf_bound_complete_measurement_onb[simp]:
  assumes \<open>is_onb B\<close>
  shows \<open>kf_bound (kf_complete_measurement B) = id_cblinfun\<close>
proof (rule cblinfun_eq_gen_eqI[where G=B], rule cinner_extensionality_basis[where B=B])
  show \<open>ccspan B = \<top>\<close>
    using assms is_onb_def by blast
  then show \<open>ccspan B = \<top>\<close>
    by -
  fix x y assume \<open>x \<in> B\<close> and \<open>y \<in> B\<close>
  have aux1: \<open>j \<noteq> x \<Longrightarrow> j \<in> B \<Longrightarrow> sandwich_tc (selfbutter j) (tc_butterfly y x) = 0\<close> for j
    apply (transfer' fixing: x B j y)
    by (smt (z3) \<open>x \<in> B\<close> apply_id_cblinfun assms butterfly_0_right butterfly_adjoint butterfly_def cblinfun_apply_cblinfun_compose
        cblinfun_comp_butterfly is_onb_def is_ortho_setD of_complex_eq_id sandwich_apply vector_to_cblinfun_adj_apply)
  have aux2: \<open>trace_tc (sandwich_tc (selfbutter y) (tc_butterfly y y)) = 1\<close>
    apply (transfer' fixing: y)
    by (metis (no_types, lifting) ext \<open>y \<in> B\<close> assms butterfly_adjoint butterfly_comp_butterfly cblinfun_comp_butterfly cinner_simps(6)
        is_onb_def norm_one one_cinner_a_scaleC_one one_cinner_one sandwich_apply selfbutter_pos trace_butterfly trace_norm_butterfly
        trace_norm_pos trace_scaleC)
  have aux3: \<open>x \<noteq> y \<Longrightarrow> trace_tc (sandwich_tc (selfbutter x) (tc_butterfly y x)) = 0\<close>
    apply (transfer' fixing: x y)
    by (metis (no_types, lifting) ext Trace_Class.trace_0 \<open>x \<in> B\<close> \<open>y \<in> B\<close> apply_id_cblinfun assms butterfly_0_left butterfly_def
        cblinfun.zero_right cblinfun_apply_cblinfun_compose cblinfun_comp_butterfly is_onb_def is_ortho_setD of_complex_eq_id
        sandwich_apply vector_to_cblinfun_adj_apply)

  have \<open>x \<bullet>\<^sub>C (kf_bound (kf_complete_measurement B) *\<^sub>V y) = trace_tc (kf_complete_measurement B *\<^sub>k\<^sub>r tc_butterfly y x)\<close>
    by (simp add: kf_bound_from_map)
  also have \<open>\<dots> = trace_tc (\<Sum>\<^sub>\<infinity>xa\<in>B. sandwich_tc (selfbutter xa) (tc_butterfly y x))\<close>
    by (simp add: kf_complete_measurement_apply_onb assms)
  also have \<open>\<dots> = trace_tc (if x \<in> B then sandwich_tc (selfbutter x) (tc_butterfly y x) else 0)\<close>
    apply (subst infsum_single[where i=x])
    using aux1 by auto
  also have \<open>\<dots> = of_bool (x = y)\<close>
    using \<open>y \<in> B\<close> aux2 aux3 by (auto intro!: simp: )
  also have \<open>\<dots> = x \<bullet>\<^sub>C (id_cblinfun *\<^sub>V y)\<close>
    using \<open>x \<in> B\<close> \<open>y \<in> B\<close> assms cnorm_eq_1 is_onb_def is_ortho_setD by fastforce
  finally show \<open>x \<bullet>\<^sub>C (kf_bound (kf_complete_measurement B) *\<^sub>V y) = x \<bullet>\<^sub>C (id_cblinfun *\<^sub>V y)\<close>
    by -
qed

lemma kf_bound_complete_measurement_ket[simp]:
  \<open>kf_bound kf_complete_measurement_ket = id_cblinfun\<close>
  by (metis is_onb_ket kf_bound_complete_measurement_onb kf_bound_cong kf_complete_measurement_ket_kf_map kf_eq_imp_eq_weak
      kf_map_bound)

lemma kf_norm_complete_measurement_onb[simp]:
  fixes B :: \<open>'a::{not_singleton, chilbert_space} set\<close>
  assumes \<open>is_onb B\<close>
  shows \<open>kf_norm (kf_complete_measurement B) = 1\<close>
  by (simp add: kf_norm_def assms)

lemma kf_norm_complete_measurement_ket[simp]:
  \<open>kf_norm kf_complete_measurement_ket = 1\<close>
  by (simp add: kf_norm_def)


lemma kf_complete_measurement_ket_diagonal_operator[simp]:
  \<open>kf_complete_measurement_ket *\<^sub>k\<^sub>r diagonal_operator_tc f = diagonal_operator_tc f\<close>
proof (cases \<open>f abs_summable_on UNIV\<close>)
  case True
  have \<open>kf_complete_measurement_ket *\<^sub>k\<^sub>r diagonal_operator_tc f = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) (diagonal_operator_tc f))\<close>
    by (simp add: kf_complete_measurement_ket_apply)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) (\<Sum>\<^sub>\<infinity>y. f y *\<^sub>C tc_butterfly (ket y) (ket y)))\<close>
    by (simp add: flip: tc_butterfly_scaleC_infsum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. sandwich_tc (selfbutter (ket x)) (f y *\<^sub>C tc_butterfly (ket y) (ket y)))\<close>
    apply (rule infsum_cong)
    apply (rule infsum_bounded_linear[unfolded o_def, symmetric])
    by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_sandwich_tc tc_butterfly_scaleC_summable True)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. of_bool (y=x) *\<^sub>C f x *\<^sub>C tc_butterfly (ket x) (ket x))\<close>
    apply (rule infsum_cong)+
    apply (transfer' fixing: f)
    by (simp add: sandwich_apply)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x))\<close>
    apply (subst infsum_of_bool_scaleC)
    by simp
  also have \<open>\<dots> = diagonal_operator_tc f\<close>
    by (simp add: flip: tc_butterfly_scaleC_infsum)
  finally show ?thesis
    by -
next
  case False
  then have \<open>diagonal_operator_tc f = 0\<close>
    by (rule diagonal_operator_tc_invalid)
  then show ?thesis
    by simp
qed

lemma kf_operators_complete_measurement:
  \<open>kf_operators (kf_complete_measurement B) = (selfbutter o sgn) ` B\<close> if \<open>is_ortho_set B\<close>
  apply (transfer' fixing: B)
  using that by force

lemma kf_operators_complete_measurement_invalid:
  \<open>kf_operators (kf_complete_measurement B) = {}\<close> if \<open>\<not> is_ortho_set B\<close>
  apply (transfer' fixing: B)
  using that by force

lemma kf_operators_complete_measurement_ket:
  \<open>kf_operators kf_complete_measurement_ket = range (\<lambda>c. butterfly (ket c) (ket c))\<close>
  by (simp add: kf_complete_measurement_ket_def kf_operators_complete_measurement image_image)

lemma kf_complete_measurement_apply_butterfly:
  assumes \<open>is_ortho_set B\<close> and \<open>b \<in> B\<close>
  shows \<open>kf_complete_measurement B *\<^sub>k\<^sub>r tc_butterfly b b = tc_butterfly b b\<close>
proof -
  have \<open>kf_complete_measurement B *\<^sub>k\<^sub>r tc_butterfly b b = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) (tc_butterfly b b))\<close>
    by (simp add: kf_complete_measurement_apply assms)
  also have \<open>\<dots> = (if b \<in> B then sandwich_tc (selfbutter (sgn b)) (tc_butterfly b b) else 0)\<close>
  proof (rule infsum_single[where i=b])
    fix c assume \<open>c \<in> B\<close> and \<open>c \<noteq> b\<close>
    then have [iff]: \<open>c \<bullet>\<^sub>C b = 0\<close>
      using assms(1,2) is_ortho_setD by blast
    then have [iff]: \<open>sgn c \<bullet>\<^sub>C b = 0\<close>
      by auto
    then
    show \<open>sandwich_tc (selfbutter (sgn c)) (tc_butterfly b b) = 0\<close>
      by (auto intro!: simp: sandwich_tc_butterfly)
  qed
  also have \<open>\<dots> = tc_butterfly b b\<close>
    by (simp add: \<open>b \<in> B\<close> sandwich_tc_butterfly)
  finally show ?thesis
    by -
qed

lemma kf_complete_measurement_ket_apply_butterfly:
  \<open>kf_complete_measurement_ket *\<^sub>k\<^sub>r tc_butterfly (ket x) (ket x) = tc_butterfly (ket x) (ket x)\<close>
  by (simp add: kf_complete_measurement_ket_def kf_apply_map_inj inj_on_def kf_complete_measurement_apply_butterfly)


(* lemma kf_unique_if_singleton:
  assumes \<open>Rep_kraus_family \<EE> \<subseteq> {Ee}\<close>
  assumes \<open>Rep_kraus_family \<FF> \<subseteq> {Ff}\<close>
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>\<EE> = \<FF>\<close>
(* WRONG! Global phase *)
proof (cases \<open>\<EE> = 0\<close>)
  case True
  with \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close> have \<open>\<FF> = 0\<close>
    using kf_eq_0_iff_eq_0 kf_eq_imp_eq_weak kf_eq_sym by blast
  with True show ?thesis
    by simp
next
  case False
  obtain E e F f where Ee: \<open>Ee = (E,e)\<close> and Ff: \<open>Ff = (F,f)\<close>
    apply atomize_elim
    by (auto split!: prod.split_asm)
  from False have \<open>\<FF> \<noteq> 0\<close>
    using \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close> kf_eq_0_iff_eq_0 kf_eq_imp_eq_weak by blast
  from False have \<open>Rep_kraus_family \<EE> \<noteq> {}\<close>
    using Rep_kraus_family_inject zero_kraus_family.rep_eq by auto
  with assms(1) have Rep\<EE>: \<open>Rep_kraus_family \<EE> = {(E,e)}\<close>
    using Ee by blast
  from \<open>\<FF> \<noteq> 0\<close> have \<open>Rep_kraus_family \<FF> \<noteq> {}\<close>
    using Rep_kraus_family_inject zero_kraus_family.rep_eq by auto
  with assms(2) have Rep\<FF>: \<open>Rep_kraus_family \<FF> = {(F,f)}\<close>
    using Ff by blast
  from Rep\<EE> have \<open>E \<noteq> 0\<close>
    using Rep_kraus_family by (force simp: kraus_family_def)
  from Rep\<FF> have \<open>F \<noteq> 0\<close>
    using Rep_kraus_family by (force simp: kraus_family_def)
  have \<open>E = F\<close>
  proof (rule cblinfun_eqI)
    fix h
    have \<open>tc_butterfly (E h) (E h) = \<EE> *\<^sub>k\<^sub>r tc_butterfly h h\<close>
      by (simp add: kf_apply.rep_eq Rep\<EE> sandwich_tc_butterfly)
    also have \<open>\<dots> = \<FF> *\<^sub>k\<^sub>r tc_butterfly h h\<close>
      by (simp add: assms(3) kf_apply_eqI kf_eq_imp_eq_weak)
    also have \<open>\<dots> = tc_butterfly (F h) (F h)\<close>
      by (simp add: kf_apply.rep_eq Rep\<FF> sandwich_tc_butterfly)
    finally show \<open>E h = F h\<close>
      by (rule tc_selfbutter_inject)
  qed
  have \<open>e = f\<close>
  proof (rule ccontr)
    assume \<open>e \<noteq> f\<close>
    obtain h where neq0: \<open>E h \<noteq> 0\<close>
    proof (atomize_elim, rule ccontr)
      assume \<open>\<nexists>h. E *\<^sub>V h \<noteq> 0\<close>
      then have \<open>E h = 0\<close> for h
        by auto
      then have \<open>E = 0\<close>
        apply (rule_tac cblinfun_eqI)
        by simp
      with \<open>E \<noteq> 0\<close> show False
        by simp
    qed
    have \<open>tc_butterfly (E h) (E h) = \<EE> *\<^sub>k\<^sub>r @{e} tc_butterfly h h\<close>
      by (simp add: kf_apply_on_def kf_filter.rep_eq kf_apply.rep_eq Rep\<EE> sandwich_tc_butterfly filter_insert_if)
  also have \<open>\<dots> = \<FF> *\<^sub>k\<^sub>r @{e} tc_butterfly h h\<close>
  using assms(3) kf_apply_on_eqI by blast
  also from \<open>e \<noteq> f\<close> have \<open>\<dots> = 0\<close>
    by (simp add: kf_apply_on_def kf_filter.rep_eq kf_apply.rep_eq Rep\<FF> sandwich_tc_butterfly filter_insert_if)
  finally have \<open>E h = 0\<close>
    using tc_selfbutter_inject[where k=0]
    by auto
  with neq0 show False
    by simp
  qed
  from \<open>E = F\<close> \<open>e = f\<close> Rep\<EE> Rep\<FF> show \<open>\<EE> = \<FF>\<close>
    using Rep_kraus_family_inject by blast
qed *)



lemma kf_map_eq_kf_map_inj_singleton:
  assumes \<open>card_le_1 (Rep_kraus_family \<EE>)\<close>
  shows \<open>kf_map f \<EE> = kf_map_inj f \<EE>\<close>
proof (cases \<open>\<EE> = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  then have \<open>Rep_kraus_family \<EE> \<noteq> {}\<close>
  using Rep_kraus_family_inject zero_kraus_family.rep_eq by auto
  with assms obtain x where Rep\<EE>: \<open>Rep_kraus_family \<EE> = {x}\<close>
    by (meson card_le_1_def subset_singleton_iff)
  obtain E y where Ey: \<open>x = (E,y)\<close>
    by force
  have \<open>(E,y) \<in> Rep_kraus_family \<EE>\<close>
    using Ey Rep\<EE> by force
  then have [iff]: \<open>E \<noteq> 0\<close>
    using Rep_kraus_family[of \<EE>]
    by (force simp: kraus_family_def)
  have *: \<open>{(F, xa). (F, xa) = x \<and> f xa = f y \<and> (\<exists>r>0. E = r *\<^sub>R F)} = {(E,y)}\<close>
    apply (subgoal_tac \<open>\<exists>r>0. E = r *\<^sub>R E\<close>)
     apply (auto intro!: simp: Ey)[1]
    by (metis scaleR_simps(12) verit_comp_simplify(28))
  have 1: \<open>(norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>x. f x = f y) \<EE>) E\<close>
    by (auto simp add: kf_element_weight_def kf_similar_elements_def kf_filter.rep_eq * Rep\<EE>)
  have 2: \<open>z = f y\<close> if \<open>(norm F)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>x. f x = z) \<EE>) F\<close> and \<open>F \<noteq> 0\<close> for F z
  proof (rule ccontr)
    assume \<open>z \<noteq> f y\<close>
    with Rep\<EE> have \<open>kf_filter (\<lambda>x. f x = z) \<EE> = 0\<close>
      apply (transfer' fixing: f z y x)
      by (auto simp: Ey)
    then have \<open>kf_element_weight (kf_filter (\<lambda>x. f x = z) \<EE>) F = 0\<close>
      by simp
    with that show False
      by fastforce
  qed
  have 3: \<open>F = E\<close> if \<open>(norm F)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>x. f x = z) \<EE>) F\<close> and \<open>F \<noteq> 0\<close> and \<open>z = f y\<close> for F z
  proof -
    from that Rep\<EE> have f\<EE>: \<open>kf_filter (\<lambda>x. f x = z) \<EE> = \<EE>\<close>
      apply (transfer' fixing: F f z y x)
      using Ey Rep_kraus_family_inject kf_filter.rep_eq by fastforce
    have \<open>\<exists>r>0. F = r *\<^sub>R E\<close>
    proof (rule ccontr)
      assume \<open>\<not> (\<exists>r>0. F = r *\<^sub>R E)\<close>
      with Rep\<EE> have \<open>kf_similar_elements \<EE> F = {}\<close>
        by (simp add: kf_similar_elements_def Ey)
      with that f\<EE> show False
        by (simp add: kf_element_weight_def)
    qed
    then obtain r where FrE: \<open>F = r *\<^sub>R E\<close> and rpos: \<open>r > 0\<close>
      by auto
    with Rep\<EE> have \<open>kf_similar_elements \<EE> F = {(E,y)}\<close>
      by (force simp: kf_similar_elements_def Ey)
    then have \<open>kf_element_weight \<EE> F = (norm E)\<^sup>2\<close>
      by (simp add: kf_element_weight_def)
    with that have \<open>norm E = norm F\<close>
      using f\<EE> by force
    with FrE rpos have \<open>r = 1\<close>
      by simp
    with FrE show \<open>F = E\<close>
      by simp
  qed
  show ?thesis
    apply (rule Rep_kraus_family_inject[THEN iffD1])
    by (auto intro!: 1 2 3 simp: kf_map.rep_eq kf_map_inj.rep_eq Rep\<EE> Ey)
qed

lemma kf_map_eq_kf_map_inj_singleton':
  assumes \<open>\<And>y. card_le_1 (Rep_kraus_family (kf_filter ((=)y) \<EE>))\<close>
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_map f \<EE> = kf_map_inj f \<EE>\<close>
proof -
  have 1: \<open>card_le_1 (Rep_kraus_family (kf_filter (\<lambda>z. x = f z) \<EE>))\<close> for x
  proof (cases \<open>x \<in> f ` kf_domain \<EE>\<close>)
    case True
    then have \<open>kf_filter (\<lambda>z. x = f z) \<EE> = kf_filter ((=) (inv_into (kf_domain \<EE>) f x)) \<EE>\<close>
      apply (rule_tac kf_filter_cong_eq)
      using assms(2)
      by auto
    with assms(1) show ?thesis
      by presburger
  next
    case False
    then have \<open>kf_filter (\<lambda>z. x = f z) \<EE> = 0\<close>
      by (simp add: image_iff)
    then show ?thesis
      by (simp add: zero_kraus_family.rep_eq)
  qed
  show ?thesis
    apply (rule kf_equal_if_filter_equal)
    unfolding kf_filter_map kf_filter_map_inj
    apply (rule kf_map_eq_kf_map_inj_singleton)
    by (rule 1)
qed

lemma kf_filter_singleton_kf_complete_measurement:
  assumes \<open>x \<in> B\<close> and \<open>is_ortho_set B\<close>
  shows \<open>kf_filter ((=)x) (kf_complete_measurement B) = kf_map_inj (\<lambda>_. x) (kf_of_op (selfbutter (sgn x)))\<close>
proof -
  from assms have [iff]: \<open>selfbutter (sgn x) \<noteq> 0\<close>
    by (smt (verit, best) inverse_1 is_ortho_set_def norm_butterfly norm_sgn norm_zero right_inverse)
  show ?thesis
    apply (transfer' fixing: x B)
    by (auto intro!: simp: assms)
qed

lemma kf_filter_singleton_kf_complete_measurement':
  assumes \<open>x \<in> B\<close> and \<open>is_ortho_set B\<close>
  shows \<open>kf_filter ((=)x) (kf_complete_measurement B) = kf_map (\<lambda>_. x) (kf_of_op (selfbutter (sgn x)))\<close>
  using kf_filter_singleton_kf_complete_measurement[OF assms]
  apply (subst kf_map_eq_kf_map_inj_singleton)
  by (auto simp: kf_of_op.rep_eq)

lemma kf_filter_disjoint:
  assumes \<open>\<And>x. x \<in> kf_domain \<EE> \<Longrightarrow> P x = False\<close>
  shows \<open>kf_filter P \<EE> = 0\<close>
  using assms
  apply (transfer' fixing: P)
  by fastforce



lemma kf_complete_measurement_tensor:
  assumes \<open>is_ortho_set B\<close> and \<open>is_ortho_set C\<close>
  shows \<open>kf_map (\<lambda>(b,c). b \<otimes>\<^sub>s c) (kf_tensor (kf_complete_measurement B) (kf_complete_measurement C))
    = kf_complete_measurement ((\<lambda>(b,c). b \<otimes>\<^sub>s c) ` (B \<times> C))\<close>
proof (rule kf_equal_if_filter_equal, rename_tac bc)
  fix bc :: \<open>('a \<times> 'b) ell2\<close>
  define BC where \<open>BC = ((\<lambda>(x, y). x \<otimes>\<^sub>s y) ` (B \<times> C))\<close>
  consider (bc_tensor) b c where \<open>b \<in> B\<close> \<open>c \<in> C\<close> \<open>bc = b \<otimes>\<^sub>s c\<close>
      | (not_bc_tensor) \<open>\<not> (\<exists>b\<in>B. \<exists>c\<in>C. bc = b \<otimes>\<^sub>s c)\<close>
    by fastforce
  then show \<open>kf_filter ((=) bc) (kf_map (\<lambda>(b, c). b \<otimes>\<^sub>s c) (kf_tensor (kf_complete_measurement B) (kf_complete_measurement C)))
      = kf_filter ((=) bc) (kf_complete_measurement ((\<lambda>(b, c). b \<otimes>\<^sub>s c) ` (B \<times> C)))\<close>
  proof cases
    case bc_tensor
    have uniq: \<open>b = b'\<close>  \<open>c = c'\<close> if \<open>b' \<in> B\<close> and \<open>c' \<in> C\<close> and \<open>b \<otimes>\<^sub>s c = b' \<otimes>\<^sub>s c'\<close> for b' c'
    proof -
      from bc_tensor have \<open>b \<noteq> 0\<close>
        using assms(1) is_ortho_set_def by blast
      with that(3) obtain \<gamma> where upto: \<open>c = \<gamma> *\<^sub>C c'\<close>
        apply atomize_elim
        by (rule tensor_ell2_almost_injective)
      from bc_tensor have \<open>c \<noteq> 0\<close>
        using assms(2) is_ortho_set_def by blast
      with upto have \<open>\<gamma> \<noteq> 0\<close>
        by auto
      with \<open>c \<noteq> 0\<close> upto have \<open>c \<bullet>\<^sub>C c' \<noteq> 0\<close>
        by simp
      with \<open>c \<in> C\<close> \<open>c' \<in> C\<close> \<open>is_ortho_set C\<close>
      show \<open>c = c'\<close>
        using is_ortho_setD by blast
      with that have \<open>b \<otimes>\<^sub>s c = b' \<otimes>\<^sub>s c\<close>
        by simp
      with \<open>c \<noteq> 0\<close> \<open>b \<in> B\<close> \<open>b' \<in> B\<close> \<open>is_ortho_set B\<close> show \<open>b = b'\<close>
        by (metis cinner_eq_zero_iff is_ortho_setD nonzero_mult_div_cancel_right tensor_ell2_inner_prod)
    qed

    have [iff]: \<open>selfbutter (sgn b) \<noteq> 0\<close>
      by (smt (verit, ccfv_SIG) bc_tensor assms inverse_1 is_ortho_set_def norm_butterfly norm_sgn norm_zero right_inverse)
    have [iff]: \<open>selfbutter (sgn c) \<noteq> 0\<close>
      by (smt (verit) bc_tensor assms inverse_1 is_ortho_set_def norm_butterfly norm_sgn norm_zero right_inverse)
    have [iff]: \<open>selfbutter (sgn bc) \<noteq> 0\<close>
      by (smt (verit, del_insts) \<open>selfbutter (sgn b) \<noteq> 0\<close> \<open>selfbutter (sgn c) \<noteq> 0\<close> bc_tensor(3) butterfly_0_right mult_cancel_right1 norm_butterfly norm_sgn sgn_zero
          tensor_ell2_nonzero)
    have \<open>kf_filter ((=) bc) (kf_map (\<lambda>(b, c). b \<otimes>\<^sub>s c) (kf_tensor (kf_complete_measurement B) (kf_complete_measurement C)))
      = kf_map (\<lambda>(x, y). x \<otimes>\<^sub>s y) (kf_filter (\<lambda>x. bc = (case x of (b, c) \<Rightarrow> b \<otimes>\<^sub>s c))
                                 (kf_tensor (kf_complete_measurement B) (kf_complete_measurement C)))\<close>
      by (simp add: kf_filter_map)
    also have \<open>\<dots> = kf_map (\<lambda>(x, y). x \<otimes>\<^sub>s y) (kf_filter ((=)(b,c))
                                 (kf_tensor (kf_complete_measurement B) (kf_complete_measurement C)))\<close>
      apply (rule arg_cong[where f=\<open>kf_map _\<close>])
      apply (rule kf_filter_cong_eq[OF refl])
      by (auto intro!: uniq simp add: kf_domain_tensor kf_complete_measurement_domain assms case_prod_beta bc_tensor split!: prod.split)
    also have \<open>\<dots> = kf_map (\<lambda>(x, y). x \<otimes>\<^sub>s y) (kf_tensor (kf_filter ((=) b) (kf_complete_measurement B))
                 (kf_filter ((=) c) (kf_complete_measurement C)))\<close>
      by (simp add: kf_filter_tensor_singleton)
    also have \<open>\<dots> = kf_map (\<lambda>(x, y). x \<otimes>\<^sub>s y) (kf_map (\<lambda>(E, F, y). y) (kf_tensor_raw (kf_filter ((=) b) (kf_complete_measurement B))
                 (kf_filter ((=) c) (kf_complete_measurement C))))\<close>
      by (simp add: kf_tensor_def id_def)
    also have \<open>\<dots> = kf_map (\<lambda>(x, y). x \<otimes>\<^sub>s y) (kf_map (\<lambda>(E, F, y). y) (kf_tensor_raw (kf_map (\<lambda>_. b) (kf_of_op (selfbutter (sgn b)))) 
                  (kf_map (\<lambda>_. c) (kf_of_op (selfbutter (sgn c))))))\<close>
      by (simp add: kf_filter_singleton_kf_complete_measurement' bc_tensor assms)
    also have \<open>\<dots> = kf_map_inj (\<lambda>(x, y). x \<otimes>\<^sub>s y) (kf_map_inj (\<lambda>(E, F, y). y) (kf_tensor_raw (kf_map_inj (\<lambda>_. b) (kf_of_op (selfbutter (sgn b)))) 
                  (kf_map_inj (\<lambda>_. c) (kf_of_op (selfbutter (sgn c))))))\<close>
      apply (subst (4) kf_map_eq_kf_map_inj_singleton)
       apply (simp add: kf_of_op.rep_eq)
      apply (subst (3) kf_map_eq_kf_map_inj_singleton)
       apply (simp add: kf_of_op.rep_eq)
      apply (subst (2) kf_map_eq_kf_map_inj_singleton)
       apply (simp add: kf_of_op.rep_eq kf_map_inj.rep_eq kf_tensor_raw.rep_eq)
      apply (subst (1) kf_map_eq_kf_map_inj_singleton)
       apply (simp add: kf_of_op.rep_eq kf_map_inj.rep_eq kf_tensor_raw.rep_eq)
      by blast
    also have \<open>\<dots> = kf_map_inj (\<lambda>_. b \<otimes>\<^sub>s c) (kf_of_op (selfbutter (sgn bc)))\<close>
      apply (transfer' fixing: b c bc)
      by (auto intro!: bc_tensor simp: tensor_butterfly simp flip: sgn_tensor_ell2 bc_tensor)
    also have \<open>\<dots> = kf_map (\<lambda>_. bc) (kf_of_op (selfbutter (sgn bc)))\<close>
      apply (subst kf_map_eq_kf_map_inj_singleton)
      by (auto intro!: bc_tensor simp: kf_of_op.rep_eq kf_map_inj.rep_eq kf_tensor_raw.rep_eq simp flip: bc_tensor)
    also have \<open>\<dots> = kf_filter ((=) bc) (kf_complete_measurement ((\<lambda>(b, c). b \<otimes>\<^sub>s c) ` (B \<times> C)))\<close>
      apply (subst kf_filter_singleton_kf_complete_measurement')
      by (auto simp: is_ortho_set_tensor bc_tensor assms)
    finally show ?thesis
      by -
  next
    case not_bc_tensor
    have ortho: \<open>is_ortho_set ((\<lambda>x. case x of (x, xa) \<Rightarrow> x \<otimes>\<^sub>s xa) ` (B \<times> C))\<close>
      by (metis is_ortho_set_tensor not_bc_tensor assms)
    show ?thesis
      apply (subst kf_filter_disjoint)
      using not_bc_tensor
       apply (simp add: kf_domain_tensor kf_complete_measurement_domain assms)
       apply fastforce
      apply (subst kf_filter_disjoint)
      using not_bc_tensor
       apply (simp add: kf_domain_tensor kf_complete_measurement_domain ortho)
       apply fastforce
      by simp
  qed
qed

lemma card_le_1_kf_filter: \<open>card_le_1 (Rep_kraus_family (kf_filter P \<EE>))\<close> if \<open>card_le_1 (Rep_kraus_family \<EE>)\<close>
  by (metis (no_types, lifting) card_le_1_def filter_insert_if kf_filter.rep_eq kf_filter_0_right
      subset_singleton_iff that zero_kraus_family.rep_eq)

lemma card_le_1_kf_map_inj[iff]: \<open>card_le_1 (Rep_kraus_family (kf_map_inj f \<EE>))\<close> if \<open>card_le_1 (Rep_kraus_family \<EE>)\<close>
  using that
  apply transfer'
  by (auto simp: card_le_1_def case_prod_unfold)


lemma card_le_1_kf_map[iff]: \<open>card_le_1 (Rep_kraus_family (kf_map f \<EE>))\<close> if \<open>card_le_1 (Rep_kraus_family \<EE>)\<close>
  using kf_map_eq_kf_map_inj_singleton[OF that] card_le_1_kf_map_inj[OF that]
  by metis
  

lemma card_le_1_kf_tensor_raw[iff]: \<open>card_le_1 (Rep_kraus_family (kf_tensor_raw \<EE> \<FF>))\<close> if \<open>card_le_1 (Rep_kraus_family \<EE>)\<close> and \<open>card_le_1 (Rep_kraus_family \<FF>)\<close>
  using that
  apply transfer'
  apply (simp add: card_le_1_def)
  by fast

lemma card_le_1_kf_tensor[iff]: \<open>card_le_1 (Rep_kraus_family (kf_tensor \<EE> \<FF>))\<close> if \<open>card_le_1 (Rep_kraus_family \<EE>)\<close> and \<open>card_le_1 (Rep_kraus_family \<FF>)\<close>
  by (auto intro!: card_le_1_kf_map card_le_1_kf_tensor_raw that simp add: kf_tensor_def)

lemma card_le_1_kf_filter_complete_measurement: \<open>card_le_1 (Rep_kraus_family (kf_filter ((=)x) (kf_complete_measurement B)))\<close>
proof -
  consider (inB) \<open>is_ortho_set B \<and> x \<in> B\<close> | (not_ortho) \<open>\<not> is_ortho_set B\<close> | (notinB) \<open>x \<notin> B\<close> \<open>is_ortho_set B\<close>
    by auto
  then show ?thesis
  proof cases
    case inB
    then have \<open>Rep_kraus_family (kf_filter ((=)x) (kf_complete_measurement B)) = {(selfbutter (sgn x),x)}\<close>
      by (auto simp: kf_filter.rep_eq kf_complete_measurement.rep_eq)
    then show ?thesis
      by (simp add: card_le_1_def)
  next
    case not_ortho
    then show ?thesis
      by (simp add: kf_complete_measurement_invalid zero_kraus_family.rep_eq)
  next
    case notinB
    then have \<open>kf_filter ((=) x) (kf_complete_measurement B) = 0\<close>
      by (metis kf_complete_measurement_domain kf_filter_disjoint)
    then show ?thesis
      by (simp add: zero_kraus_family.rep_eq)
  qed
qed

lemma kf_complete_measurement_ket_tensor:
  shows \<open>kf_tensor (kf_complete_measurement_ket :: (_,_,'a) kraus_family) (kf_complete_measurement_ket :: (_,_,'b) kraus_family)
             = kf_complete_measurement_ket\<close>
proof -
  have 1: \<open>(\<lambda>(b, c). b \<otimes>\<^sub>s c) ` (range ket \<times> range ket) = range ket\<close>
    by (auto intro!: image_eqI simp: tensor_ell2_ket case_prod_unfold)
  have 2: \<open>inj_on (inv ket \<circ> (\<lambda>(x, y). x \<otimes>\<^sub>s y)) (range ket \<times> range ket)\<close>
    by (auto intro!: inj_onI simp: tensor_ell2_ket)
  have \<open>(kf_complete_measurement_ket :: (_,_,'a\<times>'b) kraus_family)
      = kf_map_inj (inv ket) (kf_complete_measurement ((\<lambda>(b,c). b \<otimes>\<^sub>s c) ` (range ket \<times> range ket)))\<close>
    by (simp add: 1 kf_complete_measurement_ket_def)
  also have \<open>\<dots> = kf_map_inj (inv ket)
     (kf_map (\<lambda>(x, y). x \<otimes>\<^sub>s y)
       (kf_tensor (kf_complete_measurement (range ket)) (kf_complete_measurement (range ket))))\<close>
    by (simp flip: kf_complete_measurement_tensor)
  also have \<open>\<dots> = kf_map (inv ket \<circ> (\<lambda>(x, y). x \<otimes>\<^sub>s y))
     (kf_tensor (kf_complete_measurement (range ket)) (kf_complete_measurement (range ket)))\<close>
    apply (subst kf_map_inj_kf_map_comp)
    by (auto intro!: simp: inj_on_def kf_domain_tensor tensor_ell2_ket)
  also have \<open>\<dots> = kf_map_inj (inv ket \<circ> (\<lambda>(x, y). x \<otimes>\<^sub>s y))
     (kf_tensor (kf_complete_measurement (range ket)) (kf_complete_measurement (range ket)))\<close>
    apply (rule kf_map_eq_kf_map_inj_singleton')
     apply (auto intro!: card_le_1_kf_filter_complete_measurement card_le_1_kf_tensor simp: kf_filter_tensor_singleton)[1]
    by (simp add: kf_domain_tensor 2)
  also have \<open>\<dots> = kf_map_inj (map_prod (inv ket) (inv ket))
      (kf_tensor (kf_complete_measurement (range ket)) (kf_complete_measurement (range ket)))\<close>
    apply (rule kf_map_inj_cong_eq)
    by (auto simp: kf_domain_tensor tensor_ell2_ket)
  also have \<open>\<dots> = kf_tensor (kf_map_inj (inv ket) (kf_complete_measurement (range ket)))
                            (kf_map_inj (inv ket) (kf_complete_measurement (range ket)))\<close>
    by (simp add: kf_tensor_map_inj_both inj_on_inv_into)
  also have \<open>\<dots> = kf_tensor kf_complete_measurement_ket kf_complete_measurement_ket\<close>
    by (simp add: kf_complete_measurement_ket_def)
  finally show ?thesis
    by simp
qed

subsection \<open>Reconstruction\<close>

lemma kf_reconstruction_is_bounded_clinear:
  assumes \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum \<EE> \<rho>) A\<close>
  shows \<open>bounded_clinear \<EE>\<close>
proof -
  have linear: \<open>clinear \<EE>\<close>
  proof (rule clinearI)
    fix \<rho> \<sigma> c
    have \<open>((\<lambda>a. sandwich_tc (f a) \<rho> + sandwich_tc (f a) \<sigma>) has_sum (\<EE> \<rho> + \<EE> \<sigma>)) A\<close>
      by (intro has_sum_add assms)
    then have \<open>((\<lambda>a. sandwich_tc (f a) (\<rho> + \<sigma>)) has_sum (\<EE> \<rho> + \<EE> \<sigma>)) A\<close>
      by (meson has_sum_cong sandwich_tc_plus)
    with assms[of \<open>\<rho> + \<sigma>\<close>]
    show \<open>\<EE> (\<rho> + \<sigma>) = \<EE> \<rho> + \<EE> \<sigma>\<close>
      by (rule has_sum_unique)
    from assms[of \<rho>]
    have \<open>((\<lambda>a. sandwich_tc (f a) (c *\<^sub>C \<rho>)) has_sum c *\<^sub>C \<EE> \<rho>) A\<close>
      using has_sum_scaleC_right[where A=A and s=\<open>\<EE> \<rho>\<close>]
      by (auto intro!: has_sum_scaleC_right simp: sandwich_tc_scaleC_right)
    with assms[of \<open>c *\<^sub>C \<rho>\<close>]
    show \<open>\<EE> (c *\<^sub>C \<rho>) = c *\<^sub>C \<EE> \<rho>\<close>
      by (rule has_sum_unique)
  qed
  have pos: \<open>\<EE> \<rho> \<ge> 0\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho>
    apply (rule has_sum_mono_traceclass[where f=\<open>\<lambda>_.0\<close> and g=\<open>(\<lambda>a. sandwich_tc (f a) \<rho>)\<close>])
    using assms
    by (auto intro!: sandwich_tc_pos simp: that)
  have mono: \<open>\<EE> \<rho> \<le> \<EE> \<sigma>\<close> if \<open>\<rho> \<le> \<sigma>\<close> for \<rho> \<sigma>
  proof -
    have \<open>\<EE> (\<sigma> - \<rho>) \<ge> 0\<close>
      apply (rule pos)
      using that
      by auto
    then show ?thesis
      by (simp add: linear complex_vector.linear_diff)
  qed
  have bounded_pos: \<open>\<exists>B\<ge>0. \<forall>\<rho>\<ge>0. norm (\<EE> \<rho>) \<le> B * norm \<rho>\<close>
  proof (rule ccontr)
    assume asm: \<open>\<not> (\<exists>B\<ge>0. \<forall>\<rho>\<ge>0. norm (\<EE> \<rho>) \<le> B * norm \<rho>)\<close>
    obtain \<rho>0 where \<EE>_big0: \<open>norm (\<EE> (\<rho>0 i)) > 2^i * norm (\<rho>0 i)\<close> and \<rho>0_pos: \<open>\<rho>0 i \<ge> 0\<close> for i :: nat
    proof (atomize_elim, rule choice2, rule allI, rule ccontr)
      fix i
      define B :: real where \<open>B = 2^i\<close>
      have \<open>B \<ge> 0\<close>
        by (simp add: B_def)
      assume \<open>\<nexists>\<rho>0. B * norm \<rho>0 < norm (\<EE> \<rho>0) \<and> 0 \<le> \<rho>0\<close>
      then have \<open>\<forall>\<rho>\<ge>0. norm (\<EE> \<rho>) \<le> B * norm \<rho>\<close>
        by force
      with asm \<open>B \<ge> 0\<close> show False
        by blast
    qed
    have \<rho>0_neq0: \<open>\<rho>0 i \<noteq> 0\<close> for i
      using \<EE>_big0[of i] linear complex_vector.linear_0 by force
    define \<rho> where \<open>\<rho> i = \<rho>0 i /\<^sub>R norm (\<rho>0 i)\<close> for i
    have \<rho>_pos: \<open>\<rho> i \<ge> 0\<close> for i
      by (simp add: \<rho>_def \<rho>0_pos scaleR_nonneg_nonneg)
    have norm_\<rho>: \<open>norm (\<rho> i) = 1\<close> for i
      by (simp add: \<rho>0_neq0 \<rho>_def)
    from \<EE>_big0 have \<EE>_big: \<open>trace_tc (\<EE> (\<rho> i)) \<ge> 2^i\<close> for i :: nat
    proof -
      have \<open>trace_tc (\<EE> (\<rho> i)) = trace_tc (\<EE> (\<rho>0 i) /\<^sub>R norm (\<rho>0 i))\<close>
        by (simp add: \<rho>_def linear scaleR_scaleC clinear.scaleC 
          bounded_clinear_trace_tc[THEN bounded_clinear.clinear])
      also have \<open>\<dots> = norm (\<EE> (\<rho>0 i) /\<^sub>R norm (\<rho>0 i))\<close>
        using \<rho>0_pos pos
        by (metis linordered_field_class.inverse_nonnegative_iff_nonnegative norm_ge_zero norm_tc_pos scaleR_nonneg_nonneg)
      also have \<open>\<dots> = norm (\<EE> (\<rho>0 i)) / norm (\<rho>0 i)\<close>
        by (simp add: divide_inverse_commute)
      also have \<open>\<dots> > (2^i * norm (\<rho>0 i)) / norm (\<rho>0 i)\<close> (is \<open>_ > \<dots>\<close>)
        using \<EE>_big0 \<rho>0_neq0
        by (smt (verit, best) complex_of_real_strict_mono_iff divide_le_eq norm_le_zero_iff)
      also have \<open>\<dots> = 2^i\<close>
        using \<rho>0_neq0 by force
      finally show ?thesis
        by simp
    qed
    define \<sigma> \<tau> where \<open>\<sigma> n = (\<Sum>i<n. \<rho> i /\<^sub>R 2^i)\<close> and \<open>\<tau> = (\<Sum>\<^sub>\<infinity>i. \<rho> i /\<^sub>R 2^i)\<close> for n :: nat
    have \<open>(\<lambda>i. \<rho> i /\<^sub>R 2^i) abs_summable_on UNIV\<close>
    proof (rule infsum_tc_norm_bounded_abs_summable)
      from \<rho>_pos show \<open>\<rho> i /\<^sub>R 2^i \<ge> 0\<close> for i
        by (simp add: scaleR_nonneg_nonneg)
      show \<open>norm (\<Sum>i\<in>F. \<rho> i /\<^sub>R 2^i) \<le> 2\<close> if \<open>finite F\<close> for F
      proof -
        from finite_nat_bounded[OF that]
        obtain n where i_leq_n: \<open>i \<le> n\<close> if \<open>i \<in> F\<close> for i
          apply atomize_elim
          by (auto intro!: order.strict_implies_order simp: lessThan_def Ball_def simp flip: Ball_Collect)
        have \<open>norm (\<Sum>i\<in>F. \<rho> i /\<^sub>R 2^i) \<le> (\<Sum>i\<in>F. norm (\<rho> i /\<^sub>R 2^i))\<close>
          by (simp add: sum_norm_le)
        also have \<open>\<dots> = (\<Sum>i\<in>F. (1/2)^i)\<close>
          using norm_\<rho> 
          by (smt (verit, del_insts) Extra_Ordered_Fields.sign_simps(23) divide_inverse_commute linordered_field_class.inverse_nonnegative_iff_nonnegative
              norm_scaleR power_inverse power_one sum.cong zero_le_power)
        also have \<open>\<dots> \<le> (\<Sum>i\<le>n. (1/2)^i)\<close>
          apply (rule sum_mono2)
          using i_leq_n
          by auto
        also have \<open>\<dots> \<le> (\<Sum>i. (1/2)^i)\<close>
          apply (rule sum_le_suminf)
          by auto
        also have \<open>... = 2\<close>
          using suminf_geometric[of \<open>1/2 :: real\<close>]
          by simp
        finally show ?thesis
          by -
      qed
    qed
    then have summable: \<open>(\<lambda>i. \<rho> i /\<^sub>R 2^i) summable_on UNIV\<close>
      by (simp add: abs_summable_summable)
    have \<open>trace_tc (\<EE> \<tau>) \<ge> n\<close> for n :: nat
    proof -
      have \<open>trace_tc (\<EE> \<tau>) \<ge> trace_tc (\<EE> (\<sigma> n))\<close> (is \<open>_ \<ge> \<dots>\<close>)
        by (auto intro!: trace_tc_mono mono infsum_mono_neutral_traceclass
            simp: \<tau>_def \<sigma>_def summable \<rho>_pos scaleR_nonneg_nonneg simp flip: infsum_finite)
      moreover have \<open>\<dots> = (\<Sum>i<n. trace_tc (\<EE> (\<rho> i)) / 2^i)\<close>
        by (simp add: \<sigma>_def complex_vector.linear_sum linear scaleR_scaleC trace_scaleC
            bounded_clinear_trace_tc[THEN bounded_clinear.clinear] clinear.scaleC
            add.commute mult.commute divide_inverse)
      moreover have \<open>\<dots> \<ge> (\<Sum>i<n. 2^i / 2^i)\<close> (is \<open>_ \<ge> \<dots>\<close>)
        apply (intro sum_mono divide_right_mono)
        using \<EE>_big
        by (simp_all add: less_eq_complex_def)
      moreover have \<open>\<dots> = (\<Sum>i<n. 1)\<close>
        by fastforce
      moreover have \<open>\<dots> = n\<close>
        by simp
      ultimately show ?thesis
        by order
    qed
    then have Re: \<open>Re (trace_tc (\<EE> \<tau>)) \<ge> n\<close> for n :: nat
      using Re_mono by fastforce
    obtain n :: nat where \<open>n > Re (trace_tc (\<EE> \<tau>))\<close>
      apply atomize_elim
      by (rule reals_Archimedean2)
    with Re show False
      by (smt (verit, ccfv_threshold))
  qed
  then obtain B where bounded_B: \<open>norm (\<EE> \<rho>) \<le> B * norm \<rho>\<close> and B_pos: \<open>B \<ge> 0\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho>
    by auto
  have bounded: \<open>norm (\<EE> \<rho>) \<le> (4*B) * norm \<rho>\<close> for \<rho>
  proof -
    obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
      and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
      and norm: \<open>norm \<rho>1 \<le> norm \<rho>\<close> \<open>norm \<rho>2 \<le> norm \<rho>\<close> \<open>norm \<rho>3 \<le> norm \<rho>\<close> \<open>norm \<rho>4 \<le> norm \<rho>\<close>
      apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
    have \<open>norm (\<EE> \<rho>) \<le> norm (\<EE> \<rho>1) + norm (\<EE> \<rho>2) + norm (\<EE> \<rho>3) + norm (\<EE> \<rho>4)\<close>
      using linear
      by (auto intro!: norm_triangle_le norm_triangle_le_diff
          simp add: \<rho>_decomp kf_apply_plus_right kf_apply_minus_right
          kf_apply_scaleC complex_vector.linear_diff complex_vector.linear_add clinear.scaleC)
    also have \<open>\<dots> \<le> B * norm \<rho>1 + B * norm \<rho>2 + B * norm \<rho>3 + B * norm \<rho>4\<close>
      using pos by (auto intro!: add_mono simp add: pos bounded_B)
    also have \<open>\<dots> = B * (norm \<rho>1 + norm \<rho>2 + norm \<rho>3 + norm \<rho>4)\<close>
      by argo
    also have \<open>\<dots> \<le> B * (norm \<rho> + norm \<rho> + norm \<rho> + norm \<rho>)\<close>
      by (auto intro!: mult_left_mono add_mono pos B_pos
          simp only: norm)
    also have \<open>\<dots> = (4 * B) * norm \<rho>\<close>
      by argo
    finally show ?thesis
      by -
  qed
  show ?thesis
    apply (rule bounded_clinearI[where K=\<open>4*B\<close>])
      apply (simp add: complex_vector.linear_add linear) 
     apply (simp add: complex_vector.linear_scale linear) 
    using bounded by (metis Groups.mult_ac)
qed

lemma kf_reconstruction_is_kraus_family:
  assumes sum: \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum \<EE> \<rho>) A\<close>
  defines \<open>F \<equiv> Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>a. (f a, a)) ` A)\<close>
  shows \<open>kraus_family F\<close>
proof -
  from sum have \<open>bounded_clinear \<EE>\<close>
    by (rule kf_reconstruction_is_bounded_clinear)
  then obtain B where B: \<open>norm (\<EE> \<rho>) \<le> B * norm \<rho>\<close> for \<rho>
    apply atomize_elim
    by (simp add: bounded_clinear_axioms_def bounded_clinear_def mult.commute)
  show ?thesis
  proof (intro kraus_familyI bdd_aboveI2)
    fix S assume \<open>S \<in> {S. finite S \<and> S \<subseteq> F}\<close>
    then have \<open>S \<subseteq> F\<close> and \<open>finite S\<close>
      by auto
    then obtain A' where \<open>finite A'\<close> and \<open>A' \<subseteq> A\<close> and S_A': \<open>S = (\<lambda>a. (f a,a)) ` A'\<close>
      by (metis (no_types, lifting) F_def finite_subset_filter_image)
    show \<open>(\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B *\<^sub>C id_cblinfun\<close>
    proof (rule cblinfun_leI)
      fix h :: 'a assume \<open>norm h = 1\<close>
      have \<open>h \<bullet>\<^sub>C ((\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) h) = h \<bullet>\<^sub>C (\<Sum>a\<in>A'. (f a)* o\<^sub>C\<^sub>L f a) h\<close>
        by (simp add: S_A' sum.reindex inj_on_def)
      also have \<open>\<dots> = (\<Sum>a\<in>A'. h \<bullet>\<^sub>C ((f a)* o\<^sub>C\<^sub>L f a) h)\<close>
        apply (rule complex_vector.linear_sum)
        by (simp add: bounded_clinear.clinear bounded_clinear_cinner_right_comp) 
      also have \<open>\<dots> = (\<Sum>a\<in>A'. trace_tc (sandwich_tc (f a) (tc_butterfly h h)))\<close>
        by (auto intro!: sum.cong[OF refl]
            simp: trace_tc.rep_eq from_trace_class_sandwich_tc
            tc_butterfly.rep_eq cblinfun_comp_butterfly sandwich_apply trace_butterfly_comp)
      also have \<open>\<dots> = trace_tc (\<Sum>a\<in>A'. sandwich_tc (f a) (tc_butterfly h h))\<close>
        apply (rule complex_vector.linear_sum[symmetric])
        using clinearI trace_tc_plus trace_tc_scaleC by blast
      also have \<open>\<dots> = trace_tc (\<Sum>\<^sub>\<infinity>a\<in>A'. sandwich_tc (f a) (tc_butterfly h h))\<close>
        by (simp add: \<open>finite A'\<close>)
      also have \<open>\<dots> \<le> trace_tc (\<Sum>\<^sub>\<infinity>a\<in>A. (sandwich_tc (f a) (tc_butterfly h h)))\<close>
        apply (intro trace_tc_mono infsum_mono_neutral_traceclass)
        using \<open>A' \<subseteq> A\<close> sum[of \<open>tc_butterfly h h\<close>]
        by (auto intro!: sandwich_tc_pos has_sum_imp_summable simp: \<open>finite A'\<close>)
      also have \<open>\<dots> = trace_tc (\<EE> (tc_butterfly h h))\<close>
        by (metis sum infsumI)
      also have \<open>\<dots> = norm (\<EE> (tc_butterfly h h))\<close>
        by (metis (no_types, lifting) infsumI infsum_nonneg_traceclass norm_tc_pos sandwich_tc_pos sum tc_butterfly_pos)
      also from B have \<open>\<dots> \<le> B * norm (tc_butterfly h h)\<close>
        using complex_of_real_mono by blast
      also have \<open>\<dots> = B\<close>
        by (simp add: \<open>norm h = 1\<close> norm_tc_butterfly)
      also have \<open>\<dots> = h \<bullet>\<^sub>C (complex_of_real B *\<^sub>C id_cblinfun *\<^sub>V h)\<close>
        using \<open>norm h = 1\<close> cnorm_eq_1 by auto
      finally show \<open>h \<bullet>\<^sub>C ((\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) *\<^sub>V h) \<le> h \<bullet>\<^sub>C (complex_of_real B *\<^sub>C id_cblinfun *\<^sub>V h)\<close>
        by -
    qed
  next
    show \<open>0 \<notin> fst ` F\<close>
      by (force simp: F_def)
  qed
qed

lemma kf_reconstruction:
  assumes sum: \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum \<EE> \<rho>) A\<close>
  defines \<open>F \<equiv> Abs_kraus_family (Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>a. (f a, a)) ` A))\<close>
  shows \<open>kf_apply F = \<EE>\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  have Rep_F: \<open>Rep_kraus_family F = (Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>a. (f a,a)) ` A))\<close>
    unfolding F_def
    apply (rule Abs_kraus_family_inverse)
    by (auto intro!: kf_reconstruction_is_kraus_family[of _ _ \<EE>] assms simp: F_def)
  have \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum kf_apply F \<rho>) (Rep_kraus_family F)\<close>
    by (auto intro!: kf_apply_has_sum)
  then have \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum kf_apply F \<rho>) ((\<lambda>a. (f a,a)) ` A)\<close>
    apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
    by (auto simp: Rep_F)
  then have \<open>((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum kf_apply F \<rho>) A\<close>
    apply (subst (asm) has_sum_reindex)
    by (auto simp: inj_on_def o_def)
  with sum show \<open>kf_apply F \<rho> = \<EE> \<rho>\<close>
    by (metis (no_types, lifting) infsumI)
qed

subsection \<open>Cleanup\<close>

unbundle no cblinfun_syntax
unbundle no kraus_map_syntax

end
