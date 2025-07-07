section \<open>Kraus maps\<close>

theory Kraus_Maps
  imports Kraus_Families
begin

subsection \<open>Kraus maps\<close>

unbundle kraus_map_syntax
unbundle cblinfun_syntax

definition kraus_map :: \<open>(('a::chilbert_space,'a) trace_class \<Rightarrow> ('b::chilbert_space,'b) trace_class) \<Rightarrow> bool\<close> where
  kraus_map_def_raw: \<open>kraus_map \<EE> \<longleftrightarrow> (\<exists>EE :: ('a,'b,unit) kraus_family. \<EE> = kf_apply EE)\<close>

lemma kraus_map_def: \<open>kraus_map \<EE> \<longleftrightarrow> (\<exists>EE :: ('a::chilbert_space,'b::chilbert_space,'x) kraus_family. \<EE> = kf_apply EE)\<close>
  \<comment> \<open>Has a more general type than the original definition\<close>
proof (rule iffI)
  assume \<open>kraus_map \<EE>\<close>
  then obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  define EE' :: \<open>('a,'b,'x) kraus_family\<close> where \<open>EE' = kf_map (\<lambda>_. undefined) EE\<close>
  have \<open>kf_apply EE' = kf_apply EE\<close>
    by (simp add: EE'_def kf_apply_map)
  with EE show \<open>\<exists>EE :: ('a,'b,'x) kraus_family. \<EE> = kf_apply EE\<close>
    by metis
next
  assume \<open>\<exists>EE :: ('a,'b,'x) kraus_family. \<EE> = kf_apply EE\<close>
  then obtain EE :: \<open>('a,'b,'x) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  define EE' :: \<open>('a,'b,unit) kraus_family\<close> where \<open>EE' = kf_map (\<lambda>_. ()) EE\<close>
  have \<open>kf_apply EE' = kf_apply EE\<close>
    by (simp add: EE'_def kf_apply_map)
  with EE show \<open>kraus_map \<EE>\<close>
    apply (simp add: kraus_map_def_raw)
    by metis
qed

lemma kraus_mapI:
  assumes \<open>\<EE> = kf_apply \<EE>'\<close>
  shows \<open>kraus_map \<EE>\<close>
  using assms kraus_map_def by blast

lemma kraus_map_bounded_clinear: 
  \<open>bounded_clinear \<EE>\<close> if \<open>kraus_map \<EE>\<close>
  by (metis kf_apply_bounded_clinear kraus_map_def that)

lemma kraus_map_pos:
  assumes \<open>kraus_map \<EE>\<close> and \<open>\<rho> \<ge> 0\<close>
  shows \<open>\<EE> \<rho> \<ge> 0\<close>
proof -
  from assms obtain \<EE>' :: \<open>('a, 'b, unit) kraus_family\<close> where \<EE>': \<open>\<EE> = kf_apply \<EE>'\<close>
    using kraus_map_def by blast
  show ?thesis
    by (simp add: \<EE>' assms(2) kf_apply_pos)
qed

lemma kraus_map_mono:
  assumes \<open>kraus_map \<EE>\<close> and \<open>\<rho> \<ge> \<tau>\<close>
  shows \<open>\<EE> \<rho> \<ge> \<EE> \<tau>\<close>
  by (metis assms kf_apply_mono_right kraus_map_def_raw)

lemma kraus_map_kf_apply[iff]: \<open>kraus_map (kf_apply \<EE>)\<close>
  using kraus_map_def by blast

definition km_some_kraus_family :: \<open>(('a::chilbert_space, 'a) trace_class \<Rightarrow> ('b::chilbert_space, 'b) trace_class) \<Rightarrow> ('a, 'b, unit) kraus_family\<close> where
  \<open>km_some_kraus_family \<EE> = (if kraus_map \<EE> then SOME \<FF>. \<EE> = kf_apply \<FF> else 0)\<close>

lemma kf_apply_km_some_kraus_family[simp]:
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>kf_apply (km_some_kraus_family \<EE>) = \<EE>\<close>
  unfolding km_some_kraus_family_def
  apply (rule someI2_ex)
  using assms kraus_map_def by auto

lemma km_some_kraus_family_invalid:
  assumes \<open>\<not> kraus_map \<EE>\<close>
  shows \<open>km_some_kraus_family \<EE> = 0\<close>
  by (simp add: assms km_some_kraus_family_def)

definition km_operators_in :: \<open>(('a::chilbert_space,'a) trace_class \<Rightarrow> ('b::chilbert_space,'b) trace_class) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set \<Rightarrow> bool\<close> where
  \<open>km_operators_in \<EE> S \<longleftrightarrow> (\<exists>\<FF> :: ('a,'b,unit) kraus_family. kf_apply \<FF> = \<EE> \<and> kf_operators \<FF> \<subseteq> S)\<close>

lemma km_operators_in_mono: \<open>S \<subseteq> T \<Longrightarrow> km_operators_in \<EE> S \<Longrightarrow> km_operators_in \<EE> T\<close>
  by (metis basic_trans_rules(23) km_operators_in_def)

lemma km_operators_in_kf_apply:
  assumes \<open>span (kf_operators \<EE>) \<subseteq> S\<close>
  shows \<open>km_operators_in (kf_apply \<EE>) S\<close>
proof (unfold km_operators_in_def, intro conjI exI[where x=\<open>kf_flatten \<EE>\<close>])
  show \<open>(*\<^sub>k\<^sub>r) (kf_flatten \<EE>) = (*\<^sub>k\<^sub>r) \<EE>\<close>
    by simp
  from assms show \<open>kf_operators (kf_flatten \<EE>) \<subseteq> S\<close>
    using kf_operators_kf_map by fastforce
qed

lemma km_operators_in_kf_apply_flattened:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x::CARD_1) kraus_family\<close>
  assumes \<open>kf_operators \<EE> \<subseteq> S\<close>
  shows \<open>km_operators_in (kf_apply \<EE>) S\<close>
proof (unfold km_operators_in_def, intro conjI exI[where x=\<open>kf_map_inj (\<lambda>x.()) \<EE>\<close>])
  show \<open>(*\<^sub>k\<^sub>r) (kf_map_inj (\<lambda>\<FF>. ()) \<EE>) = (*\<^sub>k\<^sub>r) \<EE>\<close>
    by (auto intro!: ext kf_apply_map_inj inj_onI)
  have \<open>kf_operators (kf_map_inj (\<lambda>\<FF>. ()) \<EE>) = kf_operators \<EE>\<close>
    by simp
  with assms show \<open>kf_operators (kf_map_inj (\<lambda>\<FF>. ()) \<EE>) \<subseteq> S\<close>
    by blast
qed

lemma km_commute:
  assumes \<open>km_operators_in \<EE> S\<close>
  assumes \<open>km_operators_in \<FF> T\<close>
  assumes \<open>S \<subseteq> commutant T\<close>
  shows \<open>\<FF> o \<EE> = \<EE> o \<FF>\<close>
proof -
  from assms obtain \<EE>' :: \<open>(_,_,unit) kraus_family\<close> where \<EE>': \<open>\<EE> = kf_apply \<EE>'\<close> and \<EE>'S: \<open>kf_operators \<EE>' \<subseteq> S\<close>
    by (metis km_operators_in_def)
  from assms obtain \<FF>' :: \<open>(_,_,unit) kraus_family\<close> where \<FF>': \<open>\<FF> = kf_apply \<FF>'\<close> and \<FF>'T: \<open>kf_operators \<FF>' \<subseteq> T\<close>
    by (metis km_operators_in_def)

  have \<open>kf_operators \<EE>' \<subseteq> S\<close>
    by (rule \<EE>'S)
  also have \<open>S \<subseteq> commutant T\<close>
    by (rule assms)
  also have \<open>commutant T \<subseteq> commutant (kf_operators \<FF>')\<close>
    apply (rule commutant_antimono)
    by (rule \<FF>'T)
  finally show ?thesis
    unfolding \<EE>' \<FF>'
    by (rule kf_apply_commute[symmetric])
qed

lemma km_operators_in_UNIV: 
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>km_operators_in \<EE> UNIV\<close>
  by (metis assms kf_apply_km_some_kraus_family km_operators_in_def top.extremum)

lemma separating_kraus_map_bounded_clinear:
  fixes S :: \<open>('a::chilbert_space,'a) trace_class set\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> ('b::chilbert_space,'b) trace_class) \<Rightarrow> _) S\<close>
  shows \<open>separating_set (kraus_map :: (_ \<Rightarrow> ('b::chilbert_space,'b) trace_class) \<Rightarrow> _) S\<close>
  by (metis (mono_tags, lifting) assms kraus_map_bounded_clinear separating_set_def)

subsection \<open>Bound and norm\<close>

definition km_bound :: \<open>(('a::chilbert_space, 'a) trace_class \<Rightarrow> ('b::chilbert_space, 'b) trace_class) \<Rightarrow> ('a, 'a) cblinfun\<close> where
 \<open>km_bound \<EE> = (if \<exists>\<EE>' :: (_, _, unit) kraus_family. \<EE> = kf_apply \<EE>' then kf_bound (SOME \<EE>' :: (_, _, unit) kraus_family. \<EE> = kf_apply \<EE>') else 0)\<close>

lemma km_bound_kf_bound:
  assumes \<open>\<EE> = kf_apply \<FF>\<close>
  shows \<open>km_bound \<EE> = kf_bound \<FF>\<close>
proof -
  wlog ex: \<open>\<exists>\<EE>' :: (_, _, unit) kraus_family. \<EE> = kf_apply \<EE>'\<close>
    using assms kraus_map_def_raw negation by blast
  define \<EE>' where \<open>\<EE>' = (SOME \<EE>' :: (_, _, unit) kraus_family. \<EE> = kf_apply \<EE>')\<close>
  have \<open>\<EE> = kf_apply (kf_flatten \<FF>)\<close>
    by (simp add: assms)
  then have \<open>\<EE> = kf_apply \<EE>'\<close>
    by (metis (mono_tags, lifting) \<EE>'_def someI_ex)
  then have \<open>\<EE>' =\<^sub>k\<^sub>r \<FF>\<close>
    using assms kf_eq_weak_def by force
  then have \<open>kf_bound \<EE>' = kf_bound \<FF>\<close>
    using kf_bound_cong by blast
  then show ?thesis
    by (metis \<EE>'_def km_bound_def ex)
qed

  
definition km_norm :: \<open>(('a::chilbert_space, 'a) trace_class \<Rightarrow> ('b::chilbert_space, 'b) trace_class) \<Rightarrow> real\<close> where
  \<open>km_norm \<EE> = norm (km_bound \<EE>)\<close>

lemma km_norm_kf_norm:
  assumes \<open>\<EE> = kf_apply \<FF>\<close>
  shows \<open>km_norm \<EE> = kf_norm \<FF>\<close>
  by (simp add: assms kf_norm_def km_bound_kf_bound km_norm_def)

lemma km_bound_invalid: 
  assumes \<open>\<not> kraus_map \<EE>\<close>
  shows \<open>km_bound \<EE> = 0\<close>
  by (metis assms km_bound_def kraus_map_def_raw)

lemma km_norm_invalid: 
  assumes \<open>\<not> kraus_map \<EE>\<close>
  shows \<open>km_norm \<EE> = 0\<close>
  by (simp add: assms km_bound_invalid km_norm_def)



lemma km_norm_geq0[iff]: \<open>km_norm \<EE> \<ge> 0\<close>
  by (simp add: km_norm_def)

lemma kf_bound_pos[iff]: \<open>km_bound \<EE> \<ge> 0\<close>
  apply (cases \<open>kraus_map \<EE>\<close>)
   apply (simp add: km_bound_def) 
  by (simp add: km_bound_invalid)

lemma km_bounded_pos:
  assumes \<open>kraus_map \<EE>\<close> and \<open>\<rho> \<ge> 0\<close>
  shows \<open>norm (\<EE> \<rho>) \<le> km_norm \<EE> * norm \<rho>\<close>
proof -
  from assms obtain \<EE>' :: \<open>('a, 'b, unit) kraus_family\<close> where \<EE>': \<open>\<EE> = kf_apply \<EE>'\<close>
    using kraus_map_def by blast
  show ?thesis
    by (simp add: \<EE>' assms(2) kf_apply_bounded_pos km_norm_kf_norm)
qed

lemma km_bounded:
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>norm (\<EE> \<rho>) \<le> 4 * km_norm \<EE> * norm \<rho>\<close>
proof -
  from assms obtain \<EE>' :: \<open>('a, 'b, unit) kraus_family\<close> where \<EE>': \<open>\<EE> = kf_apply \<EE>'\<close>
    using kraus_map_def by blast
  show ?thesis
    by (simp add: \<EE>' kf_apply_bounded km_norm_kf_norm)
qed

lemma km_bound_from_map:
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>\<psi> \<bullet>\<^sub>C km_bound \<EE> \<phi> = trace_tc (\<EE> (tc_butterfly \<phi> \<psi>))\<close>
  by (metis assms kf_bound_from_map km_bound_kf_bound kraus_map_def_raw)

lemma trace_from_km_bound: 
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>trace_tc (\<EE> \<rho>) = trace_tc (compose_tcr (km_bound \<EE>) \<rho>)\<close>
  by (metis assms km_bound_kf_bound kraus_map_def_raw trace_from_kf_bound)

lemma km_bound_selfadjoint[iff]: \<open>selfadjoint (km_bound \<EE>)\<close>
  by (simp add: pos_selfadjoint)

lemma km_bound_leq_km_norm_id: \<open>km_bound \<EE> \<le> km_norm \<EE> *\<^sub>R id_cblinfun\<close>
  by (simp add: km_norm_def less_eq_scaled_id_norm)

lemma kf_norm_km_some_kraus_family[simp]: \<open>kf_norm (km_some_kraus_family \<EE>) = km_norm \<EE>\<close>
  apply (cases \<open>kraus_map \<EE>\<close>)
  by (auto intro!: km_norm_kf_norm[symmetric] simp: km_some_kraus_family_invalid km_norm_invalid)

subsection \<open>Basic Kraus maps\<close>

text \<open>Zero map and constant maps. Addition and rescaling and composition of maps.\<close>

lemma kraus_map_0[iff]: \<open>kraus_map 0\<close>
  by (metis kf_apply_0 kraus_mapI)

lemma kraus_map_0'[iff]: \<open>kraus_map (\<lambda>_. 0)\<close>
  using kraus_map_0 unfolding func_zero by simp
lemma km_bound_0[simp]: \<open>km_bound 0 = 0\<close>
  using km_bound_kf_bound[of 0 0]
  by simp

lemma km_norm_0[simp]: \<open>km_norm 0 = 0\<close>
  by (simp add: km_norm_def)

lemma km_some_kraus_family_0[simp]: \<open>km_some_kraus_family 0 = 0\<close>
  apply (rule kf_eq_0_iff_eq_0[THEN iffD1])
  by (simp add: kf_eq_weak_def)

lemma kraus_map_id[iff]: \<open>kraus_map id\<close>
  by (auto intro!: ext kraus_mapI[of _ kf_id])

lemma km_bound_id[simp]: \<open>km_bound id = id_cblinfun\<close>
  using km_bound_kf_bound[of id kf_id]
  by (simp add: kf_id_apply[abs_def] id_def)

lemma km_norm_id_leq1[iff]: \<open>km_norm id \<le> 1\<close>
  by (simp add: km_norm_def norm_cblinfun_id_le)

lemma km_norm_id_eq1[simp]: \<open>km_norm (id :: ('a :: {chilbert_space, not_singleton}, 'a) trace_class \<Rightarrow> _) = 1\<close>
  by (simp add: km_norm_def)

lemma km_operators_in_id[iff]: \<open>km_operators_in id {id_cblinfun}\<close>
  apply (subst asm_rl[of \<open>id = kf_apply kf_id\<close>])
  by (auto simp: km_operators_in_kf_apply_flattened) 

lemma kraus_map_add[iff]:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>kraus_map (\<lambda>\<rho>. \<EE> \<rho> + \<FF> \<rho>)\<close>
proof -
  from assms obtain \<EE>' :: \<open>('a, 'b, unit) kraus_family\<close> where \<EE>': \<open>\<EE> = kf_apply \<EE>'\<close>
    using kraus_map_def by blast
  from assms obtain \<FF>' :: \<open>('a, 'b, unit) kraus_family\<close> where \<FF>': \<open>\<FF> = kf_apply \<FF>'\<close>
    using kraus_map_def by blast
  show ?thesis
    apply (rule kraus_mapI[of _ \<open>\<EE>' + \<FF>'\<close>])
    by (auto intro!: ext simp: \<EE>' \<FF>' kf_plus_apply')
qed

lemma kraus_map_plus'[iff]:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>kraus_map (\<EE> + \<FF>)\<close>
  using assms by (simp add: plus_fun_def)

lemma km_bound_plus:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>km_bound (\<EE> + \<FF>) = km_bound \<EE> + km_bound \<FF>\<close>
proof -
  from assms obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  from assms obtain FF :: \<open>('a,'b,unit) kraus_family\<close> where FF: \<open>\<FF> = kf_apply FF\<close>
    using kraus_map_def_raw by blast
  show ?thesis
    apply (rule km_bound_kf_bound[where \<FF>=\<open>EE + FF\<close>, THEN trans])
    by (auto intro!: ext simp: EE FF kf_plus_apply' kf_plus_bound' km_bound_kf_bound)
qed

lemma km_norm_triangle:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>km_norm (\<EE> + \<FF>) \<le> km_norm \<EE> + km_norm \<FF>\<close>
  by (simp add: km_norm_def km_bound_plus assms norm_triangle_ineq)


lemma kraus_map_constant[iff]: \<open>kraus_map (\<lambda>\<sigma>. trace_tc \<sigma> *\<^sub>C \<rho>)\<close> if \<open>\<rho> \<ge> 0\<close>
  apply (rule kraus_mapI[where \<EE>'=\<open>kf_constant \<rho>\<close>])
  by (simp add: kf_constant_apply[OF that, abs_def])

lemma kraus_map_constant_invalid: 
  \<open>\<not> kraus_map (\<lambda>\<sigma> :: ('a::{chilbert_space,not_singleton},'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>)\<close> if \<open>~ \<rho> \<ge> 0\<close>
proof (rule ccontr)
  assume \<open>\<not> \<not> kraus_map (\<lambda>\<sigma> :: ('a,'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>)\<close>
  then have km: \<open>kraus_map (\<lambda>\<sigma> :: ('a,'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>)\<close>
    by simp
  obtain h :: 'a where \<open>norm h = 1\<close>
    using ex_norm1_not_singleton by blast
  from km have \<open>trace_tc (tc_butterfly h h) *\<^sub>C \<rho> \<ge> 0\<close>
    using kraus_map_pos by fastforce
  with \<open>norm h = 1\<close>
  have \<open>\<rho> \<ge> 0\<close>
    by (metis mult_cancel_left2 norm_tc_butterfly norm_tc_pos of_real_1 scaleC_one tc_butterfly_pos)
  with that show False
    by simp
qed

lemma kraus_map_scale:
  assumes \<open>kraus_map \<EE>\<close> and \<open>c \<ge> 0\<close>
  shows \<open>kraus_map (\<lambda>\<rho>. c *\<^sub>R \<EE> \<rho>)\<close>
proof -
  from assms obtain \<EE>' :: \<open>('a, 'b, unit) kraus_family\<close> where \<EE>': \<open>\<EE> = kf_apply \<EE>'\<close>
  using kraus_map_def by blast
  then show ?thesis
    apply (rule_tac kraus_mapI[where \<EE>'=\<open>c *\<^sub>R \<EE>'\<close>])
    by (auto intro!: ext simp add: \<EE>' kf_scale_apply assms)
qed

lemma km_bound_scale[simp]: \<open>km_bound (\<lambda>\<rho>. c *\<^sub>R \<EE> \<rho>) = c *\<^sub>R km_bound \<EE>\<close> if \<open>c \<ge> 0\<close>
proof -
  consider (km) \<open>kraus_map \<EE>\<close> | (c0) \<open>c = 0\<close> | (not_km) \<open>\<not> kraus_map \<EE>\<close> \<open>c > 0\<close>
    using \<open>0 \<le> c\<close> by argo
  then show ?thesis
  proof cases
    case km
    then obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
      using kraus_map_def_raw by blast
    with \<open>c \<ge> 0 \<close>have \<open>kf_bound (c *\<^sub>R EE) = c *\<^sub>R kf_bound EE\<close>
      by simp
    then show ?thesis
      using km_bound_kf_bound[of \<open>\<lambda>\<rho>. c *\<^sub>R \<EE> \<rho>\<close> \<open>c *\<^sub>R EE\<close>, symmetric]
      using kf_scale_apply[OF \<open>c \<ge> 0\<close>, of EE, abs_def]
      by (simp add: EE km_bound_kf_bound)
  next
    case c0
    then show ?thesis
      by (simp flip: func_zero)
  next
    case not_km
    have \<open>\<not> kraus_map (\<lambda>\<rho>. c *\<^sub>R \<EE> \<rho>)\<close>
    proof (rule ccontr)
      assume \<open>\<not> \<not> kraus_map (\<lambda>\<rho>. c *\<^sub>R \<EE> \<rho>)\<close>
      then have \<open>kraus_map (\<lambda>\<rho>. inverse c *\<^sub>R (c *\<^sub>R \<EE> \<rho>))\<close>
        apply (rule_tac kraus_map_scale)
        using not_km by auto
      then have \<open>kraus_map \<EE>\<close>
        using not_km by (simp add: scaleR_scaleR field.field_inverse)
      with not_km show False
        by simp
    qed
    with not_km show ?thesis
      by (simp add: km_bound_invalid)
  qed
qed


lemma km_norm_scale[simp]: \<open>km_norm (\<lambda>\<rho>. c *\<^sub>R \<EE> \<rho>) = c * km_norm \<EE>\<close> if \<open>c \<ge> 0\<close>
  using that by (simp add: km_norm_def)



lemma kraus_map_sandwich[iff]: \<open>kraus_map (sandwich_tc A)\<close>
  apply (rule kraus_mapI[of _ \<open>kf_of_op A\<close>])
  using kf_of_op_apply[of A, abs_def]
  by simp

lemma km_bound_sandwich[simp]: \<open>km_bound (sandwich_tc A) = A* o\<^sub>C\<^sub>L A\<close>
  using km_bound_kf_bound[of \<open>sandwich_tc A\<close> \<open>kf_of_op A\<close>, symmetric]
  using kf_bound_of_op[of A]
  using kf_of_op_apply[of A]
  by fastforce

lemma km_norm_sandwich[simp]: \<open>km_norm (sandwich_tc A) = (norm A)\<^sup>2\<close>
  by (simp add: km_norm_def)

lemma km_operators_in_sandwich: \<open>km_operators_in (sandwich_tc U) {U}\<close>
  apply (subst kf_of_op_apply[abs_def, symmetric])
  apply (rule km_operators_in_kf_apply_flattened)
  by simp

lemma km_constant_bound[simp]: \<open>km_bound (\<lambda>\<sigma>. trace_tc \<sigma> *\<^sub>C \<rho>) = norm \<rho> *\<^sub>R id_cblinfun\<close> if \<open>\<rho> \<ge> 0\<close>
  apply (rule km_bound_kf_bound[THEN trans])
  using that apply (rule kf_constant_apply[symmetric, THEN ext])
  using that by (rule kf_bound_constant)

lemma km_constant_norm[simp]: \<open>km_norm (\<lambda>\<sigma>::('a::{chilbert_space,not_singleton},'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>) = norm \<rho>\<close> if \<open>\<rho> \<ge> 0\<close>
  apply (subst km_norm_kf_norm[of \<open>(\<lambda>\<sigma>::('a,'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>)\<close> \<open>kf_constant \<rho>\<close>])
   apply (subst kf_constant_apply[OF that, abs_def], rule refl)
  apply (rule kf_norm_constant)
  by (fact that)

lemma km_constant_norm_leq[simp]: \<open>km_norm (\<lambda>\<sigma>::('a::chilbert_space,'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>) \<le> norm \<rho>\<close>
proof -
  consider (pos) \<open>\<rho> \<ge> 0\<close> | (singleton) \<open>\<not> class.not_singleton TYPE('a)\<close> | (nonpos) \<open>\<not> \<rho> \<ge> 0\<close> \<open>class.not_singleton TYPE('a)\<close>
    by blast
  then show ?thesis
  proof cases
    case pos
    show ?thesis
      apply (subst km_norm_kf_norm[of \<open>(\<lambda>\<sigma>::('a,'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>)\<close> \<open>kf_constant \<rho>\<close>])
       apply (subst kf_constant_apply[OF pos, abs_def], rule refl)
      by (rule kf_norm_constant_leq)
  next
    case nonpos
    have \<open>\<not> kraus_map (\<lambda>\<sigma>::('a,'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>)\<close>
      apply (rule kraus_map_constant_invalid[internalize_sort' 'a])
        apply (rule chilbert_space_axioms)
      using nonpos by -
    then have \<open>km_norm (\<lambda>\<sigma>::('a,'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>) = 0\<close>
      using km_norm_invalid by blast
    then show ?thesis
      by (metis norm_ge_zero)
  next
    case singleton
    then have \<open>(\<lambda>\<sigma>::('a,'a) trace_class. trace_tc \<sigma> *\<^sub>C \<rho>) = 0\<close>
      apply (subst not_not_singleton_tc_zero)
      by auto
    then show ?thesis
      by simp
  qed
qed

lemma kraus_map_comp:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>kraus_map (\<EE> o \<FF>)\<close>
proof -
  from assms obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  from assms obtain FF :: \<open>('c,'a,unit) kraus_family\<close> where FF: \<open>\<FF> = kf_apply FF\<close>
    using kraus_map_def_raw by blast
  show ?thesis
    apply (rule kraus_mapI[where \<EE>'=\<open>kf_comp EE FF\<close>])
    by (simp add: EE FF kf_comp_apply)
qed

lemma km_comp_norm_leq:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>km_norm (\<EE> o \<FF>) \<le> km_norm \<EE> * km_norm \<FF>\<close>
proof -
  from assms obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  from assms obtain FF :: \<open>('c,'a,unit) kraus_family\<close> where FF: \<open>\<FF> = kf_apply FF\<close>
    using kraus_map_def_raw by blast
  have \<open>km_norm (\<EE> o \<FF>) = kf_norm (kf_comp EE FF)\<close>
    by (simp add: EE FF kf_comp_apply km_norm_kf_norm)
  also have \<open>\<dots> \<le> kf_norm EE * kf_norm FF\<close>
    by (simp add: kf_comp_norm_leq)
  also have \<open>\<dots> = km_norm \<EE> * km_norm \<FF>\<close>
    by (simp add: EE FF km_norm_kf_norm)
  finally show ?thesis
    by -
qed

lemma km_bound_comp_sandwich:
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>km_bound (\<lambda>\<rho>. \<EE> (sandwich_tc U \<rho>)) = sandwich (U*) (km_bound \<EE>)\<close>
proof -
  from assms obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  have \<open>km_bound (\<lambda>\<rho>. \<EE> (sandwich_tc U \<rho>)) = kf_bound (kf_comp EE (kf_of_op U))\<close>
    apply (rule km_bound_kf_bound)
    by (simp add: kf_comp_apply o_def EE kf_of_op_apply)
  also have \<open>\<dots> = sandwich (U*) *\<^sub>V kf_bound EE\<close>
    by (simp add: kf_bound_comp_of_op)
  also have \<open>\<dots> = sandwich (U*) (km_bound \<EE>)\<close>
    by (simp add: EE km_bound_kf_bound)
  finally show ?thesis
    by -
qed

(* lemma sandwich_tc_compose: \<open>sandwich_tc A (sandwich_tc B \<rho>) = sandwich_tc (A o\<^sub>C\<^sub>L B) \<rho>\<close>
  apply transfer'
  by (simp add: sandwich_compose) *)



lemma km_norm_comp_sandwich_coiso:
  assumes \<open>isometry (U*)\<close>
  shows \<open>km_norm (\<lambda>\<rho>. \<EE> (sandwich_tc U \<rho>)) = km_norm \<EE>\<close>
proof (cases \<open>kraus_map \<EE>\<close>)
  case True
  then obtain EE :: \<open>(_,_,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  have \<open>km_norm (\<lambda>\<rho>. \<EE> (sandwich_tc U \<rho>)) = kf_norm (kf_comp EE (kf_of_op U))\<close>
    apply (rule km_norm_kf_norm)
    by (auto intro!: simp: kf_comp_apply o_def EE kf_of_op_apply)
  also have \<open>\<dots> = kf_norm EE\<close>
    by (simp add: assms kf_norm_comp_of_op_coiso)
  also have \<open>\<dots> = km_norm \<EE>\<close>
    by (simp add: EE km_norm_kf_norm)
  finally show ?thesis
    by -
next
  case False
  have \<open>\<not> kraus_map (\<lambda>\<rho>. \<EE> (sandwich_tc U \<rho>))\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<not> kraus_map (\<lambda>\<rho>. \<EE> (sandwich_tc U \<rho>))\<close>
    then have \<open>kraus_map (\<lambda>\<rho>. \<EE> (sandwich_tc U \<rho>))\<close>
      by blast
    then have \<open>kraus_map (\<lambda>\<rho>. \<EE> (sandwich_tc U (sandwich_tc (U*) \<rho>)))\<close>
      apply (rule kraus_map_comp[unfolded o_def])
      by fastforce
    then have \<open>kraus_map \<EE>\<close>
      using isometryD[OF assms]
      by (simp flip: sandwich_tc_compose[unfolded o_def, THEN fun_cong])
    then show False
      using False by blast
  qed
  with False show ?thesis
    by (simp add: km_norm_invalid)
qed

lemma km_bound_comp_sandwich_iso:
  assumes \<open>isometry U\<close>
  shows \<open>km_bound (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>)) = km_bound \<EE>\<close>
proof (cases \<open>kraus_map \<EE>\<close>)
  case True
  then obtain EE :: \<open>(_,_,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  have \<open>km_bound (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>)) = kf_bound (kf_comp (kf_of_op U) EE)\<close>
    apply (rule km_bound_kf_bound)
    by (auto intro!: simp: kf_comp_apply o_def EE kf_of_op_apply)
  also have \<open>\<dots> = kf_bound EE\<close>
    by (simp add: assms kf_bound_comp_iso)
  also have \<open>\<dots> = km_bound \<EE>\<close>
    by (simp add: EE km_bound_kf_bound)
  finally show ?thesis
    by -
next
  case False
  have \<open>\<not> kraus_map (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>))\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<not> kraus_map (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>))\<close>
    then have \<open>kraus_map (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>))\<close>
      by blast
    then have \<open>kraus_map (\<lambda>\<rho>. sandwich_tc (U*) (sandwich_tc U (\<EE> \<rho>)))\<close>
      apply (rule kraus_map_comp[unfolded o_def, rotated])
      by fastforce
    then have \<open>kraus_map \<EE>\<close>
      using isometryD[OF assms]
      by (simp flip: sandwich_tc_compose[unfolded o_def, THEN fun_cong])
    then show False
      using False by blast
  qed
  with False show ?thesis
    by (simp add: km_bound_invalid)
qed

lemma km_norm_comp_sandwich_iso:
  assumes \<open>isometry U\<close>
  shows \<open>km_norm (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>)) = km_norm \<EE>\<close>
proof (cases \<open>kraus_map \<EE>\<close>)
  case True
  then obtain EE :: \<open>(_,_,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  have \<open>km_norm (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>)) = kf_norm (kf_comp (kf_of_op U) EE)\<close>
    apply (rule km_norm_kf_norm)
    by (auto intro!: simp: kf_comp_apply o_def EE kf_of_op_apply)
  also have \<open>\<dots> = kf_norm EE\<close>
    by (simp add: assms kf_norm_comp_iso)
  also have \<open>\<dots> = km_norm \<EE>\<close>
    by (simp add: EE km_norm_kf_norm)
  finally show ?thesis
    by -
next
  case False
  have \<open>\<not> kraus_map (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>))\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<not> kraus_map (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>))\<close>
    then have \<open>kraus_map (\<lambda>\<rho>. sandwich_tc U (\<EE> \<rho>))\<close>
      by blast
    then have \<open>kraus_map (\<lambda>\<rho>. sandwich_tc (U*) (sandwich_tc U (\<EE> \<rho>)))\<close>
      apply (rule kraus_map_comp[unfolded o_def, rotated])
      by fastforce
    then have \<open>kraus_map \<EE>\<close>
      using isometryD[OF assms]
      by (simp flip: sandwich_tc_compose[unfolded o_def, THEN fun_cong])
    then show False
      using False by blast
  qed
  with False show ?thesis
    by (simp add: km_norm_invalid)
qed


lemma kraus_map_sum:
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> kraus_map (\<EE> x)\<close>
  shows \<open>kraus_map (\<Sum>x\<in>A. \<EE> x)\<close>
  apply (insert assms, induction A rule:infinite_finite_induct)
  by auto

lemma km_bound_sum:
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> kraus_map (\<EE> x)\<close>
  shows \<open>km_bound (\<Sum>x\<in>A. \<EE> x) = (\<Sum>x\<in>A. km_bound (\<EE> x))\<close>
proof (insert assms, induction A rule:infinite_finite_induct)
  case (infinite A)
  then show ?case
    by (metis km_bound_0 sum.infinite)
next
  case empty
  then show ?case
    by (metis km_bound_0 sum.empty)
next
  case (insert x F)
  have \<open>km_bound (\<Sum>x\<in>insert x F. \<EE> x) = km_bound (\<EE> x + (\<Sum>x\<in>F. \<EE> x))\<close>
    by (simp add: insert.hyps)
  also have \<open>\<dots> = km_bound (\<EE> x) + km_bound (\<Sum>x\<in>F. \<EE> x)\<close>
    by (simp add: km_bound_plus kraus_map_sum insert.prems)
  also have \<open>\<dots> = km_bound (\<EE> x) + (\<Sum>x\<in>F. km_bound (\<EE> x))\<close>
    by (simp add: insert)
  also have \<open>\<dots> = (\<Sum>x\<in>insert x F. km_bound (\<EE> x))\<close>
    using insert.hyps by fastforce
  finally show ?case
    by -
qed




subsection \<open>Infinite sums\<close>

lemma
  assumes \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum \<EE> \<rho>) A\<close>
  defines \<open>EE \<equiv> Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>a. (f a, a)) ` A)\<close>
  shows kraus_mapI_sum: \<open>kraus_map \<EE>\<close>
    and kraus_map_sum_kraus_family: \<open>kraus_family EE\<close>
    and kraus_map_sum_kf_apply: \<open>\<EE> = kf_apply (Abs_kraus_family EE)\<close>
proof -
  show \<open>kraus_family EE\<close>
    unfolding EE_def
    apply (rule kf_reconstruction_is_kraus_family)
    by (fact assms(1))
  show \<open>\<EE> = kf_apply (Abs_kraus_family EE)\<close>
    unfolding EE_def
    apply (rule kf_reconstruction[symmetric])
    by (fact assms(1))
  then show \<open>kraus_map \<EE>\<close>
    by (rule kraus_mapI)
qed


lemma kraus_map_infsum_sandwich: 
  assumes \<open>\<And>\<rho>. (\<lambda>a. sandwich_tc (f a) \<rho>) summable_on A\<close>
  shows \<open>kraus_map (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>a\<in>A. sandwich_tc (f a) \<rho>)\<close>
  apply (rule kraus_mapI_sum)
  using assms by (rule has_sum_infsum)

lemma kraus_map_sum_sandwich: \<open>kraus_map (\<lambda>\<rho>. \<Sum>a\<in>A. sandwich_tc (f a) \<rho>)\<close>
  apply (cases \<open>finite A\<close>)
   apply (simp add: kraus_map_infsum_sandwich flip: infsum_finite)
  by simp


lemma kraus_map_as_infsum:
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>\<exists>M. \<forall>\<rho>. ((\<lambda>E. sandwich_tc E \<rho>) has_sum \<EE> \<rho>) M\<close>
proof -
  from assms obtain \<EE>' :: \<open>('a, 'b, unit) kraus_family\<close> where \<EE>': \<open>\<EE> = kf_apply \<EE>'\<close>
    using kraus_map_def by blast
  define M where \<open>M = fst ` Rep_kraus_family \<EE>'\<close>
  have \<open>((\<lambda>E. sandwich_tc E \<rho>) has_sum \<EE> \<rho>) M\<close> for \<rho>
  proof -
    have [simp]: \<open>inj_on fst (Rep_kraus_family \<EE>')\<close>
      by (auto intro!: inj_onI)
    from kf_apply_has_sum[of \<rho> \<EE>']
    have \<open>((\<lambda>(E, x). sandwich_tc E \<rho>) has_sum kf_apply \<EE>' \<rho>) (Rep_kraus_family \<EE>')\<close>
      by -
    then show ?thesis
      by (simp add: M_def has_sum_reindex o_def case_prod_unfold \<EE>')
  qed
  then show ?thesis
    by auto
qed



definition km_summable :: \<open>('a \<Rightarrow> ('b::chilbert_space,'b) trace_class \<Rightarrow> ('c::chilbert_space,'c) trace_class) \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>km_summable \<EE> A \<longleftrightarrow> summable_on_in cweak_operator_topology (\<lambda>a. km_bound (\<EE> a)) A\<close>

lemma km_summable_kf_summable:
  assumes \<open>\<And>a \<rho>. a \<in> A \<Longrightarrow> \<EE> a \<rho> = \<FF> a *\<^sub>k\<^sub>r \<rho>\<close>
  shows \<open>km_summable \<EE> A \<longleftrightarrow> kf_summable \<FF> A\<close>
proof -
  have \<open>km_summable \<EE> A \<longleftrightarrow> summable_on_in cweak_operator_topology (\<lambda>a. km_bound (\<EE> a)) A\<close>
    using km_summable_def by blast
  also have \<open>\<dots> \<longleftrightarrow> summable_on_in cweak_operator_topology (\<lambda>a. kf_bound (\<FF> a)) A\<close>
    apply (rule summable_on_in_cong)
    apply (rule km_bound_kf_bound)
    using assms by fastforce
  also have \<open>\<dots> \<longleftrightarrow> kf_summable \<FF> A\<close>
    using kf_summable_def by blast
  finally show ?thesis
    by -
qed

lemma km_summable_summable:
  assumes km: \<open>\<And>a. a\<in>A \<Longrightarrow> kraus_map (\<EE> a)\<close>
  assumes sum: \<open>km_summable \<EE> A\<close>
  shows \<open>(\<lambda>a. \<EE> a \<rho>) summable_on A\<close>
proof -
  from km
  obtain EE :: \<open>_ \<Rightarrow> (_,_,unit) kraus_family\<close> where EE: \<open>\<EE> a = kf_apply (EE a)\<close> if \<open>a \<in> A\<close> for a
    apply atomize_elim
    apply (rule_tac choice)
    by (simp add: kraus_map_def_raw) 
  from sum
  have \<open>kf_summable EE A\<close>
    by (simp add: EE km_summable_kf_summable)
  then have \<open>(\<lambda>a. EE a *\<^sub>k\<^sub>r \<rho>) summable_on A\<close>
    by (rule kf_infsum_apply_summable)
  then show ?thesis
    by (metis (mono_tags, lifting) EE summable_on_cong)
qed


lemma kraus_map_infsum:
  assumes km: \<open>\<And>a. a\<in>A \<Longrightarrow> kraus_map (\<EE> a)\<close>
  assumes sum: \<open>km_summable \<EE> A\<close>
  shows \<open>kraus_map (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a \<rho>)\<close>
proof -
  from km
  obtain EE :: \<open>_ \<Rightarrow> (_,_,unit) kraus_family\<close> where EE: \<open>\<EE> a = kf_apply (EE a)\<close> if \<open>a \<in> A\<close> for a
    apply atomize_elim
    apply (rule_tac choice)
    by (simp add: kraus_map_def_raw) 
  from sum
  have \<open>kf_summable EE A\<close>
    by (simp add: EE km_summable_kf_summable)
  then have \<open>kf_infsum EE A *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>a\<in>A. EE a *\<^sub>k\<^sub>r \<rho>)\<close> for \<rho>
    by (metis kf_infsum_apply)
  also have \<open>\<dots> \<rho> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a \<rho>)\<close> for \<rho>
    by (metis (mono_tags, lifting) EE infsum_cong)
  finally show ?thesis
    apply (rule_tac kraus_mapI[of _ \<open>kf_infsum EE A\<close>])
    by auto
qed

lemma km_bound_infsum:
  assumes km: \<open>\<And>a. a\<in>A \<Longrightarrow> kraus_map (\<EE> a)\<close>
  assumes sum: \<open>km_summable \<EE> A\<close>
  shows \<open>km_bound (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a \<rho>) = infsum_in cweak_operator_topology (\<lambda>a. km_bound (\<EE> a)) A\<close>
proof -
  from km
  obtain EE :: \<open>_ \<Rightarrow> (_,_,unit) kraus_family\<close> where EE: \<open>\<EE> a = kf_apply (EE a)\<close> if \<open>a \<in> A\<close> for a
    apply atomize_elim
    apply (rule_tac choice)
    by (simp add: kraus_map_def_raw) 
  from sum have \<open>kf_summable EE A\<close>
    by (simp add: EE km_summable_kf_summable)
  have \<open>km_bound (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a \<rho>) = km_bound (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>a\<in>A. EE a *\<^sub>k\<^sub>r \<rho>)\<close>
    apply (rule arg_cong[where f=km_bound])
    by (auto intro!: infsum_cong simp add: EE)
  also have \<open>\<dots> = kf_bound (kf_infsum EE A)\<close>
    apply (rule km_bound_kf_bound)
    using kf_infsum_apply[OF \<open>kf_summable EE A\<close>]
    by auto
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>a. kf_bound (EE a)) A\<close>
    using \<open>kf_summable EE A\<close> kf_bound_infsum by fastforce
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>a. km_bound (\<EE> a)) A\<close>
    by (metis (mono_tags, lifting) EE infsum_in_cong km_bound_kf_bound)
  finally show ?thesis
    by -
qed


lemma km_norm_infsum:
  assumes km: \<open>\<And>a. a\<in>A \<Longrightarrow> kraus_map (\<EE> a)\<close>
  assumes sum: \<open>(\<lambda>a. km_norm (\<EE> a)) summable_on A\<close>
  shows \<open>km_norm (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a \<rho>) \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. km_norm (\<EE> a))\<close>
proof -
  from km
  obtain EE :: \<open>_ \<Rightarrow> (_,_,unit) kraus_family\<close> where EE: \<open>\<EE> a = kf_apply (EE a)\<close> if \<open>a \<in> A\<close> for a
    apply atomize_elim
    apply (rule_tac choice)
    by (simp add: kraus_map_def_raw) 
  from sum have sum1: \<open>(\<lambda>a. kf_norm (EE a)) summable_on A\<close>
    by (metis (mono_tags, lifting) EE km_norm_kf_norm summable_on_cong)
  then have sum2: \<open>kf_summable EE A\<close>
    using kf_summable_from_abs_summable by blast
  have \<open>km_norm (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a \<rho>) = km_norm (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>a\<in>A. EE a *\<^sub>k\<^sub>r \<rho>)\<close>
    apply (rule arg_cong[where f=km_norm])
    apply (rule ext)
    apply (rule infsum_cong)
    by (simp add: EE)
  also have \<open>\<dots> = kf_norm (kf_infsum EE A)\<close>
    apply (subst kf_infsum_apply[OF sum2, abs_def, symmetric])
    using km_norm_kf_norm by blast
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. kf_norm (EE a))\<close>
    by (metis kf_norm_infsum sum1)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. km_norm (\<EE> a))\<close>
    by (metis (mono_tags, lifting) EE infsum_cong km_norm_kf_norm)
  finally show ?thesis
    by -
qed

lemma kraus_map_has_sum:
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> kraus_map (\<EE> x)\<close>
  assumes \<open>km_summable \<EE> A\<close>
  assumes \<open>(\<EE> has_sum \<FF>) A\<close>
  shows \<open>kraus_map \<FF>\<close>
proof -
  from \<open>(\<EE> has_sum \<FF>) A\<close>
  have \<open>((\<lambda>x. \<EE> x t) has_sum \<FF> t) A\<close> for t
    by (simp add: has_sum_coordinatewise)
  then have \<open>\<FF> t = (\<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a t)\<close> for t
    by (metis infsumI)
  with kraus_map_infsum[OF assms(1,2)]
  show \<open>kraus_map \<FF>\<close>
    by presburger
qed

lemma km_summable_iff_sums_to_kraus_map:
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> kraus_map (\<EE> a)\<close>
  shows \<open>km_summable \<EE> A \<longleftrightarrow> (\<exists>\<FF>. (\<forall>t. ((\<lambda>x. \<EE> x t) has_sum \<FF> t) A) \<and> kraus_map \<FF>)\<close>
proof (rule iffI)
  assume asm: \<open>km_summable \<EE> A\<close>
  define \<FF> where \<open>\<FF> t = (\<Sum>\<^sub>\<infinity>a\<in>A. \<EE> a t)\<close> for t
  from km_summable_summable[OF assms asm]
  have \<open>((\<lambda>x. \<EE> x t) has_sum \<FF> t) A\<close> for t
    using \<FF>_def by fastforce
  moreover from kraus_map_infsum[OF assms asm]
  have \<open>kraus_map \<FF>\<close>
    by (simp add: \<FF>_def[abs_def])
  ultimately show \<open>(\<exists>\<FF>. (\<forall>t. ((\<lambda>x. \<EE> x t) has_sum \<FF> t) A) \<and> kraus_map \<FF>)\<close>
    by auto
next
  assume \<open>\<exists>\<FF>. (\<forall>t. ((\<lambda>x. \<EE> x t) has_sum \<FF> t) A) \<and> kraus_map \<FF>\<close>
  then obtain \<FF> where \<open>kraus_map \<FF>\<close> and \<open>((\<lambda>x. \<EE> x t) has_sum \<FF> t) A\<close> for t
    by auto
  then have \<open>((\<lambda>x. trace_tc (\<EE> x (tc_butterfly k h))) has_sum trace_tc (\<FF> (tc_butterfly k h))) A\<close> for h k
    using bounded_clinear.bounded_linear bounded_clinear_trace_tc has_sum_bounded_linear by blast
  then have \<open>((\<lambda>x. trace_tc (\<EE> x (tc_butterfly k h))) has_sum h \<bullet>\<^sub>C (km_bound \<FF> *\<^sub>V k)) A\<close> for h k
    by (simp add: km_bound_from_map \<open>kraus_map \<FF>\<close>)
  then have \<open>((\<lambda>x. h \<bullet>\<^sub>C (km_bound (\<EE> x) *\<^sub>V k)) has_sum h \<bullet>\<^sub>C (km_bound \<FF> *\<^sub>V k)) A\<close> for h k
    apply (rule has_sum_cong[THEN iffD1, rotated 1])
    by (simp add: km_bound_from_map assms)
  then have \<open>has_sum_in cweak_operator_topology (\<lambda>a. km_bound (\<EE> a)) A (km_bound \<FF>)\<close>
    by (simp add: has_sum_in_cweak_operator_topology_pointwise)
  then show \<open>km_summable \<EE> A\<close>
    using  summable_on_in_def km_summable_def by blast
qed





subsection \<open>Tensor products\<close>

definition km_tensor_exists :: \<open>(('a ell2, 'b ell2) trace_class \<Rightarrow> ('c ell2, 'd ell2) trace_class)
                             \<Rightarrow> (('e ell2, 'f ell2) trace_class \<Rightarrow> ('g ell2, 'h ell2) trace_class) \<Rightarrow> bool\<close> where
  \<open>km_tensor_exists \<EE> \<FF> \<longleftrightarrow> (\<exists>\<EE>\<FF>. bounded_clinear \<EE>\<FF> \<and> (\<forall>\<rho> \<sigma>. \<EE>\<FF> (tc_tensor \<rho> \<sigma>) = tc_tensor (\<EE> \<rho>) (\<FF> \<sigma>)))\<close>


definition km_tensor :: \<open>(('a ell2, 'c ell2) trace_class \<Rightarrow> ('e ell2, 'g ell2) trace_class)
                      \<Rightarrow> (('b ell2, 'd ell2) trace_class \<Rightarrow> ('f ell2, 'h ell2) trace_class)
                      \<Rightarrow> (('a \<times> 'b) ell2, ('c \<times> 'd) ell2) trace_class \<Rightarrow> (('e \<times> 'f) ell2, ('g \<times> 'h) ell2) trace_class\<close> where
  \<open>km_tensor \<EE> \<FF> = (if km_tensor_exists \<EE> \<FF>
                    then SOME \<EE>\<FF>. bounded_clinear \<EE>\<FF> \<and> (\<forall>\<rho> \<sigma>. \<EE>\<FF> (tc_tensor \<rho> \<sigma>) = tc_tensor (\<EE> \<rho>) (\<FF> \<sigma>))
                    else 0)\<close>

lemma km_tensor_invalid:
  assumes \<open>\<not> km_tensor_exists \<EE> \<FF>\<close>
  shows \<open>km_tensor \<EE> \<FF> = 0\<close>
  by (simp add: assms km_tensor_def)


lemma km_tensor_exists_bounded_clinear[iff]:
  assumes \<open>km_tensor_exists \<EE> \<FF>\<close>
  shows \<open>bounded_clinear (km_tensor \<EE> \<FF>)\<close>
  unfolding km_tensor_def
  apply (rule someI2_ex[where P=\<open>\<lambda>\<EE>\<FF>. bounded_clinear \<EE>\<FF> \<and> (\<forall>\<rho> \<sigma>. \<EE>\<FF> (tc_tensor \<rho> \<sigma>) = tc_tensor (\<EE> \<rho>) (\<FF> \<sigma>))\<close>])
  using assms
  by (simp_all add: km_tensor_exists_def)

lemma km_tensor_apply[simp]:
  assumes \<open>km_tensor_exists \<EE> \<FF>\<close>
  shows \<open>km_tensor \<EE> \<FF> (tc_tensor \<rho> \<sigma>) = tc_tensor (\<EE> \<rho>) (\<FF> \<sigma>)\<close>
  unfolding km_tensor_def
  apply (rule someI2_ex[where P=\<open>\<lambda>\<EE>\<FF>. bounded_clinear \<EE>\<FF> \<and> (\<forall>\<rho> \<sigma>. \<EE>\<FF> (tc_tensor \<rho> \<sigma>) = tc_tensor (\<EE> \<rho>) (\<FF> \<sigma>))\<close>])
  using assms
  by (simp_all add: km_tensor_exists_def)

lemma km_tensor_unique:
  assumes \<open>bounded_clinear \<EE>\<FF>\<close>
  assumes \<open>\<And>\<rho> \<sigma>. \<EE>\<FF> (tc_tensor \<rho> \<sigma>) = tc_tensor (\<EE> \<rho>) (\<FF> \<sigma>)\<close>
  shows \<open>\<EE>\<FF> = km_tensor \<EE> \<FF>\<close>
proof -
  define P where \<open>P \<EE>\<FF> \<longleftrightarrow> bounded_clinear \<EE>\<FF> \<and> (\<forall>\<rho> \<sigma>. \<EE>\<FF> (tc_tensor \<rho> \<sigma>) = tc_tensor (\<EE> \<rho>) (\<FF> \<sigma>))\<close> for \<EE>\<FF>
  have \<open>P \<EE>\<FF>\<close>
    using P_def assms by presburger
  then have \<open>km_tensor_exists \<EE> \<FF>\<close>
    using P_def km_tensor_exists_def by blast
  with \<open>P \<EE>\<FF>\<close> have Ptensor: \<open>P (km_tensor \<EE> \<FF>)\<close>
    by (simp add: P_def)
  show ?thesis
    apply (rule eq_from_separatingI2)
       apply (rule separating_set_bounded_clinear_tc_tensor)
    using assms Ptensor by (simp_all add: P_def)
qed

lemma km_tensor_kf_tensor: \<open>km_tensor (kf_apply \<EE>) (kf_apply \<FF>) = kf_apply (kf_tensor \<EE> \<FF>)\<close>
  by (metis kf_apply_bounded_clinear kf_apply_tensor km_tensor_unique)

lemma km_tensor_kraus_map:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>kraus_map (km_tensor \<EE> \<FF>)\<close>
proof -
  from assms obtain EE :: \<open>(_,_,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  from assms obtain FF :: \<open>(_,_,unit) kraus_family\<close> where FF: \<open>\<FF> = kf_apply FF\<close>
    using kraus_map_def_raw by blast
  show ?thesis
    by (simp add: EE FF km_tensor_kf_tensor)
qed

lemma km_tensor_kraus_map_exists: 
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>km_tensor_exists \<EE> \<FF>\<close>
proof -
  from assms obtain EE :: \<open>(_,_,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  from assms obtain FF :: \<open>(_,_,unit) kraus_family\<close> where FF: \<open>\<FF> = kf_apply FF\<close>
    using kraus_map_def_raw by blast
  show ?thesis
    using EE FF kf_apply_bounded_clinear kf_apply_tensor km_tensor_exists_def by blast
qed

lemma km_tensor_as_infsum:
  assumes \<open>\<And>\<rho>. ((\<lambda>i. sandwich_tc (E i) \<rho>) has_sum \<EE> \<rho>) I\<close>
  assumes \<open>\<And>\<rho>. ((\<lambda>j. sandwich_tc (F j) \<rho>) has_sum \<FF> \<rho>) J\<close>
  shows \<open>km_tensor \<EE> \<FF> \<rho> = (\<Sum>\<^sub>\<infinity>(i,j)\<in>I\<times>J. sandwich_tc (E i \<otimes>\<^sub>o F j) \<rho>)\<close>
proof -
  define EE FF where \<open>EE = Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>a. (E a, a)) ` I)\<close> and \<open>FF = Set.filter (\<lambda>(E,_). E\<noteq>0) ((\<lambda>a. (F a, a)) ` J)\<close>
  then have [simp]: \<open>kraus_family EE\<close>  \<open>kraus_family FF\<close>
    using assms kraus_map_sum_kraus_family
    by blast+
  have \<open>\<EE> = kf_apply (Abs_kraus_family EE)\<close> and \<open>\<FF> = kf_apply (Abs_kraus_family FF)\<close>
    using assms kraus_map_sum_kf_apply EE_def FF_def
    by blast+
  then have \<open>km_tensor \<EE> \<FF> \<rho> = kf_apply (kf_tensor (Abs_kraus_family EE) (Abs_kraus_family FF)) \<rho>\<close>
    by (simp add: km_tensor_kf_tensor)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E, x), (F, y))\<in>EE \<times> FF. sandwich_tc (E \<otimes>\<^sub>o F) \<rho>)\<close>
    by (simp add: kf_apply_tensor_as_infsum Abs_kraus_family_inverse)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E, x), (F, y))\<in>(\<lambda>(i,j). ((E i, i), (F j, j)))`(I\<times>J). sandwich_tc (E \<otimes>\<^sub>o F) \<rho>)\<close>
    apply (rule infsum_cong_neutral)
    by (auto simp: EE_def FF_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(i,j)\<in>I\<times>J. sandwich_tc (E i \<otimes>\<^sub>o F j) \<rho>)\<close>
    by (simp add: infsum_reindex inj_on_def o_def case_prod_unfold)
  finally show ?thesis
    by -
qed

lemma km_bound_tensor:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>km_bound (km_tensor \<EE> \<FF>) = km_bound \<EE> \<otimes>\<^sub>o km_bound \<FF>\<close>
proof -
  from assms obtain EE :: \<open>(_,_,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  from assms obtain FF :: \<open>(_,_,unit) kraus_family\<close> where FF: \<open>\<FF> = kf_apply FF\<close>
    using kraus_map_def_raw by blast
  show ?thesis
    by (simp add: EE FF km_tensor_kf_tensor kf_bound_tensor km_bound_kf_bound)
qed

lemma km_norm_tensor:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>km_norm (km_tensor \<EE> \<FF>) = km_norm \<EE> * km_norm \<FF>\<close>
proof -
  from assms obtain EE :: \<open>(_,_,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  from assms obtain FF :: \<open>(_,_,unit) kraus_family\<close> where FF: \<open>\<FF> = kf_apply FF\<close>
    using kraus_map_def_raw by blast
  show ?thesis
    by (simp add: EE FF km_tensor_kf_tensor kf_norm_tensor km_norm_kf_norm)
qed

lemma km_tensor_compose_distrib:
  assumes \<open>km_tensor_exists \<EE> \<GG>\<close> and \<open>km_tensor_exists \<FF> \<HH>\<close>
  shows \<open>km_tensor (\<EE> o \<FF>) (\<GG> o \<HH>) = km_tensor \<EE> \<GG> o km_tensor \<FF> \<HH>\<close>
  by (smt (verit, del_insts) assms(1,2) comp_bounded_clinear km_tensor_exists_def km_tensor_unique o_apply)

lemma kraus_map_tensor_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_map (\<lambda>\<sigma>. tc_tensor \<sigma> \<rho>)\<close>
  apply (rule kraus_mapI[of _ \<open>kf_tensor_right \<rho>\<close>])
  by (auto intro!: ext simp: kf_apply_tensor_right assms)
lemma kraus_map_tensor_left[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_map (\<lambda>\<sigma>. tc_tensor \<rho> \<sigma>)\<close>
  apply (rule kraus_mapI[of _ \<open>kf_tensor_left \<rho>\<close>])
  by (auto intro!: ext simp: kf_apply_tensor_left assms)


lemma km_bound_tensor_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>km_bound (\<lambda>\<sigma>. tc_tensor \<sigma> \<rho>) = norm \<rho> *\<^sub>C id_cblinfun\<close>
  apply (subst km_bound_kf_bound)
   apply (rule ext)
   apply (subst kf_apply_tensor_right[OF assms])
  by (auto intro!: simp: kf_bound_tensor_right assms)
lemma km_bound_tensor_left[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>km_bound (\<lambda>\<sigma>. tc_tensor \<rho> \<sigma>) = norm \<rho> *\<^sub>C id_cblinfun\<close>
  apply (subst km_bound_kf_bound)
   apply (rule ext)
   apply (subst kf_apply_tensor_left[OF assms])
  by (auto intro!: simp: kf_bound_tensor_left assms)

lemma kf_norm_tensor_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>km_norm (\<lambda>\<sigma>. tc_tensor \<sigma> \<rho>) = norm \<rho>\<close>
  by (simp add: km_norm_def km_bound_tensor_right assms)

lemma kf_norm_tensor_left[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>km_norm (\<lambda>\<sigma>. tc_tensor \<rho> \<sigma>) = norm \<rho>\<close>
  by (simp add: km_norm_def km_bound_tensor_left assms)

lemma km_operators_in_tensor:
  assumes \<open>km_operators_in \<EE> S\<close>
  assumes \<open>km_operators_in \<FF> T\<close>
  shows \<open>km_operators_in (km_tensor \<EE> \<FF>) (span {s \<otimes>\<^sub>o t | s t. s\<in>S \<and> t\<in>T})\<close>
proof -
  have [iff]: \<open>inj_on (\<lambda>((),()). ()) X\<close> for X
    by (simp add: inj_on_def)
  from assms obtain \<EE>' :: \<open>(_,_,unit) kraus_family\<close> where \<EE>_def: \<open>\<EE> = kf_apply \<EE>'\<close> and \<EE>'S: \<open>kf_operators \<EE>' \<subseteq> S\<close>
    by (metis km_operators_in_def)
  from assms obtain \<FF>' :: \<open>(_,_,unit) kraus_family\<close> where \<FF>_def: \<open>\<FF> = kf_apply \<FF>'\<close> and \<FF>'T: \<open>kf_operators \<FF>' \<subseteq> T\<close>
    by (metis km_operators_in_def)
  define \<EE>\<FF> where \<open>\<EE>\<FF> = kf_map_inj (\<lambda>((),()). ()) (kf_tensor \<EE>' \<FF>')\<close>
  then have \<open>kf_operators \<EE>\<FF> = kf_operators (kf_tensor \<EE>' \<FF>')\<close>
    by (simp add: \<EE>\<FF>_def)
  also have \<open>kf_operators (kf_tensor \<EE>' \<FF>') \<subseteq> span {E \<otimes>\<^sub>o F | E F. E \<in> kf_operators \<EE>' \<and> F \<in> kf_operators \<FF>'}\<close>
    using kf_operators_tensor by force
  also have \<open>\<dots> \<subseteq> span {E \<otimes>\<^sub>o F | E F. E \<in> S \<and> F \<in> T}\<close>
    by (smt (verit) Collect_mono_iff \<EE>'S \<FF>'T span_mono subset_iff)
  finally have \<open>kf_operators \<EE>\<FF> \<subseteq> span {s \<otimes>\<^sub>o t |s t. s \<in> S \<and> t \<in> T}\<close>
    using \<EE>\<FF>_def by blast
  moreover have \<open>kf_apply \<EE>\<FF> = km_tensor \<EE> \<FF>\<close>
    by (simp add: \<EE>\<FF>_def \<EE>_def \<FF>_def kf_apply_bounded_clinear kf_apply_tensor km_tensor_unique)
  ultimately show ?thesis
    by (auto intro!: exI[of _ \<EE>\<FF>] simp add: km_operators_in_def)
qed

lemma km_tensor_sandwich_tc:
  \<open>km_tensor (sandwich_tc A) (sandwich_tc B) = sandwich_tc (A \<otimes>\<^sub>o B)\<close>
  by (metis bounded_clinear_sandwich_tc km_tensor_unique sandwich_tc_tensor)

subsection \<open>Trace and partial trace\<close>


definition \<open>km_trace_preserving \<EE> \<longleftrightarrow> (\<exists>\<FF>::(_,_,unit) kraus_family. \<EE> = kf_apply \<FF> \<and> kf_trace_preserving \<FF>)\<close>
lemma km_trace_preserving_def': \<open>km_trace_preserving \<EE> \<longleftrightarrow> (\<exists>\<FF>::(_, _, 'c) kraus_family. \<EE> = kf_apply \<FF> \<and> kf_trace_preserving \<FF>)\<close>
  \<comment> \<open>Has a more general type than @{thm [source] km_trace_preserving_def}\<close>
proof (rule iffI)
  assume \<open>km_trace_preserving \<EE>\<close>
  then obtain \<FF> :: \<open>(_,_,unit) kraus_family\<close> where \<EE>\<FF>: \<open>\<EE> = kf_apply \<FF>\<close> and tp\<FF>: \<open>kf_trace_preserving \<FF>\<close>
    using km_trace_preserving_def by blast
  from \<EE>\<FF> have \<open>\<EE> = kf_apply (kf_map (\<lambda>_. undefined :: 'c) \<FF>)\<close>
    by simp
  moreover from tp\<FF> have \<open>kf_trace_preserving (kf_map (\<lambda>_. undefined :: 'c) \<FF>)\<close>
    by (metis \<EE>\<FF> calculation kf_trace_preserving_iff_bound_id km_bound_kf_bound)
  ultimately show \<open>\<exists>\<FF>::(_, _, 'c) kraus_family. \<EE> = (*\<^sub>k\<^sub>r) \<FF> \<and> kf_trace_preserving \<FF>\<close>
    by blast
next
  assume \<open>\<exists>\<FF>::(_, _, 'c) kraus_family. \<EE> = (*\<^sub>k\<^sub>r) \<FF> \<and> kf_trace_preserving \<FF>\<close>
  then obtain \<FF> :: \<open>(_,_,'c) kraus_family\<close> where \<EE>\<FF>: \<open>\<EE> = kf_apply \<FF>\<close> and tp\<FF>: \<open>kf_trace_preserving \<FF>\<close>
    by blast
  from \<EE>\<FF> have \<open>\<EE> = kf_apply (kf_flatten \<FF>)\<close>
    by simp
  moreover from tp\<FF> have \<open>kf_trace_preserving (kf_flatten \<FF>)\<close>
    by (metis \<EE>\<FF> calculation kf_trace_preserving_iff_bound_id km_bound_kf_bound)
  ultimately show \<open>km_trace_preserving \<EE>\<close>
    using km_trace_preserving_def by blast
qed

definition km_trace_reducing_def: \<open>km_trace_reducing \<EE> \<longleftrightarrow> (\<exists>\<FF>::(_,_,unit) kraus_family. \<EE> = kf_apply \<FF> \<and> kf_trace_reducing \<FF>)\<close>
lemma km_trace_reducing_def': \<open>km_trace_reducing \<EE> \<longleftrightarrow> (\<exists>\<FF>::(_, _, 'c) kraus_family. \<EE> = kf_apply \<FF> \<and> kf_trace_reducing \<FF>)\<close>
proof (rule iffI)
  assume \<open>km_trace_reducing \<EE>\<close>
  then obtain \<FF> :: \<open>(_,_,unit) kraus_family\<close> where \<EE>\<FF>: \<open>\<EE> = kf_apply \<FF>\<close> and tp\<FF>: \<open>kf_trace_reducing \<FF>\<close>
    using km_trace_reducing_def by blast
  from \<EE>\<FF> have \<open>\<EE> = kf_apply (kf_map (\<lambda>_. undefined :: 'c) \<FF>)\<close>
    by simp
  moreover from tp\<FF> have \<open>kf_trace_reducing (kf_map (\<lambda>_. undefined :: 'c) \<FF>)\<close>
    by (simp add: kf_trace_reducing_iff_norm_leq1)
  ultimately show \<open>\<exists>\<FF>::(_, _, 'c) kraus_family. \<EE> = (*\<^sub>k\<^sub>r) \<FF> \<and> kf_trace_reducing \<FF>\<close>
    by blast
next
  assume \<open>\<exists>\<FF>::(_, _, 'c) kraus_family. \<EE> = (*\<^sub>k\<^sub>r) \<FF> \<and> kf_trace_reducing \<FF>\<close>
  then obtain \<FF> :: \<open>(_,_,'c) kraus_family\<close> where \<EE>\<FF>: \<open>\<EE> = kf_apply \<FF>\<close> and tp\<FF>: \<open>kf_trace_reducing \<FF>\<close>
    by blast
  from \<EE>\<FF> have \<open>\<EE> = kf_apply (kf_flatten \<FF>)\<close>
    by simp
  moreover from tp\<FF> have \<open>kf_trace_reducing (kf_flatten \<FF>)\<close>
    by (simp add: kf_trace_reducing_iff_norm_leq1)
  ultimately show \<open>km_trace_reducing \<EE>\<close>
    using km_trace_reducing_def by blast
qed

lemma km_trace_preserving_apply[simp]: \<open>km_trace_preserving (kf_apply \<EE>) = kf_trace_preserving \<EE>\<close>
  using kf_trace_preserving_def km_trace_preserving_def' by auto

lemma km_trace_reducing_apply[simp]: \<open>km_trace_reducing (kf_apply \<EE>) = kf_trace_reducing \<EE>\<close>
  by (metis kf_trace_reducing_iff_norm_leq1 km_norm_kf_norm km_trace_reducing_def')

lemma km_trace_preserving_iff: \<open>km_trace_preserving \<EE> \<longleftrightarrow> kraus_map \<EE> \<and> (\<forall>\<rho>. trace_tc (\<EE> \<rho>) = trace_tc \<rho>)\<close>
proof (intro iffI conjI allI)
  assume tp: \<open>km_trace_preserving \<EE>\<close>
  then obtain \<FF> :: \<open>(_,_,unit) kraus_family\<close> where \<EE>\<FF>: \<open>\<EE> = kf_apply \<FF>\<close> and tp\<FF>: \<open>kf_trace_preserving \<FF>\<close>
    by (metis kf_trace_preserving_def kf_trace_reducing_def km_trace_preserving_def order.refl)
  then show \<open>kraus_map \<EE>\<close>
    by blast
  from tp\<FF> show \<open>trace_tc (\<EE> \<rho>) = trace_tc \<rho>\<close> for \<rho>
    by (simp add: \<EE>\<FF> kf_trace_preserving_def)
next
  assume asm: \<open>kraus_map \<EE> \<and> (\<forall>\<rho>. trace_tc (\<EE> \<rho>) = trace_tc \<rho>)\<close>
  then obtain \<FF> :: \<open>(_,_,unit) kraus_family\<close> where \<EE>\<FF>: \<open>\<EE> = kf_apply \<FF>\<close>
    using kraus_map_def_raw by blast
  from asm \<EE>\<FF> have \<open>trace_tc (kf_apply \<FF> \<rho>) = trace_tc \<rho>\<close> for \<rho>
    by blast
  then have \<open>kf_trace_preserving \<FF>\<close>
    using kf_trace_preserving_def by blast
  with \<EE>\<FF> show \<open>km_trace_preserving \<EE>\<close>
    using km_trace_preserving_def by blast
qed


lemma km_trace_reducing_iff: \<open>km_trace_reducing \<EE> \<longleftrightarrow> kraus_map \<EE> \<and> (\<forall>\<rho>\<ge>0. trace_tc (\<EE> \<rho>) \<le> trace_tc \<rho>)\<close>
proof (intro iffI conjI allI impI)
  assume tp: \<open>km_trace_reducing \<EE>\<close>
  then obtain \<FF> :: \<open>(_,_,unit) kraus_family\<close> where \<EE>\<FF>: \<open>\<EE> = kf_apply \<FF>\<close> and tp\<FF>: \<open>kf_trace_reducing \<FF>\<close>
    by (metis kf_trace_reducing_def kf_trace_reducing_def km_trace_reducing_def order.refl)
  then show \<open>kraus_map \<EE>\<close>
    by blast
  from tp\<FF> \<EE>\<FF> show \<open>trace_tc (\<EE> \<rho>) \<le> trace_tc \<rho>\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho>
    using kf_trace_reducing_def that by blast
next
  assume asm: \<open>kraus_map \<EE> \<and> (\<forall>\<rho>\<ge>0. trace_tc (\<EE> \<rho>) \<le> trace_tc \<rho>)\<close>
  then obtain \<FF> :: \<open>(_,_,unit) kraus_family\<close> where \<EE>\<FF>: \<open>\<EE> = kf_apply \<FF>\<close>
    using kraus_map_def_raw by blast
  from asm \<EE>\<FF> have \<open>trace_tc (kf_apply \<FF> \<rho>) \<le> trace_tc \<rho>\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho>
    using that by blast
  then have \<open>kf_trace_reducing \<FF>\<close>
    using kf_trace_reducing_def by blast
  with \<EE>\<FF> show \<open>km_trace_reducing \<EE>\<close>
    using km_trace_reducing_def by blast
qed

lemma km_trace_preserving_imp_reducing:
  assumes \<open>km_trace_preserving \<EE>\<close>
  shows \<open>km_trace_reducing \<EE>\<close>
  using assms km_trace_preserving_iff km_trace_reducing_iff by fastforce

lemma km_trace_preserving_id[iff]: \<open>km_trace_preserving id\<close>
  by (simp add: km_trace_preserving_iff)

lemma km_trace_reducing_iff_norm_leq1: \<open>km_trace_reducing \<EE> \<longleftrightarrow> kraus_map \<EE> \<and> km_norm \<EE> \<le> 1\<close>
proof (intro iffI conjI)
  assume \<open>km_trace_reducing \<EE>\<close>
  then show \<open>kraus_map \<EE>\<close>
    using km_trace_reducing_iff by blast
  then obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  with \<open>km_trace_reducing \<EE>\<close>
  have \<open>kf_trace_reducing EE\<close>
    using kf_trace_reducing_def km_trace_reducing_iff by blast
  then have \<open>kf_norm EE \<le> 1\<close>
    using kf_trace_reducing_iff_norm_leq1 by blast
  then show \<open>km_norm \<EE> \<le> 1\<close>
    by (simp add: EE km_norm_kf_norm)
next
  assume asm: \<open>kraus_map \<EE> \<and> km_norm \<EE> \<le> 1\<close>
  then obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  from asm have \<open>km_norm \<EE> \<le> 1\<close>
    by blast
  then have \<open>kf_norm EE \<le> 1\<close>
    by (simp add: EE km_norm_kf_norm)
  then have \<open>kf_trace_reducing EE\<close>
    by (simp add: kf_trace_reducing_iff_norm_leq1)
  then show \<open>km_trace_reducing \<EE>\<close>
    using EE km_trace_reducing_def by blast
qed


lemma km_trace_preserving_iff_bound_id: \<open>km_trace_preserving \<EE> \<longleftrightarrow> kraus_map \<EE> \<and> km_bound \<EE> = id_cblinfun\<close>
proof (intro iffI conjI)
  assume \<open>km_trace_preserving \<EE>\<close>
  then show \<open>kraus_map \<EE>\<close>
    using km_trace_preserving_iff by blast
  then obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  with \<open>km_trace_preserving \<EE>\<close>
  have \<open>kf_trace_preserving EE\<close>
    using kf_trace_preserving_def km_trace_preserving_iff by blast
  then have \<open>kf_bound EE = id_cblinfun\<close>
    by (simp add: kf_trace_preserving_iff_bound_id)
  then show \<open>km_bound \<EE> = id_cblinfun\<close>
    by (simp add: EE km_bound_kf_bound)
next
  assume asm: \<open>kraus_map \<EE> \<and> km_bound \<EE> = id_cblinfun\<close>
  then have \<open>kraus_map \<EE>\<close>
    by simp
  then obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close>
    using kraus_map_def_raw by blast
  from asm have \<open>kf_bound EE = id_cblinfun\<close>
    by (simp add: EE km_bound_kf_bound)
  then have \<open>kf_trace_preserving EE\<close>
    by (simp add: kf_trace_preserving_iff_bound_id)
  then show \<open>km_trace_preserving \<EE>\<close>
    using EE km_trace_preserving_def by blast
qed

lemma km_trace_preserving_iff_bound_id':
  fixes \<EE> :: \<open>('a::{chilbert_space, not_singleton}, 'a) trace_class \<Rightarrow> _\<close>
  shows \<open>km_trace_preserving \<EE> \<longleftrightarrow> km_bound \<EE> = id_cblinfun\<close>
  using km_bound_invalid km_trace_preserving_iff_bound_id by fastforce

lemma km_trace_norm_preserving: \<open>km_norm \<EE> \<le> 1\<close> if \<open>km_trace_preserving \<EE>\<close>
  using km_trace_preserving_imp_reducing km_trace_reducing_iff_norm_leq1 that by blast

lemma km_trace_norm_preserving_eq: 
  fixes \<EE> :: \<open>('a::{chilbert_space,not_singleton},'a) trace_class \<Rightarrow> ('b::chilbert_space,'b) trace_class\<close>
  assumes \<open>km_trace_preserving \<EE>\<close>
  shows \<open>km_norm \<EE> = 1\<close>
  using assms 
  by (simp add: km_trace_preserving_iff_bound_id' km_norm_def)


lemma kraus_map_trace: \<open>kraus_map (one_dim_iso o trace_tc)\<close>
  by (auto intro!: ext kraus_mapI[of _ \<open>kf_trace some_chilbert_basis\<close>]
      simp: kf_trace_is_trace)

lemma trace_preserving_trace_kraus_map[iff]: \<open>km_trace_preserving (one_dim_iso o trace_tc)\<close>
  using km_trace_preserving_iff kraus_map_trace by fastforce

lemma km_trace_bound[simp]: \<open>km_bound (one_dim_iso o trace_tc) = id_cblinfun\<close>
  using km_trace_preserving_iff_bound_id by blast

lemma km_trace_norm_eq1[simp]: \<open>km_norm (one_dim_iso o trace_tc :: ('a::{chilbert_space,not_singleton},'a) trace_class \<Rightarrow> _) = 1\<close>
  using km_trace_norm_preserving_eq by blast

lemma km_trace_norm_leq1[simp]: \<open>km_norm (one_dim_iso o trace_tc) \<le> 1\<close>
  using km_trace_norm_preserving by blast

lemma kraus_map_partial_trace[iff]: \<open>kraus_map partial_trace\<close>
  by (auto intro!: ext kraus_mapI[of _ \<open>kf_partial_trace_right\<close>] simp flip: partial_trace_is_kf_partial_trace)

lemma partial_trace_ignores_kraus_map:
  assumes \<open>km_trace_preserving \<EE>\<close>
  assumes \<open>kraus_map \<FF>\<close>
  shows \<open>partial_trace (km_tensor \<FF> \<EE> \<rho>) = \<FF> (partial_trace \<rho>)\<close>
proof -
  from assms
  obtain EE :: \<open>(_,_,unit) kraus_family\<close> where EE_def: \<open>\<EE> = kf_apply EE\<close> and tpEE: \<open>kf_trace_preserving EE\<close>
    using km_trace_preserving_def by blast
  obtain FF :: \<open>(_,_,unit) kraus_family\<close> where FF_def: \<open>\<FF> = kf_apply FF\<close>
    using assms(2) kraus_map_def_raw by blast
  have \<open>partial_trace (km_tensor \<FF> \<EE> \<rho>) = partial_trace (kf_tensor FF EE *\<^sub>k\<^sub>r \<rho>)\<close>
    using assms
    by (simp add: km_trace_preserving_def partial_trace_ignores_kraus_family
        km_tensor_kf_tensor EE_def kf_id_apply[abs_def] id_def FF_def
        flip: km_tensor_kf_tensor)
  also have \<open>\<dots> = FF *\<^sub>k\<^sub>r partial_trace \<rho>\<close>
    by (simp add: partial_trace_ignores_kraus_family tpEE)
  also have \<open>\<dots> = \<FF> (partial_trace \<rho>)\<close>
    using FF_def by presburger
  finally show ?thesis
    by -
qed


lemma km_partial_trace_bound[simp]: \<open>km_bound partial_trace = id_cblinfun\<close>
  apply (subst km_bound_kf_bound[of _ kf_partial_trace_right])
  using partial_trace_is_kf_partial_trace by auto

lemma km_partial_trace_norm[simp]:
  shows \<open>km_norm partial_trace = 1\<close>
  by (simp add: km_norm_def)


lemma km_trace_preserving_tensor:
  assumes \<open>km_trace_preserving \<EE>\<close> and \<open>km_trace_preserving \<FF>\<close>
  shows \<open>km_trace_preserving (km_tensor \<EE> \<FF>)\<close>
proof -
  from assms obtain EE :: \<open>('a ell2, 'b ell2, unit) kraus_family\<close> where EE: \<open>\<EE> = kf_apply EE\<close> and tE: \<open>kf_trace_preserving EE\<close>
    using km_trace_preserving_def by blast
  from assms obtain FF :: \<open>('c ell2, 'd ell2, unit) kraus_family\<close> where FF: \<open>\<FF> = kf_apply FF\<close> and tF: \<open>kf_trace_preserving FF\<close>
    using km_trace_preserving_def by blast
  show ?thesis
    by (auto intro!: kf_trace_preserving_tensor simp: EE FF km_tensor_kf_tensor tE tF)
qed

lemma km_trace_reducing_tensor:
  assumes \<open>km_trace_reducing \<EE>\<close> and \<open>km_trace_reducing \<FF>\<close>
  shows \<open>km_trace_reducing (km_tensor \<EE> \<FF>)\<close>
  by (smt (z3) assms(1,2) km_norm_geq0 km_norm_tensor km_tensor_kraus_map km_trace_reducing_iff_norm_leq1
      mult_left_le_one_le)

subsection \<open>Complete measurements\<close>


definition \<open>km_complete_measurement B \<rho> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) \<rho>)\<close>
abbreviation \<open>km_complete_measurement_ket \<equiv> km_complete_measurement (range ket)\<close>


lemma km_complete_measurement_kf_complete_measurement: \<open>km_complete_measurement B = kf_apply (kf_complete_measurement B)\<close> if \<open>is_ortho_set B\<close>
  by (simp add: kf_complete_measurement_apply[OF that, abs_def] km_complete_measurement_def[abs_def])

lemma km_complete_measurement_ket_kf_complete_measurement_ket: \<open>km_complete_measurement_ket = kf_apply kf_complete_measurement_ket\<close>
  by (metis Complex_L2.is_ortho_set_ket kf_apply_map kf_complete_measurement_ket_kf_map kf_eq_imp_eq_weak kf_eq_weak_def
      km_complete_measurement_kf_complete_measurement)


lemma km_complete_measurement_has_sum:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>((\<lambda>x. sandwich_tc (selfbutter (sgn x)) \<rho>) has_sum km_complete_measurement B \<rho>) B\<close>
  using kf_complete_measurement_has_sum[OF assms] and assms
  by (simp add: kf_complete_measurement_apply km_complete_measurement_def)

lemma km_complete_measurement_ket_has_sum:
  \<open>((\<lambda>x. sandwich_tc (selfbutter (ket x)) \<rho>) has_sum km_complete_measurement_ket \<rho>) UNIV\<close>
  by (smt (verit) has_sum_cong has_sum_reindex inj_ket is_onb_ket is_ortho_set_ket kf_complete_measurement_apply
      kf_complete_measurement_has_sum_onb km_complete_measurement_def o_def)

lemma km_bound_complete_measurement:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>km_bound (km_complete_measurement B) \<le> id_cblinfun\<close>
  apply (subst km_bound_kf_bound[of _ \<open>kf_complete_measurement B\<close>])
  using assms kf_complete_measurement_apply km_complete_measurement_def apply fastforce 
  by (simp add: assms kf_bound_complete_measurement)

lemma km_norm_complete_measurement:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>km_norm (km_complete_measurement B) \<le> 1\<close>
  apply (subst km_norm_kf_norm[of _ \<open>kf_complete_measurement B\<close>])
   apply (simp add: assms km_complete_measurement_kf_complete_measurement)
  by (simp_all add: assms kf_norm_complete_measurement)

lemma km_bound_complete_measurement_onb[simp]:
  assumes \<open>is_onb B\<close>
  shows \<open>km_bound (km_complete_measurement B) = id_cblinfun\<close>
  apply (subst km_bound_kf_bound[of _ \<open>kf_complete_measurement B\<close>])
  using assms
  by (auto intro!: ext simp: kf_complete_measurement_apply is_onb_def km_complete_measurement_def)

lemma km_bound_complete_measurement_ket[simp]: \<open>km_bound km_complete_measurement_ket = id_cblinfun\<close>
  by fastforce

lemma km_norm_complete_measurement_onb[simp]:
  fixes B :: \<open>'a::{not_singleton, chilbert_space} set\<close>
  assumes \<open>is_onb B\<close>
  shows \<open>km_norm (km_complete_measurement B) = 1\<close>
  apply (subst km_norm_kf_norm[of _ \<open>kf_complete_measurement B\<close>])
  using assms
  by (auto intro!: ext simp: kf_complete_measurement_apply is_onb_def km_complete_measurement_def)

lemma km_norm_complete_measurement_ket[simp]:
  shows \<open>km_norm km_complete_measurement_ket = 1\<close>
  by fastforce

lemma kraus_map_complete_measurement:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kraus_map (km_complete_measurement B)\<close>
  apply (rule kraus_mapI[of _ \<open>kf_complete_measurement B\<close>])
  by (auto intro!: ext simp add: assms kf_complete_measurement_apply km_complete_measurement_def)

lemma kraus_map_complete_measurement_ket[iff]:
  shows \<open>kraus_map km_complete_measurement_ket\<close>
  by (simp add: kraus_map_complete_measurement)

lemma km_complete_measurement_idem[simp]:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>km_complete_measurement B (km_complete_measurement B \<rho>) = km_complete_measurement B \<rho>\<close>
  using kf_complete_measurement_idem[of B]
    kf_complete_measurement_apply[OF assms] km_complete_measurement_def
  by (metis (no_types, lifting) ext kf_comp_apply kf_complete_measurement_idem_weak kf_eq_weak_def o_def)

lemma km_complete_measurement_ket_idem[simp]:
  \<open>km_complete_measurement_ket (km_complete_measurement_ket \<rho>) = km_complete_measurement_ket \<rho>\<close>
  by fastforce

lemma km_complete_measurement_has_sum_onb:
  assumes \<open>is_onb B\<close>
  shows \<open>((\<lambda>x. sandwich_tc (selfbutter x) \<rho>) has_sum km_complete_measurement B \<rho>) B\<close>
  using kf_complete_measurement_has_sum_onb[OF assms] and assms
  by (simp add: kf_complete_measurement_apply km_complete_measurement_def is_onb_def)

lemma km_complete_measurement_ket_diagonal_operator[simp]:
  \<open>km_complete_measurement_ket (diagonal_operator_tc f) = diagonal_operator_tc f\<close>
  using kf_complete_measurement_ket_diagonal_operator[of f]
  by (metis (no_types, lifting) is_ortho_set_ket kf_apply_map kf_apply_on_UNIV kf_apply_on_eqI kf_complete_measurement_apply
      kf_complete_measurement_ket_kf_map km_complete_measurement_def)

lemma km_operators_complete_measurement:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>km_operators_in (km_complete_measurement B) (span (selfbutter ` B))\<close>
proof -
  have \<open>span ((selfbutter \<circ> sgn) ` B) \<subseteq> span (selfbutter ` B)\<close>
  proof (intro real_vector.span_minimal[OF _ real_vector.subspace_span] subsetI)
    fix a
    assume \<open>a \<in> (selfbutter \<circ> sgn) ` B\<close>
    then obtain h where \<open>a = selfbutter (sgn h)\<close> and \<open>h \<in> B\<close>
      by force
    then have \<open>a = (inverse (norm h))\<^sup>2 *\<^sub>R selfbutter h\<close>
      by (simp add: sgn_div_norm scaleR_scaleC power2_eq_square)
    with \<open>h \<in> B\<close>
    show \<open>a \<in> span (selfbutter ` B)\<close>
      by (simp add: span_clauses(1) span_mul)
  qed
  then show ?thesis
    by (simp add: km_complete_measurement_kf_complete_measurement assms km_operators_in_kf_apply
        kf_operators_complete_measurement)
qed

lemma km_operators_complete_measurement_ket:
  shows \<open>km_operators_in km_complete_measurement_ket (span (range (\<lambda>c. (selfbutter (ket c)))))\<close>
  by (metis (no_types, lifting) image_cong is_ortho_set_ket km_operators_complete_measurement range_composition)


lemma km_complete_measurement_ket_butterket[simp]:
  \<open>km_complete_measurement_ket (tc_butterfly (ket c) (ket c)) = tc_butterfly (ket c) (ket c)\<close>
  by (simp add: km_complete_measurement_ket_kf_complete_measurement_ket kf_complete_measurement_ket_apply_butterfly)

lemma km_complete_measurement_tensor:
  assumes \<open>is_ortho_set B\<close> and \<open>is_ortho_set C\<close>
  shows \<open>km_tensor (km_complete_measurement B) (km_complete_measurement C)
             = km_complete_measurement ((\<lambda>(b,c). b \<otimes>\<^sub>s c) ` (B \<times> C))\<close>
  by (simp add: km_complete_measurement_kf_complete_measurement assms is_ortho_set_tensor km_tensor_kf_tensor
      flip: kf_complete_measurement_tensor)

lemma km_complete_measurement_ket_tensor:
  shows \<open>km_tensor (km_complete_measurement_ket :: ('a ell2, _) trace_class \<Rightarrow> _) (km_complete_measurement_ket :: ('b ell2, _) trace_class \<Rightarrow> _)
             = km_complete_measurement_ket\<close>
  by (simp add: km_complete_measurement_ket_kf_complete_measurement_ket km_tensor_kf_tensor kf_complete_measurement_ket_tensor)

lemma km_tensor_0_left[simp]: \<open>km_tensor (0 :: ('a ell2, 'b ell2) trace_class \<Rightarrow> ('c ell2, 'd ell2) trace_class) \<EE> = 0\<close>
proof (cases \<open>km_tensor_exists (0 :: ('a ell2, 'b ell2) trace_class \<Rightarrow> ('c ell2, 'd ell2) trace_class) \<EE>\<close>)
  case True
  then show ?thesis
    apply (rule_tac eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
    by (simp_all add: km_tensor_apply)
next
  case False
  then show ?thesis
    using km_tensor_invalid by blast
qed

lemma km_tensor_0_right[simp]: \<open>km_tensor \<EE> (0 :: ('a ell2, 'b ell2) trace_class \<Rightarrow> ('c ell2, 'd ell2) trace_class) = 0\<close>
proof (cases \<open>km_tensor_exists \<EE> (0 :: ('a ell2, 'b ell2) trace_class \<Rightarrow> ('c ell2, 'd ell2) trace_class)\<close>)
  case True
  then show ?thesis
    apply (rule_tac eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
    by (simp_all add: km_tensor_apply)
next
  case False
  then show ?thesis
    using km_tensor_invalid by blast
qed




unbundle no kraus_map_syntax
unbundle no cblinfun_syntax

end
