(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Completeness and cocompleteness\<close>
theory CZH_UCAT_Complete
  imports 
    CZH_UCAT_Limit
    CZH_UCAT_Limit_Product
    CZH_UCAT_Limit_Equalizer
begin



subsection\<open>Limits by products and equalizers\<close>

lemma cat_limit_of_cat_prod_obj_and_cat_equalizer:
  \<comment>\<open>See Theorem 1 in Chapter V-2 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>\<aa> \<bb> \<gg> \<ff>. \<lbrakk> \<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>; \<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb> \<rbrakk> \<Longrightarrow>
      \<exists>E \<epsilon>. \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A. tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) A \<CC> \<Longrightarrow>
      \<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A. tm_cf_discrete \<alpha> (\<JJ>\<lparr>Arr\<rparr>) A \<CC> \<Longrightarrow>
      \<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains r u where "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  let ?L =\<open>\<lambda>u. \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>\<close> and ?R =\<open>\<lambda>i. \<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<close>
  
  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> by (rule assms(1))

  have "?R j \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    by (cs_concl cs_shallow cs_intro: cat_cs_intros that)

  have "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) ?R \<CC>"
  proof(intro tm_cf_discreteI)
    show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "i \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for i
      by (cs_concl cs_shallow cs_intro: cat_cs_intros that)
    show "VLambda (\<JJ>\<lparr>Obj\<rparr>) ?R \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      show "\<R>\<^sub>\<circ> (VLambda (\<JJ>\<lparr>Obj\<rparr>) ?R) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof-
        have "\<R>\<^sub>\<circ> (VLambda (\<JJ>\<lparr>Obj\<rparr>) ?R) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
          by (auto simp: \<FF>.cf_ObjMap_vdomain)
        moreover have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (force intro: vrange_in_VsetI \<FF>.tm_cf_ObjMap_in_Vset)
        ultimately show ?thesis by auto
      qed
    qed (auto simp: cat_small_cs_intros)
    show "(\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      show "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof-
        have "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
        proof(rule vrange_VLambda_vsubset)
          fix x assume x: "x \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
          then have "\<JJ>\<lparr>CId\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
            by (auto intro: cat_cs_intros simp: cat_cs_simps)
          moreover from x have "\<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<JJ>\<lparr>CId\<rparr>\<lparr>x\<rparr>\<rparr>"
            by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          ultimately show "\<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
            by (simp add: \<FF>.ArrMap.vsv_vimageI2)
        qed
        moreover have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (force intro: vrange_in_VsetI \<FF>.tm_cf_ArrMap_in_Vset)
        ultimately show ?thesis by auto
      qed
    qed (auto simp: cat_small_cs_intros)
  qed (auto intro: cat_cs_intros)

  from assms(3)[where A=\<open>?R\<close>, OF this] obtain P\<^sub>O \<pi>\<^sub>O
    where \<pi>\<^sub>O: "\<pi>\<^sub>O : P\<^sub>O <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> ?R : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by clarsimp

  interpret \<pi>\<^sub>O: is_cat_obj_prod \<alpha> \<open>\<JJ>\<lparr>Obj\<rparr>\<close> ?R \<CC> P\<^sub>O \<pi>\<^sub>O by (rule \<pi>\<^sub>O)

  have P\<^sub>O: "P\<^sub>O \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (intro \<pi>\<^sub>O.cat_cone_obj)

  have "?L u \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "u \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for u
  proof-
    from that obtain a b where "u : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
    then show ?thesis 
      by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed

  have tm_cf_discrete: "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Arr\<rparr>) ?L \<CC>"
  proof(intro tm_cf_discreteI)
    show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for f
    proof-
      from that obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
      then show ?thesis 
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed
 
    show "(\<lambda>u\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      show "\<R>\<^sub>\<circ> (\<lambda>u\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. ?L u) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof-
        have "\<R>\<^sub>\<circ> (\<lambda>u\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. ?L u) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
        proof(rule vrange_VLambda_vsubset)
          fix f assume "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>"
          then obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
          then show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
            by 
              (
                cs_concl cs_shallow
                  cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_cs_intros
              )
        qed
        moreover have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (auto intro: vrange_in_VsetI \<FF>.tm_cf_ObjMap_in_Vset)
        ultimately show ?thesis by auto
      qed
    qed (auto simp: cat_small_cs_intros)

    show "(\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>i\<rparr>\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      show "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>i\<rparr>\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof-
        have "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>i\<rparr>\<rparr>\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
        proof(rule vrange_VLambda_vsubset)
          fix f assume "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>"
          then obtain a b where f: "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
          then have "\<JJ>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
            by (auto intro: cat_cs_intros simp: cat_cs_simps)
          moreover from f have 
            "\<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<JJ>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>"
            by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          ultimately show "\<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
            by (simp add: \<FF>.ArrMap.vsv_vimageI2)
        qed
        moreover have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (force intro: vrange_in_VsetI \<FF>.tm_cf_ArrMap_in_Vset)
        ultimately show ?thesis by auto
      qed
    qed (auto simp: cat_small_cs_intros)
  qed (auto intro: cat_cs_intros)

  from assms(4)[where A=\<open>?L\<close>, OF this, simplified] obtain P\<^sub>A \<pi>\<^sub>A
    where \<pi>\<^sub>A: "\<pi>\<^sub>A : P\<^sub>A <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> ?L : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by auto

  interpret \<pi>\<^sub>A: is_cat_obj_prod \<alpha> \<open>\<JJ>\<lparr>Arr\<rparr>\<close> ?L \<CC> P\<^sub>A \<pi>\<^sub>A by (rule \<pi>\<^sub>A)

  let ?F = \<open>\<lambda>u. \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>\<close> and ?f = \<open>\<lambda>u. \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>\<close> 
  let ?\<pi>\<^sub>O' = \<open>ntcf_obj_prod_base \<CC> (:\<^sub>C (\<JJ>\<lparr>Arr\<rparr>)\<lparr>Obj\<rparr>) ?F P\<^sub>O ?f\<close>

  have \<pi>\<^sub>O': "?\<pi>\<^sub>O' :
    P\<^sub>O <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (\<JJ>\<lparr>Arr\<rparr>) (\<lambda>u. \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>) \<CC> :
    :\<^sub>C (\<JJ>\<lparr>Arr\<rparr>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    unfolding the_cat_discrete_components(1)
  proof
    (
      intro 
        tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone 
        tm_cf_discrete
    )
    fix f assume "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>"
    then obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
    then show "\<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr> : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>"
      by 
        (
          cs_concl cs_shallow
            cs_simp:
              the_cat_discrete_components(1) cat_discrete_cs_simps cat_cs_simps
            cs_intro: cat_cs_intros
        )
  qed (intro P\<^sub>O)

  from \<pi>\<^sub>A.cat_obj_prod_unique_cone'[OF \<pi>\<^sub>O'] obtain f' 
    where f': "f' : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
      and \<pi>\<^sub>O'_NTMap_app: 
        "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>\<^sub>O'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      and unique_f':
        "\<lbrakk>
          f'' : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A;
          \<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>\<^sub>O'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''
         \<rbrakk> \<Longrightarrow> f'' = f'"
      for f''
    by metis

  have \<pi>\<^sub>O_NTMap_app_Cod: 
    "\<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>b\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'" if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" for f a b 
  proof-
    from that have "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" by auto
    from \<pi>\<^sub>O'_NTMap_app[OF this] that show ?thesis
      by 
        (
          cs_prems cs_shallow
            cs_simp: cat_cs_simps the_cat_discrete_components(1)
            cs_intro: cat_cs_intros
        )
  qed

  from this[symmetric] have \<pi>\<^sub>A_NTMap_Comp_app: 
    "\<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q) = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q" 
    if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" and "q : c \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>O" for q f a b c 
    using that f'
    by (intro \<FF>.HomCod.cat_assoc_helper)
      (
        cs_concl cs_shallow
          cs_simp: 
            cat_cs_simps cat_discrete_cs_simps the_cat_discrete_components(1)
          cs_intro: cat_cs_intros
      )+

  let ?g = \<open>\<lambda>u. \<FF>\<lparr>ArrMap\<rparr>\<lparr>u\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Dom\<rparr>\<lparr>u\<rparr>\<rparr>\<close> 
  let ?\<pi>\<^sub>O'' = \<open>ntcf_obj_prod_base \<CC> (:\<^sub>C (\<JJ>\<lparr>Arr\<rparr>)\<lparr>Obj\<rparr>) ?F P\<^sub>O ?g\<close>
  
  have \<pi>\<^sub>O'': "?\<pi>\<^sub>O'' : P\<^sub>O <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (\<JJ>\<lparr>Arr\<rparr>) ?L \<CC> : :\<^sub>C (\<JJ>\<lparr>Arr\<rparr>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    unfolding the_cat_discrete_components(1)
  proof
    (
      intro 
        tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone  
        tm_cf_discrete
    )
    show "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<rparr> : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>"
      if "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for f
    proof-
      from that obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b"  by auto
      then show ?thesis
        by  
          (
            cs_concl 
              cs_simp: 
                cat_cs_simps cat_discrete_cs_simps 
                the_cat_discrete_components(1) 
              cs_intro: cat_cs_intros
          )
    qed
  qed (intro P\<^sub>O)

  from \<pi>\<^sub>A.cat_obj_prod_unique_cone'[OF \<pi>\<^sub>O''] obtain g' 
    where g': "g' : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
      and \<pi>\<^sub>O''_NTMap_app: 
        "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>\<^sub>O''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g'"
      and unique_g':
        "\<lbrakk>
          g'' : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A;
          \<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>\<^sub>O''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g''
         \<rbrakk> \<Longrightarrow> g'' = g'"
      for g''
    by (metis (lifting))

  have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g'" 
    if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" for f a b 
  proof-
    from that have "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" by auto
    from \<pi>\<^sub>O''_NTMap_app[OF this] that show ?thesis
      by 
        (
          cs_prems cs_shallow
            cs_simp: cat_cs_simps the_cat_discrete_components(1)
            cs_intro: cat_cs_intros
        )
  qed
  then have \<pi>\<^sub>O_NTMap_app_Dom: 
    "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q) =
      (\<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g') \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q" 
    if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" and "q : c \<mapsto>\<^bsub>\<CC>\<^esub>  P\<^sub>O" for q f a b c 
    using that g' 
    by (intro \<FF>.HomCod.cat_assoc_helper)
      (
        cs_concl 
          cs_simp: 
            cat_cs_simps cat_discrete_cs_simps the_cat_discrete_components(1)
          cs_intro: cat_cs_intros
      )

  from assms(2)[OF f' g'] obtain E \<epsilon> where \<epsilon>: 
    "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (P\<^sub>O,P\<^sub>A,g',f') : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by clarsimp

  interpret \<epsilon>: is_cat_equalizer_2 \<alpha> P\<^sub>O P\<^sub>A g' f' \<CC> E \<epsilon> by (rule \<epsilon>)

  define \<mu> where "\<mu> =
    [(\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>), cf_const \<JJ> \<CC> E, \<FF>, \<JJ>, \<CC>]\<^sub>\<circ>"

  have \<mu>_components:
    "\<mu>\<lparr>NTMap\<rparr> = (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>)"
    "\<mu>\<lparr>NTDom\<rparr> = cf_const \<JJ> \<CC> E"
    "\<mu>\<lparr>NTCod\<rparr> = \<FF>"
    "\<mu>\<lparr>NTDGDom\<rparr> = \<JJ>"
    "\<mu>\<lparr>NTDGCod\<rparr> = \<CC>"
    unfolding \<mu>_def nt_field_simps by (simp_all add: nat_omega_simps)

  have [cat_cs_simps]: 
    "\<mu>\<lparr>NTMap\<rparr>\<lparr>i\<rparr> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>" if "i \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" 
    for i
    using that unfolding \<mu>_components by simp

  have "\<mu> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  proof(intro is_cat_limitI)

    show \<mu>: "\<mu> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
      show "vfsequence \<mu>" unfolding \<mu>_def by simp 
      show "vcard \<mu> = 5\<^sub>\<nat>" unfolding \<mu>_def by (simp add: nat_omega_simps)
      show "cf_const \<JJ> \<CC> E : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_intro: cat_cs_intros cat_lim_cs_intros)
      show "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      show "\<mu>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : cf_const \<JJ> \<CC> E\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        if "a \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for a
        using that
        by 
          (
            cs_concl 
              cs_simp: 
                cat_cs_simps 
                cat_discrete_cs_simps 
                cat_parallel_cs_simps 
                the_cat_discrete_components(1) 
              cs_intro: cat_cs_intros cat_lim_cs_intros cat_parallel_cs_intros
          )
      show 
        "\<mu>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> cf_const \<JJ> \<CC> E\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
          \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<mu>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" for a b f
        using that \<epsilon> g' f' 
        by 
          (
            cs_concl 
              cs_simp:
                cat_parallel_cs_simps
                cat_cs_simps 
                the_cat_discrete_components(1) 
                \<pi>\<^sub>O_NTMap_app_Cod 
                \<pi>\<^sub>O_NTMap_app_Dom 
                \<epsilon>.cat_eq_2_Comp_eq(1) 
              cs_intro: cat_lim_cs_intros cat_cs_intros cat_parallel_cs_intros
          )

    qed (auto simp: \<mu>_components cat_cs_intros)

    interpret \<mu>: is_cat_cone \<alpha> E \<JJ> \<CC> \<FF> \<mu> by (rule \<mu>)

    show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> u' = \<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
      if "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" for u' r'
    proof-

      interpret u': is_cat_cone \<alpha> r' \<JJ> \<CC> \<FF> u' by (rule that)

      let ?u' = \<open>\<lambda>j. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr>\<close> 
      let ?\<pi>' = \<open>ntcf_obj_prod_base \<CC> (\<JJ>\<lparr>Obj\<rparr>) ?R r' ?u'\<close>

      have \<pi>'_NTMap_app: "?\<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
        using that 
        unfolding ntcf_obj_prod_base_components the_cat_discrete_components 
        by auto

      have \<pi>': "?\<pi>' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (\<JJ>\<lparr>Obj\<rparr>) ?R \<CC> : :\<^sub>C (\<JJ>\<lparr>Obj\<rparr>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        unfolding the_cat_discrete_components(1)
      proof(intro tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone)
        show "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) ?R \<CC>"
        proof(intro tm_cf_discreteI)
          show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "i \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for i
            by (cs_concl cs_simp: cat_cs_simps cs_intro: that cat_cs_intros)
          show "category \<alpha> \<CC>" by (auto intro: cat_cs_intros)
          from \<FF>.tm_cf_ObjMap_in_Vset show "(\<lambda>x\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
            by (auto simp: \<FF>.cf_ObjMap_vdomain)
          show "(\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
          proof(rule vbrelation.vbrelation_Limit_in_VsetI)
            have "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
            proof(intro vsubsetI)
              fix x assume "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>)"
              then obtain i where i: "i \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" 
                and x_def: "x = \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>"
                by auto
              from i have "x = \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<JJ>\<lparr>CId\<rparr>\<lparr>i\<rparr>\<rparr>"
                by (simp add: x_def \<FF>.cf_ObjMap_CId)
              moreover from i have "\<JJ>\<lparr>CId\<rparr>\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
                by 
                  (
                    cs_concl cs_shallow 
                      cs_simp: cat_cs_simps cs_intro: cat_cs_intros
                  )
              ultimately show "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
                by (auto intro: \<FF>.ArrMap.vsv_vimageI2)
            qed
            then show "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"  
              by
                (
                  auto simp: 
                    \<FF>.tm_cf_ArrMap_in_Vset vrange_in_VsetI vsubset_in_VsetI
                )
          qed (auto intro: \<FF>.HomDom.tiny_cat_Obj_in_Vset)
        qed
        show "u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : r' \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
          using that 
          by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      qed (auto simp: cat_cs_intros)

      from \<pi>\<^sub>O.cat_obj_prod_unique_cone'[OF this] obtain h' 
        where h': "h' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>O"
          and \<pi>'_NTMap_app': 
            "\<And>j. j \<in>\<^sub>\<circ> (\<JJ>\<lparr>Obj\<rparr>) \<Longrightarrow> ?\<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'"
          and unique_h': "\<And>h''.
            \<lbrakk> 
              h'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>O;
              \<And>j. j \<in>\<^sub>\<circ> (\<JJ>\<lparr>Obj\<rparr>) \<Longrightarrow> ?\<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'' 
            \<rbrakk> \<Longrightarrow> h'' = h'"
        by metis

      interpret \<pi>':
        is_cat_cone \<alpha> r' \<open>:\<^sub>C (\<JJ>\<lparr>Obj\<rparr>)\<close> \<CC> \<open>:\<rightarrow>: (\<JJ>\<lparr>Obj\<rparr>) (app (\<FF>\<lparr>ObjMap\<rparr>)) \<CC>\<close> ?\<pi>'
        by (rule \<pi>')

      let ?u'' = \<open>\<lambda>u. u'\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>\<close> 
      let ?\<pi>'' = \<open>ntcf_obj_prod_base \<CC> (\<JJ>\<lparr>Arr\<rparr>) ?L r' ?u''\<close>

      have \<pi>''_NTMap_app: "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = u'\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
        if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" for f a b 
        using that 
        unfolding ntcf_obj_prod_base_components the_cat_discrete_components 
        by 
          (
            cs_concl cs_shallow
              cs_simp: V_cs_simps cat_cs_simps cs_intro: cat_cs_intros
          )
      
      have \<pi>'': "?\<pi>'' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (\<JJ>\<lparr>Arr\<rparr>) ?L \<CC> : :\<^sub>C (\<JJ>\<lparr>Arr\<rparr>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        unfolding the_cat_discrete_components(1)
      proof
        (
          intro 
            tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone 
            tm_cf_discrete
        )
        fix f assume "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>"
        then obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
        then show "u'\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr> : r' \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>"
          by 
            (
              cs_concl cs_shallow
                cs_simp: cat_cs_simps cs_intro: cat_cs_intros
            )
      qed (simp add: cat_cs_intros)

      from \<pi>\<^sub>A.cat_obj_prod_unique_cone'[OF this] obtain h'' 
        where h'': "h'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
          and \<pi>''_NTMap_app': 
            "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h''"
          and unique_h'': "\<And>h'''.
            \<lbrakk> 
              h''' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A;
              \<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h''' 
            \<rbrakk> \<Longrightarrow> h''' = h''"
        by metis

      interpret \<pi>'': is_cat_cone \<alpha> r' \<open>:\<^sub>C (\<JJ>\<lparr>Arr\<rparr>)\<close> \<CC> \<open>:\<rightarrow>: (\<JJ>\<lparr>Arr\<rparr>) ?L \<CC>\<close> ?\<pi>''
        by (rule \<pi>'')

      have g'h'_f'h': "g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'"  
      proof-

        from g' h' have g'h': "g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
          by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        from f' h' have f'h': "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
          by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

        have "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')"
          if "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for f
        proof-
          from that obtain a b where f: "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
          then have "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = u'\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
            by (cs_concl cs_simp: \<pi>''_NTMap_app cat_cs_simps)
          also from f have "\<dots> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<pi>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by 
              (
                cs_concl  
                  cs_simp: \<pi>'_NTMap_app cat_cs_simps cat_lim_cs_simps 
                  cs_intro: cat_cs_intros
              )
          also from f g' h' have "\<dots> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')" 
            by 
              (
                cs_concl 
                  cs_simp: 
                    cat_cs_simps 
                    cat_discrete_cs_simps
                    the_cat_discrete_components(1) 
                    \<pi>'_NTMap_app'
                    \<pi>\<^sub>O_NTMap_app_Dom 
                  cs_intro: cat_cs_intros
              )
          finally show ?thesis by simp
        qed
          
        from unique_h''[OF g'h' this, simplified] have g'h'_h'': 
          "g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' = h''".
        have "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')"
          if "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for f
        proof-
          from that obtain a b where f: "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
          then have "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = u'\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
            by (cs_concl cs_simp: \<pi>''_NTMap_app cat_cs_simps)
          also from f have "\<dots> = ?\<pi>'\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
            by 
              (
                cs_concl cs_shallow 
                  cs_simp: \<pi>'_NTMap_app cs_intro: cat_cs_intros
              )
          also from f have "\<dots> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'"
            by 
              (
                cs_concl cs_shallow 
                  cs_simp: \<pi>'_NTMap_app' cs_intro: cat_cs_intros
              )
          also from f g' h' have "\<dots> = (\<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f') \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'"
            by 
              (
                cs_concl cs_shallow 
                  cs_simp: \<pi>\<^sub>O_NTMap_app_Cod cs_intro: cat_cs_intros
              )
          also from that f' h' have "\<dots> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')"
            by 
              (
                cs_concl cs_shallow
                  cs_simp: cat_cs_simps the_cat_discrete_components(1) 
                  cs_intro: cat_cs_intros
               )
          finally show ?thesis by simp
        qed
        from unique_h''[OF f'h' this, simplified] have f'h'_h'': 
          "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' = h''".
        from g'h'_h'' f'h'_h'' show ?thesis by simp
      qed

      let ?II = \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close> 
        and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L P\<^sub>O P\<^sub>A g' f'\<close>

    define \<epsilon>' where "\<epsilon>' =
      [
        (\<lambda>f\<in>\<^sub>\<circ>?II\<lparr>Obj\<rparr>. (f = \<aa>\<^sub>P\<^sub>L\<^sub>2 ? h' : (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'))),
        cf_const ?II \<CC> r',
        ?II_II,
        ?II,
        \<CC>
      ]\<^sub>\<circ>"

    have \<epsilon>'_components: 
      "\<epsilon>'\<lparr>NTMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>?II\<lparr>Obj\<rparr>. (f = \<aa>\<^sub>P\<^sub>L\<^sub>2 ? h' : (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')))"
      "\<epsilon>'\<lparr>NTDom\<rparr> = cf_const ?II \<CC> r'"
      "\<epsilon>'\<lparr>NTCod\<rparr> = ?II_II"
      "\<epsilon>'\<lparr>NTDGDom\<rparr> = ?II"
      "\<epsilon>'\<lparr>NTDGCod\<rparr> = \<CC>"
      unfolding \<epsilon>'_def nt_field_simps by (simp_all add: nat_omega_simps)

    have \<epsilon>'_NTMap_app_I2: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = h'" if "x = \<aa>\<^sub>P\<^sub>L\<^sub>2" for x 
    proof-
      have "x \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>"
        unfolding that by (cs_concl cs_intro: cat_parallel_cs_intros)
      then show ?thesis unfolding \<epsilon>'_components that by simp
    qed

    have \<epsilon>'_NTMap_app_sI2: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'" if "x = \<bb>\<^sub>P\<^sub>L\<^sub>2" for x 
    proof-
      have "x \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>"
        unfolding that by (cs_concl cs_shallow cs_intro: cat_parallel_cs_intros)
      with \<epsilon>.cat_parallel_\<aa>\<bb> show ?thesis
        unfolding \<epsilon>'_components by (cs_concl cs_simp: V_cs_simps that)
    qed

    interpret par: cf_parallel_2 \<alpha> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L P\<^sub>O P\<^sub>A g' f' \<CC>
      by (intro cf_parallel_2I cat_parallel_2I)
        (simp_all add: cat_cs_intros cat_parallel_cs_intros)

    have "\<epsilon>' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
      show "vfsequence \<epsilon>'" unfolding \<epsilon>'_def by auto
      show "vcard \<epsilon>' = 5\<^sub>\<nat>" unfolding \<epsilon>'_def by (simp add: nat_omega_simps)
      from h' show "cf_const (?II) \<CC> r' : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by 
          (
            cs_concl cs_shallow 
              cs_simp: cat_parallel_cs_simps cs_intro: cat_cs_intros
          )
      from h' show "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : 
        cf_const ?II \<CC> r'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> ?II_II\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        if "a \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>" for a 
        using that
        by (elim the_cat_parallel_2_ObjE; simp only:)
          (
            cs_concl 
              cs_simp: 
                \<epsilon>'_NTMap_app_I2 \<epsilon>'_NTMap_app_sI2 
                cat_cs_simps cat_parallel_cs_simps 
              cs_intro: cat_cs_intros cat_parallel_cs_intros
          )
      from h' f' g'h'_f'h' show 
        "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> cf_const ?II \<CC> r'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
          ?II_II\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          if "f : a \<mapsto>\<^bsub>?II\<^esub> b" for a b f
          using that
          by (elim \<epsilon>.the_cat_parallel_2_is_arrE; simp only:)
            (
              cs_concl 
                cs_intro: cat_cs_intros cat_parallel_cs_intros 
                cs_simp:
                  cat_cs_simps
                  cat_parallel_cs_simps
                  \<epsilon>'_NTMap_app_I2 
                  \<epsilon>'_NTMap_app_sI2
            )+
      qed 
        (
          simp add: \<epsilon>'_components | 
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_lim_cs_intros cat_cs_intros cat_small_cs_intros 
        )+
    from \<epsilon>.cat_eq_2_unique_cone[OF this] obtain t'
      where t': "t' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E"
        and \<epsilon>'_NTMap_app: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t'"
        and unique_t':
          "\<lbrakk> t'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E; \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t''\<rbrakk> \<Longrightarrow> 
            t'' = t'" 
        for t''
      by metis

    show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> u' = \<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
    proof(intro ex1I conjI; (elim conjE)?, (rule t')?)
      show [symmetric, cat_cs_simps]: "u' = \<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t'"
      proof(rule ntcf_eqI[OF u'.is_ntcf_axioms])
        from t' show 
          "\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t' : cf_const \<JJ> \<CC> r' \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
          by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        show "u'\<lparr>NTMap\<rparr> = (\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI)
          show "vsv ((\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>)"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          from t' show 
            "\<D>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>) = \<D>\<^sub>\<circ> ((\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>)"
            by 
              (
                cs_concl cs_shallow 
                  cs_simp: cat_cs_simps cs_intro: cat_cs_intros
              )
          show "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            if "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>)" for a
          proof-
            from that have "a \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" 
              by (cs_prems cs_shallow cs_simp: cat_cs_simps)
            with t' show "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
              by 
                (
                  cs_concl 
                    cs_simp:
                      cat_cs_simps 
                      \<pi>'_NTMap_app
                      cat_parallel_cs_simps
                      the_cat_discrete_components(1)
                      \<epsilon>'_NTMap_app[symmetric]
                      \<epsilon>'_NTMap_app_I2
                      \<pi>'_NTMap_app'[symmetric]
                    cs_intro: cat_cs_intros cat_parallel_cs_intros
                )
          qed
        qed auto
      qed simp_all

      fix t'' assume prems': "t'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E" "u' = \<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t''"
      then have u'_NTMap_app_x:
        "u'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = (\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t'')\<lparr>NTMap\<rparr>\<lparr>x\<rparr>"
        for x 
        by simp
      have "?\<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t'')" 
        if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
        using u'_NTMap_app_x[of j] prems'(1) that
        by 
          (
            cs_prems 
              cs_simp:
                cat_cs_simps 
                cat_discrete_cs_simps 
                cat_parallel_cs_simps 
                the_cat_discrete_components(1) 
              cs_intro: cat_cs_intros cat_parallel_cs_intros
          ) 
          (simp add: \<pi>'_NTMap_app[OF that, symmetric])
      moreover from prems'(1) have "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>O"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_parallel_cs_simps 
              cs_intro: cat_cs_intros cat_parallel_cs_intros
          )
      ultimately have [cat_cs_simps]: "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t'' = h'" 
        by (intro unique_h') simp
      show "t'' = t'"
        by (rule unique_t', intro prems'(1)) 
          (cs_concl cs_shallow cs_simp: \<epsilon>'_NTMap_app_I2 cat_cs_simps)
      qed
    qed
 
  qed
  
  then show ?thesis using that by clarsimp

qed

lemma cat_colimit_of_cat_prod_obj_and_cat_coequalizer:
  \<comment>\<open>See Theorem 1 in Chapter V-2 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>\<aa> \<bb> \<gg> \<ff>. \<lbrakk> \<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>; \<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa> \<rbrakk> \<Longrightarrow>
      \<exists>E \<epsilon>. \<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A. tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) A \<CC> \<Longrightarrow>
      \<exists>P \<pi>. \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A. tm_cf_discrete \<alpha> (\<JJ>\<lparr>Arr\<rparr>) A \<CC> \<Longrightarrow>
      \<exists>P \<pi>. \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains r u where "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> by (rule assms(1))
  have "\<exists>E \<epsilon>. \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" for \<aa> \<bb> \<gg> \<ff>
  proof-
    from assms(2)[OF that(1,2)] obtain E \<epsilon> 
      where \<epsilon>: "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by clarsimp
    interpret \<epsilon>: is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule \<epsilon>)
    from \<epsilon>.is_cat_equalizer_2_op[unfolded cat_op_simps] show ?thesis by auto
  qed
  moreover have "\<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) A (op_cat \<CC>)" for A
  proof-
    interpret tm_cf_discrete \<alpha> \<open>\<JJ>\<lparr>Obj\<rparr>\<close> A \<open>op_cat \<CC>\<close> by (rule that)
    from assms(3)[OF tm_cf_discrete_op[unfolded cat_op_simps]] obtain P \<pi> 
      where \<pi>: "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by clarsimp 
    interpret \<pi>: is_cat_obj_coprod \<alpha> \<open>\<JJ>\<lparr>Obj\<rparr>\<close> A \<CC> P \<pi> by (rule \<pi>)
    from \<pi>.is_cat_obj_prod_op show ?thesis by auto
  qed
  moreover have "\<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Arr\<rparr>) A (op_cat \<CC>)" for A 
  proof-
    interpret tm_cf_discrete \<alpha> \<open>\<JJ>\<lparr>Arr\<rparr>\<close> A \<open>op_cat \<CC>\<close> by (rule that)
    from assms(4)[OF tm_cf_discrete_op[unfolded cat_op_simps]] obtain P \<pi> 
      where \<pi>: "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by clarsimp 
    interpret \<pi>: is_cat_obj_coprod \<alpha> \<open>\<JJ>\<lparr>Arr\<rparr>\<close> A \<CC> P \<pi> by (rule \<pi>)
    from \<pi>.is_cat_obj_prod_op show ?thesis by auto
  qed
  ultimately obtain u r where u: 
    "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by 
      (
        rule cat_limit_of_cat_prod_obj_and_cat_equalizer[
          OF \<FF>.is_tm_functor_op, unfolded cat_op_simps
          ]
      )
  interpret u: is_cat_limit \<alpha> \<open>op_cat \<JJ>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<FF>\<close> r u by (rule u)
  from u.is_cat_colimit_op[unfolded cat_op_simps] that show ?thesis by simp
qed



subsection\<open>Small-complete and small-cocomplete category\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale cat_small_complete = category \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_small_complete: 
    "\<And>\<FF> \<JJ>. \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow> \<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"

locale cat_small_cocomplete = category \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_small_cocomplete: 
    "\<And>\<FF> \<JJ>. \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow> \<exists>u r. u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"


text\<open>Rules.\<close>

mk_ide rf cat_small_complete_def[unfolded cat_small_complete_axioms_def]
  |intro cat_small_completeI|
  |dest cat_small_completeD[dest]|
  |elim cat_small_completeE[elim]|

lemma cat_small_completeE'[elim]:
  assumes "cat_small_complete \<alpha> \<CC>" and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains u r where "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by auto

mk_ide rf cat_small_cocomplete_def[unfolded cat_small_cocomplete_axioms_def]
  |intro cat_small_cocompleteI|
  |dest cat_small_cocompleteD[dest]|
  |elim cat_small_cocompleteE[elim]|

lemma cat_small_cocompleteE'[elim]:
  assumes "cat_small_cocomplete \<alpha> \<CC>" and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains u r where "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by auto


subsubsection\<open>Duality\<close>

lemma (in cat_small_complete) cat_small_cocomplete_op[cat_op_intros]:
  "cat_small_cocomplete \<alpha> (op_cat \<CC>)"
proof(intro cat_small_cocompleteI)
  fix \<FF> \<JJ> assume "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  then interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<open>op_cat \<CC>\<close> \<FF> .
  from cat_small_complete[OF \<FF>.is_tm_functor_op[unfolded cat_op_simps]]
  obtain u r where u: "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by auto
  then interpret u: is_cat_limit \<alpha> \<open>op_cat \<JJ>\<close> \<CC> \<open>op_cf \<FF>\<close> r u .
  from u.is_cat_colimit_op[unfolded cat_op_simps] show 
    "\<exists>u r. u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by auto
qed (auto intro: cat_cs_intros)

lemmas [cat_op_intros] = cat_small_complete.cat_small_cocomplete_op

lemma (in cat_small_cocomplete) cat_small_complete_op[cat_op_intros]:
  "cat_small_complete \<alpha> (op_cat \<CC>)"
proof(intro cat_small_completeI)
  fix \<FF> \<JJ> assume prems: "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  then interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<open>op_cat \<CC>\<close> \<FF> .
  from cat_small_cocomplete[OF \<FF>.is_tm_functor_op[unfolded cat_op_simps]]
  obtain u r where u: "u : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by auto
  interpret u: is_cat_colimit \<alpha> \<open>op_cat \<JJ>\<close> \<CC> \<open>op_cf \<FF>\<close> r u by (rule u)
  from u.is_cat_limit_op[unfolded cat_op_simps] show 
    "\<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by auto
qed (auto intro: cat_cs_intros)

lemmas [cat_op_intros] = cat_small_cocomplete.cat_small_complete_op


subsubsection\<open>A category with equalizers and small products is small-complete\<close>

lemma (in category) cat_small_complete_if_eq_and_obj_prod:
  \<comment>\<open>See Corollary 2 in Chapter V-2 in \cite{mac_lane_categories_2010}\<close>
  assumes "\<And>\<aa> \<bb> \<gg> \<ff>. \<lbrakk> \<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>; \<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb> \<rbrakk> \<Longrightarrow>
      \<exists>E \<epsilon>. \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A I. tm_cf_discrete \<alpha> I A \<CC> \<Longrightarrow> \<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cat_small_complete \<alpha> \<CC>"
proof(intro cat_small_completeI)
  fix \<FF> \<JJ> assume prems: "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  then interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> .
  show "\<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (rule cat_limit_of_cat_prod_obj_and_cat_equalizer[OF prems assms(1)])
      (auto intro: assms(2))
qed (auto simp: cat_cs_intros)

lemma (in category) cat_small_cocomplete_if_eq_and_obj_prod:
  assumes "\<And>\<aa> \<bb> \<gg> \<ff>. \<lbrakk> \<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>; \<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa> \<rbrakk> \<Longrightarrow>
    \<exists>E \<epsilon>. \<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A I. tm_cf_discrete \<alpha> I A \<CC> \<Longrightarrow> \<exists>P \<pi>. \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cat_small_cocomplete \<alpha> \<CC>"
proof-
  have "\<exists>E \<epsilon>. \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" and "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" for \<aa> \<bb> \<gg> \<ff>
  proof-
    from assms(1)[OF that] obtain \<epsilon> E where 
      \<epsilon>: "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by clarsimp
    interpret \<epsilon>: is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule \<epsilon>)
    from \<epsilon>.is_cat_equalizer_2_op show ?thesis by auto
  qed
  moreover have "\<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "tm_cf_discrete \<alpha> I A (op_cat \<CC>)" for A I
  proof-
    interpret tm_cf_discrete \<alpha> I A \<open>op_cat \<CC>\<close> by (rule that)
    from assms(2)[OF tm_cf_discrete_op[unfolded cat_op_simps]] obtain P \<pi> 
      where \<pi>: "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by auto
    interpret \<pi>: is_cat_obj_coprod \<alpha> I A \<CC> P \<pi> by (rule \<pi>)
    from \<pi>.is_cat_obj_prod_op show ?thesis by auto
  qed
  ultimately interpret cat_small_complete \<alpha> \<open>op_cat \<CC>\<close>
    by 
      (
        rule category.cat_small_complete_if_eq_and_obj_prod[
          OF category_op, unfolded cat_op_simps
          ]
      )
  show ?thesis by (rule cat_small_cocomplete_op[unfolded cat_op_simps])
qed


subsubsection\<open>
Existence of the initial and terminal objects in 
small-complete and small-cocomplete categories
\<close>

lemma (in cat_small_complete) cat_sc_ex_obj_initial:
  \<comment>\<open>See Theorem 1 in Chapter V-6 in \cite{mac_lane_categories_2010}.\<close>
  assumes "A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "A \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<exists>f a. a \<in>\<^sub>\<circ> A \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
  obtains z where "obj_initial \<CC> z"
proof-
  
  interpret tcd: tm_cf_discrete \<alpha> A id \<CC>
  proof(intro tm_cf_discreteI)
    show "(\<lambda>i\<in>\<^sub>\<circ>A. \<CC>\<lparr>CId\<rparr>\<lparr>id i\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      unfolding id_def
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      from assms(1) have "A \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>)" by (simp add: cat_CId_vdomain)
      then have "\<R>\<^sub>\<circ> (VLambda A (app (\<CC>\<lparr>CId\<rparr>))) = \<CC>\<lparr>CId\<rparr> `\<^sub>\<circ> A" by auto
      moreover have "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>A. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
        by (rule cat_Hom_vifunion_in_Vset[OF assms(1,1,2,2)])
      moreover have "\<CC>\<lparr>CId\<rparr> `\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>A. Hom \<CC> a b)"
      proof(intro vsubsetI)
        fix f assume "f \<in>\<^sub>\<circ> \<CC>\<lparr>CId\<rparr> `\<^sub>\<circ> A"
        then obtain a where a: "a \<in>\<^sub>\<circ> A" and f_def: "f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>" by auto
        from assms(1) a show "f \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>A. Hom \<CC> a b)"
          unfolding f_def by (intro vifunionI) (auto simp: cat_CId_is_arr)
      qed
      ultimately show "\<R>\<^sub>\<circ> (VLambda A (app (\<CC>\<lparr>CId\<rparr>))) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
    qed (simp_all add: assms(2))
  qed 
    (
      use assms in 
        \<open>auto simp: assms(2) Limit_vid_on_in_Vset intro: cat_cs_intros\<close>
    )

  have tcd: ":\<rightarrow>: A id \<CC> : :\<^sub>C A \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by 
      (
        cs_concl cs_shallow cs_intro: 
          cat_small_cs_intros 
          cat_cs_intros 
          cat_small_discrete_cs_intros
          cat_discrete_cs_intros
      )
  from cat_small_complete[OF this] obtain \<pi> w 
    where "\<pi> : w <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m :\<rightarrow>: A id \<CC> : :\<^sub>C A \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by auto
  then interpret \<pi>: is_cat_obj_prod \<alpha> A id \<CC> w \<pi>
    by (intro is_cat_obj_prodI tcd.cf_discrete_axioms)

  let ?ww = \<open>Hom \<CC> w w\<close>

  have CId_w: "\<CC>\<lparr>CId\<rparr>\<lparr>w\<rparr> \<in>\<^sub>\<circ> ?ww"
    by (cs_concl cs_intro: cat_cs_intros cat_lim_cs_intros)
  then have ww_neq_vempty: "?ww \<noteq> 0" by force

  have wd: "\<exists>h. h : w \<mapsto>\<^bsub>\<CC>\<^esub> d" if "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for d
  proof-
    from assms(3)[OF that] obtain g a where a: "a \<in>\<^sub>\<circ> A" and g: "g : a \<mapsto>\<^bsub>\<CC>\<^esub> d"
      by clarsimp
    from \<pi>.ntcf_NTMap_is_arr[unfolded the_cat_discrete_components, OF a] a g 
    have "\<pi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : w \<mapsto>\<^bsub>\<CC>\<^esub> a"
      by
        (
          cs_prems cs_shallow cs_simp:
            id_apply the_cat_discrete_components(1) 
            cat_discrete_cs_simps cat_cs_simps
        )
    with g have "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : w \<mapsto>\<^bsub>\<CC>\<^esub> d"
      by (cs_concl cs_shallow cs_intro: cat_cs_intros)
    then show ?thesis by (intro exI)
  qed

  have "cf_parallel \<alpha> (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww w w (vid_on ?ww) \<CC>"
    by (intro cat_cf_parallel_\<aa>\<bb> \<pi>.cat_cone_obj cat_Hom_in_Vset) simp_all
  then have "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww w w (vid_on ?ww) :
    \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by (intro cf_parallel.cf_parallel_the_cf_parallel_is_tm_functor)
  from cat_small_complete[OF this] obtain \<epsilon> v where \<epsilon>: "\<epsilon> :
    v <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww w w (vid_on ?ww) :
    \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by clarsimp
  from is_cat_equalizerI[
      OF
        this
        _ 
        cat_Hom_in_Vset[OF \<pi>.cat_cone_obj \<pi>.cat_cone_obj]
        ww_neq_vempty
      ]
  interpret \<epsilon>: is_cat_equalizer \<alpha> w w ?ww \<open>vid_on ?ww\<close> \<CC> v \<epsilon> by auto
  note \<epsilon>_is_monic_arr = 
    is_cat_equalizer.cat_eq_is_monic_arr[OF \<epsilon>.is_cat_equalizer_axioms]
  note \<epsilon>_is_monic_arrD = is_monic_arrD[OF \<epsilon>_is_monic_arr]

  show ?thesis
  proof(rule, intro obj_initialI)

    show "v \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (rule \<epsilon>.cat_cone_obj)
    then have CId_v: "\<CC>\<lparr>CId\<rparr>\<lparr>v\<rparr> : v \<mapsto>\<^bsub>\<CC>\<^esub> v" 
      by (cs_concl cs_shallow cs_intro: cat_cs_intros)

    fix d assume prems: "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    from wd[OF prems] obtain h where h: "h : w \<mapsto>\<^bsub>\<CC>\<^esub> d" by auto

    show "\<exists>!f. f : v \<mapsto>\<^bsub>\<CC>\<^esub> d"
    proof(rule ex1I)
      define f where "f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>"
      from \<epsilon>_is_monic_arrD(1) h show f: "f : v \<mapsto>\<^bsub>\<CC>\<^esub> d"
        unfolding f_def by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      fix g assume prems': "g : v \<mapsto>\<^bsub>\<CC>\<^esub> d"
      have "cf_parallel_2 \<alpha> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L v d g f \<CC>"
        by (intro cat_cf_parallel_2_cat_equalizer prems' f)
      then have "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L v d g f :
        \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
        by (intro cf_parallel_2.cf_parallel_2_the_cf_parallel_2_is_tm_functor)
      from cat_small_complete[OF this] obtain \<epsilon>' u 
        where "\<epsilon>' :
          u <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L v d g f :
          \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by clarsimp
      from is_cat_equalizer_2I[OF this prems' f] interpret \<epsilon>': 
        is_cat_equalizer_2 \<alpha> v d g f \<CC> u \<epsilon>'.
      note \<epsilon>'_is_monic_arr = is_cat_equalizer_2.cat_eq_2_is_monic_arr[
        OF \<epsilon>'.is_cat_equalizer_2_axioms
        ]
      note \<epsilon>'_is_monic_arrD = is_monic_arrD[OF \<epsilon>'_is_monic_arr]
      then have "u \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
      from wd[OF this] obtain s where s: "s : w \<mapsto>\<^bsub>\<CC>\<^esub> u" by clarsimp
      from s \<epsilon>'_is_monic_arrD(1) \<epsilon>_is_monic_arrD(1) have \<epsilon>\<epsilon>'s:
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s : w \<mapsto>\<^bsub>\<CC>\<^esub> w"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      from s \<epsilon>'_is_monic_arrD(1) \<epsilon>_is_monic_arrD(1) have \<epsilon>'s\<epsilon>:
        "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> : v \<mapsto>\<^bsub>\<CC>\<^esub> v"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from \<epsilon>_is_monic_arrD(1) \<epsilon>'_is_monic_arrD(1) s have 
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>) =
          \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      also from
        \<epsilon>.cat_eq_Comp_eq
          [
            unfolded in_Hom_iff, OF cat_CId_is_arr[OF \<pi>.cat_cone_obj] \<epsilon>\<epsilon>'s,
            symmetric
          ]
        \<epsilon>\<epsilon>'s \<pi>.cat_cone_obj \<epsilon>_is_monic_arr(1)
      have "\<dots> = \<CC>\<lparr>CId\<rparr>\<lparr>w\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>"
        by (cs_prems cs_shallow cs_simp: vid_on_atI cs_intro:  cat_cs_intros)
      also from \<epsilon>.cf_parallel_\<aa>' \<epsilon>_is_monic_arrD(1) have 
        "\<dots> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>v\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro:  cat_cs_intros)
      finally have
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>) =
          \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>v\<rparr>".      
      from 
        is_monic_arrD(2)[OF \<epsilon>_is_monic_arr \<epsilon>'s\<epsilon> CId_v this] 
        \<epsilon>'_is_monic_arrD(1) s \<epsilon>_is_monic_arrD(1) 
      have \<epsilon>'s\<epsilon>_is_CId: 
        "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>) = \<CC>\<lparr>CId\<rparr>\<lparr>v\<rparr>"
        by (cs_prems cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      have \<epsilon>'_is_iso_arr: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> : u \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> v"
        by 
        (
          intro 
            cat_is_iso_arr_if_is_monic_arr_is_right_inverse 
            \<epsilon>'_is_monic_arr,
          rule is_right_inverseI[OF _ \<epsilon>'_is_monic_arrD(1) \<epsilon>'s\<epsilon>_is_CId]
        )
        (
          use s \<epsilon>_is_monic_arrD(1) in 
            \<open>cs_concl cs_shallow cs_intro: cat_cs_intros\<close>
        )
      from \<epsilon>'.cat_eq_2_Comp_eq(1) have 
        "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> =
          f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>"
        by simp      
      from this f \<epsilon>'_is_monic_arrD(1) \<epsilon>'_is_iso_arr prems' show "g = f"
        by
          (
            cs_prems cs_shallow
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_arrow_cs_intros
          )
    qed

  qed

qed

lemma (in cat_small_cocomplete) cat_sc_ex_obj_terminal:
  \<comment>\<open>See Theorem 1 in Chapter V-6 in \cite{mac_lane_categories_2010}.\<close>
  assumes "A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "A \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<exists>f a. a \<in>\<^sub>\<circ> A \<and> f : c \<mapsto>\<^bsub>\<CC>\<^esub> a"
  obtains z where "obj_terminal \<CC> z"
  using that 
  by 
    (
      rule cat_small_complete.cat_sc_ex_obj_initial[
        OF cat_small_complete_op, unfolded cat_op_simps, OF assms, simplified
        ]
    )


subsubsection\<open>Creation of limits, continuity and completeness\<close>

lemma
  \<comment>\<open>See Theorem 2 in Chapter V-4 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "cat_small_complete \<alpha> \<BB>"
    and "\<And>\<FF> \<JJ>. \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA> \<Longrightarrow> \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>\<FF> \<JJ>. \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA> \<Longrightarrow> cf_creates_limits \<alpha> \<GG> \<FF>"
  shows is_tm_cf_continuous_if_cf_creates_limits: "is_tm_cf_continuous \<alpha> \<GG>"
    and cat_small_complete_if_cf_creates_limits: "cat_small_complete \<alpha> \<AA>"
proof-

  interpret \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  interpret \<BB>: cat_small_complete \<alpha> \<BB> by (rule assms(2))

  show "is_tm_cf_continuous \<alpha> \<GG>"
  proof(intro is_tm_cf_continuousI, rule assms)
    fix \<FF> \<JJ> assume prems: "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    then interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<AA> \<FF> .
    from cat_small_completeD(2)[OF assms(2) assms(3)[OF prems]] obtain \<psi> r
      where \<psi>: "\<psi> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by clarsimp
    show "cf_preserves_limits \<alpha> \<GG> \<FF>"
      by 
        (
          rule cf_preserves_limits_if_cf_creates_limits, 
          rule assms(1),
          rule \<FF>.is_functor_axioms,
          rule \<psi>,
          rule assms(4)[OF prems]
        )
  qed

  show "cat_small_complete \<alpha> \<AA>"
  proof(intro cat_small_completeI \<GG>.HomDom.category_axioms)
    fix \<FF> \<JJ> assume prems: "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    then interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<AA> \<FF> .
    from cat_small_completeD(2)[OF assms(2) assms(3)[OF prems]] obtain \<psi> r
      where \<psi>: "\<psi> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by clarsimp
    from cf_creates_limitsE''[
        OF assms(4)[OF prems] \<psi> \<FF>.is_functor_axioms assms(1)
        ]
    show "\<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by metis
  qed

qed



subsection\<open>Finite-complete and finite-cocomplete category\<close>

locale cat_finite_complete = category \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_finite_complete: 
    "\<And>\<FF> \<JJ>. \<lbrakk> finite_category \<alpha> \<JJ>; \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<rbrakk> \<Longrightarrow> 
      \<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"

locale cat_finite_cocomplete = category \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_finite_cocomplete: 
    "\<And>\<FF> \<JJ>. \<lbrakk> finite_category \<alpha> \<JJ>; \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<rbrakk> \<Longrightarrow> 
      \<exists>u r. u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"


text\<open>Rules.\<close>

mk_ide rf cat_finite_complete_def[unfolded cat_finite_complete_axioms_def]
  |intro cat_finite_completeI|
  |dest cat_finite_completeD[dest]|
  |elim cat_finite_completeE[elim]|

lemma cat_finite_completeE'[elim]:
  assumes "cat_finite_complete \<alpha> \<CC>" 
    and "finite_category \<alpha> \<JJ>" 
    and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains u r where "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by auto

mk_ide rf cat_finite_cocomplete_def[unfolded cat_finite_cocomplete_axioms_def]
  |intro cat_finite_cocompleteI|
  |dest cat_finite_cocompleteD[dest]|
  |elim cat_finite_cocompleteE[elim]|

lemma cat_finite_cocompleteE'[elim]:
  assumes "cat_finite_cocomplete \<alpha> \<CC>" 
    and "finite_category \<alpha> \<JJ>" 
    and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains u r where "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by auto


text\<open>Elementary properties.\<close>

sublocale cat_small_complete \<subseteq> cat_finite_complete
proof(intro cat_finite_completeI)
  fix \<FF> \<JJ> assume prems: "finite_category \<alpha> \<JJ>" "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  interpret \<FF>: is_functor \<alpha> \<JJ> \<CC> \<FF> by (rule prems(2))
  from cat_small_complete_axioms show "\<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (auto intro: \<FF>.cf_is_tm_functor_if_HomDom_finite_category[OF prems(1)])
qed (auto intro: cat_cs_intros)

sublocale cat_small_cocomplete \<subseteq> cat_finite_cocomplete
proof(intro cat_finite_cocompleteI)
  fix \<FF> \<JJ> assume prems: "finite_category \<alpha> \<JJ>" "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  interpret \<FF>: is_functor \<alpha> \<JJ> \<CC> \<FF> by (rule prems(2))
  from cat_small_cocomplete_axioms show "\<exists>u r. u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (auto intro: \<FF>.cf_is_tm_functor_if_HomDom_finite_category[OF prems(1)])
qed (auto intro: cat_cs_intros)

text\<open>\newpage\<close>

end