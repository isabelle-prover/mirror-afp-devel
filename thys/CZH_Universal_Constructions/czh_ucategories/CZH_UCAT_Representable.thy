(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Representable and corepresentable functors\<close>
theory CZH_UCAT_Representable
  imports
    CZH_Elementary_Categories.CZH_ECAT_Yoneda
    CZH_UCAT_Pointed
    CZH_UCAT_Limit
begin



subsection\<open>Representable and corepresentable functors\<close>


subsubsection\<open>Definitions and elementary properties\<close>


text\<open>
See Chapter III-2 in \<^cite>\<open>"mac_lane_categories_2010"\<close> 
or Section 2.1 in \<^cite>\<open>"riehl_category_2016"\<close>.
\<close>

definition cat_representation :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "cat_representation \<alpha> \<FF> c \<psi> \<longleftrightarrow>
    c \<in>\<^sub>\<circ> \<FF>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr> \<and>
    \<psi> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomDom\<rparr>(c,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"

definition cat_corepresentation :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "cat_corepresentation \<alpha> \<FF> c \<psi> \<longleftrightarrow>
    c \<in>\<^sub>\<circ> \<FF>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr> \<and>
    \<psi> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat (\<FF>\<lparr>HomDom\<rparr>)(-,c) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"


text\<open>Rules.\<close>

context
  fixes \<alpha> \<CC> \<FF>
  assumes \<FF>: "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
begin

interpretation \<FF>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> by (rule \<FF>)

mk_ide rf cat_representation_def[where \<alpha>=\<alpha> and \<FF>=\<FF>, unfolded cat_cs_simps]
  |intro cat_representationI|
  |dest cat_representationD'|
  |elim cat_representationE'|

end

lemmas cat_representationD[dest] = cat_representationD'[rotated]
  and  cat_representationE[elim] = cat_representationE'[rotated]

lemma cat_corepresentationI:
  assumes "category \<alpha> \<CC>"
    and "\<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<psi> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,c) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "cat_corepresentation \<alpha> \<FF> c \<psi>"
proof-
  interpret category \<alpha> \<CC> by (rule assms(1)) 
  interpret \<FF>: is_functor \<alpha> \<open>op_cat \<CC>\<close> \<open>cat_Set \<alpha>\<close> \<FF> by (rule assms(2))
  note [cat_op_simps] = \<FF>.HomDom.cat_op_cat_cf_Hom_snd[
      symmetric, unfolded cat_op_simps, OF assms(3)
      ]
  show ?thesis
    unfolding cat_corepresentation_def
    by (intro conjI, unfold cat_cs_simps cat_op_simps; intro assms)
qed

lemma cat_corepresentationD:
  assumes "cat_corepresentation \<alpha> \<FF> c \<psi>"
    and "category \<alpha> \<CC>"
    and "\<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<psi> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,c) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  interpret category \<alpha> \<CC> by (rule assms(2)) 
  interpret \<FF>: is_functor \<alpha> \<open>op_cat \<CC>\<close> \<open>cat_Set \<alpha>\<close> \<FF> by (rule assms(3))
  note c\<psi> = cat_corepresentation_def[
      THEN iffD1, OF assms(1), unfolded cat_cs_simps cat_op_simps
      ]
  from c\<psi>(1) show c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  note [cat_op_simps] = \<FF>.HomDom.cat_op_cat_cf_Hom_snd[
      symmetric, unfolded cat_op_simps, OF c
      ]
  show "\<psi> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,c) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (rule conjunct2[OF c\<psi>, unfolded cat_op_simps])
qed

lemma cat_corepresentationE:
  assumes "cat_corepresentation \<alpha> \<FF> c \<psi>"
    and "category \<alpha> \<CC>"
    and "\<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  obtains "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<psi> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,c) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  by (simp add: cat_corepresentationD[OF assms])


subsubsection\<open>Representable functors and universal arrows\<close>

lemma universal_arrow_of_if_cat_representation:
  \<comment>\<open>See Proposition 2 in Chapter III-2 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "cat_representation \<alpha> \<KK> r \<psi>"
    and "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "universal_arrow_of
    \<KK> (set {\<aa>}) r (ntcf_paa \<aa> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>) (\<psi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>))"
proof-
  note r\<psi> = cat_representationD[OF assms(2,1)]
  interpret \<KK>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<KK> by (rule assms(1))
  interpret \<psi>: is_iso_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<close> \<KK> \<psi> 
    by (rule r\<psi>(2))
  from assms(3) have set_\<aa>: "set {\<aa>} \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    by (simp add: Limit_vsingleton_in_VsetI cat_Set_components(1))
  from
    ntcf_cf_comp_is_iso_ntcf[
      OF \<KK>.ntcf_pointed_inv_is_iso_ntcf[OF assms(3)] assms(1)
      ]
  have \<aa>\<KK>: "ntcf_pointed_inv \<alpha> \<aa> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> :
    \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha> (set {\<aa>},-) \<circ>\<^sub>C\<^sub>F \<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_prems cs_simp: cat_cs_simps)
  from iso_ntcf_is_iso_arr(1)[OF \<aa>\<KK>] r\<psi> assms(3) have [cat_cs_simps]:
    "((ntcf_pointed_inv \<alpha> \<aa> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<psi>)\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>) =
      ntcf_paa \<aa> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>) (\<psi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>)"
    by
      (
        cs_concl
          cs_simp: cat_cs_simps
          cs_intro: cat_Set_cs_intros cat_cs_intros cat_op_intros
      )
  show "universal_arrow_of
    \<KK> (set {\<aa>}) r (ntcf_paa \<aa> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>) (\<psi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>))"
    by
      (
        rule \<KK>.cf_universal_arrow_of_if_is_iso_ntcf
          [
            OF r\<psi>(1) set_\<aa> ntcf_vcomp_is_iso_ntcf[OF \<aa>\<KK> r\<psi>(2)], 
            unfolded cat_cs_simps
          ]
      )
qed

lemma universal_arrow_of_if_cat_corepresentation:
  \<comment>\<open>See Proposition 2 in Chapter III-2 in \cite{mac_lane_categories_2010}.\<close>
  assumes "category \<alpha> \<CC>"
    and "\<KK> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "cat_corepresentation \<alpha> \<KK> r \<psi>"
    and "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "universal_arrow_of
    \<KK> (set {\<aa>}) r (ntcf_paa \<aa> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>) (\<psi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>))"
proof-
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(1))
  note r\<psi> = cat_corepresentationD[OF assms(3,1,2)]
  note [cat_op_simps] = \<CC>.cat_op_cat_cf_Hom_snd[OF r\<psi>(1)]
  have rep: "cat_representation \<alpha> \<KK> r \<psi>"
    by (intro cat_representationI, rule assms(2), unfold cat_op_simps; rule r\<psi>)
  show ?thesis
    by 
      (
        rule universal_arrow_of_if_cat_representation[
          OF assms(2) rep assms(4), unfolded cat_op_simps
          ]
      )
qed

lemma cat_representation_if_universal_arrow_of:
  \<comment>\<open>See Proposition 2 in Chapter III-2 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "universal_arrow_of \<KK> (set {\<aa>}) r u"
  shows "cat_representation \<alpha> \<KK> r (Yoneda_arrow \<alpha> \<KK> r (u\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>))"
proof-

  let ?Y = \<open>Yoneda_component \<KK> r (u\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>)\<close>

  interpret \<KK>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<KK> by (rule assms(1))

  note ua = \<KK>.universal_arrow_ofD[OF assms(3)]

  from ua(2) have u\<aa>: "u\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr> \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    by 
      (
        cs_concl cs_shallow 
          cs_intro: V_cs_intros cat_Set_cs_intros cat_cs_intros
      )

  have [cat_cs_simps]: "Yoneda_arrow \<alpha> \<KK> r (u\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>NTMap\<rparr>\<lparr>c\<rparr> = ?Y c"
    if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c
    using that 
    by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from ua(1) have [cat_cs_simps]: "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> = Hom \<CC> r c"
    if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c
    using that 
    by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_op_intros)

  show ?thesis
  proof
    (
      intro cat_representationI is_iso_ntcfI, 
      rule assms(1), 
      rule ua(1), 
      rule \<KK>.HomDom.cat_Yoneda_arrow_is_ntcf[OF assms(1) ua(1) u\<aa>],
      rule cat_Set_is_iso_arrI,
      simp_all only: cat_cs_simps 
    )

    fix c assume prems: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    with ua(1,2) show Yc: "?Y c : Hom \<CC> r c \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
      by 
        (
          cs_concl cs_shallow 
            cs_intro: V_cs_intros cat_Set_cs_intros cat_cs_intros
        )

    note YcD = cat_Set_is_arrD[OF Yc]

    interpret Yc: arr_Set \<alpha> \<open>?Y c\<close> by (rule YcD(1))

    show dom_Yc: "\<D>\<^sub>\<circ> (?Y c\<lparr>ArrVal\<rparr>) = Hom \<CC> r c"
      by (simp add: \<KK>.Yoneda_component_ArrVal_vdomain)

    show "v11 (?Y c\<lparr>ArrVal\<rparr>)"
    proof(intro Yc.ArrVal.vsv_valeq_v11I, unfold dom_Yc in_Hom_iff)

      fix g f assume prems': 
        "g : r \<mapsto>\<^bsub>\<CC>\<^esub> c" "f : r \<mapsto>\<^bsub>\<CC>\<^esub> c" "?Y c\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> = ?Y c\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"

      from prems have c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto

      from prems'(3,1,2) have \<KK>gu\<aa>_\<KK>fu\<aa>:
        "\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<lparr>ArrVal\<rparr>\<lparr>u\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>\<rparr> = \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>u\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>\<rparr>"
        by (cs_prems cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

      from prems'(1,2) ua(1,2) have \<KK>g_u: 
        "\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
        and \<KK>f_u: 
        "\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+
      then have dom_lhs: "\<D>\<^sub>\<circ> ((\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u)\<lparr>ArrVal\<rparr>) = set {\<aa>}"
        and dom_rhs: "\<D>\<^sub>\<circ> ((\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u)\<lparr>ArrVal\<rparr>) = set {\<aa>}"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps)+

      have \<KK>g_\<KK>f: "\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u = \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u"
      proof(rule arr_Set_eqI)
        from \<KK>g_u show arr_Set_\<KK>g_u: "arr_Set \<alpha> (\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u)"
          by (auto dest: cat_Set_is_arrD)
        from \<KK>f_u show arr_Set_\<KK>f_u: "arr_Set \<alpha> (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u)"
          by (auto dest: cat_Set_is_arrD)
        show 
          "(\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u)\<lparr>ArrVal\<rparr> =
            (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u)\<lparr>ArrVal\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs vsingleton_iff; (simp only:)?)
          from prems'(1,2) ua(2) show 
            "(\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u)\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr> =
              (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u)\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>"
            by
              (
                cs_concl cs_shallow
                  cs_simp: cat_cs_simps \<KK>gu\<aa>_\<KK>fu\<aa> 
                  cs_intro: V_cs_intros cat_cs_intros
              )
        qed (use arr_Set_\<KK>g_u arr_Set_\<KK>f_u in auto)
      qed (use \<KK>g_u \<KK>f_u in \<open>cs_concl cs_shallow cs_simp: cat_cs_simps\<close>)+
      from prems'(1) ua(2) have
        "\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from ua(3)[OF c this] obtain h where h: "h : r \<mapsto>\<^bsub>\<CC>\<^esub> c"
        and \<KK>g_u_def: 
          "\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u = umap_of \<KK> (set {\<aa>}) r u c\<lparr>ArrVal\<rparr>\<lparr>h\<rparr>"
        and h_unique: "\<And>h'.
          \<lbrakk>
            h' : r \<mapsto>\<^bsub>\<CC>\<^esub> c;
            \<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u = umap_of \<KK> (set {\<aa>}) r u c\<lparr>ArrVal\<rparr>\<lparr>h'\<rparr>
          \<rbrakk> \<Longrightarrow> h' = h"
        by metis
      from prems'(1,2) ua(2) have
        "\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u = umap_of \<KK> (set {\<aa>}) r u c\<lparr>ArrVal\<rparr>\<lparr>g\<rparr>"
        "\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u = umap_of \<KK> (set {\<aa>}) r u c\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
        by 
          (
            cs_concl cs_shallow 
              cs_simp: cat_cs_simps \<KK>g_\<KK>f cs_intro: cat_cs_intros
          )+
      from h_unique[OF prems'(1) this(1)] h_unique[OF prems'(2) this(2)] show 
        "g = f"
        by simp
    qed

    show "\<R>\<^sub>\<circ> (?Y c\<lparr>ArrVal\<rparr>) = \<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    proof
      (
        intro 
          vsubset_antisym Yc.arr_Par_ArrVal_vrange[unfolded YcD] 
          vsubsetI
      ) 
      fix y assume prems': "y \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
      from prems have \<KK>c: "\<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      from ua(3)[OF prems \<KK>.ntcf_paa_is_arr[OF assms(2) \<KK>c prems']] obtain f 
        where f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> c"
          and ntcf_paa_y:
            "ntcf_paa \<aa> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) y = umap_of \<KK> (set {\<aa>}) r u c\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
          and f_unique: "\<And>f'.
            \<lbrakk>
              f' : r \<mapsto>\<^bsub>\<CC>\<^esub> c;
              ntcf_paa \<aa> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) y = umap_of \<KK> (set {\<aa>}) r u c\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
            \<rbrakk> \<Longrightarrow> f' = f"
        by metis
      from ntcf_paa_y f ua(2) have 
        "ntcf_paa \<aa> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) y = \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u"
        by (cs_prems cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      then have 
        "ntcf_paa \<aa> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) y\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr> =
          (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u)\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>"
        by simp
      from this f ua(2) have [symmetric, cat_cs_simps]: 
        "y = \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>u\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>\<rparr>"
        by 
          (
            cs_prems cs_shallow
              cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_cs_intros
          )
      show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (?Y c\<lparr>ArrVal\<rparr>)"
        by (intro Yc.ArrVal.vsv_vimageI2')
          (
            use f in 
              \<open>
                cs_concl cs_shallow
                  cs_simp: cat_cs_simps cs_intro: cat_cs_intros
              \<close>
          )+
    qed
  qed

qed

lemma cat_corepresentation_if_universal_arrow_of:
  \<comment>\<open>See Proposition 2 in Chapter III-2 in \cite{mac_lane_categories_2010}.\<close>
  assumes "category \<alpha> \<CC>"
    and "\<KK> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "universal_arrow_of \<KK> (set {\<aa>}) r u"
  shows "cat_corepresentation \<alpha> \<KK> r (Yoneda_arrow \<alpha> \<KK> r (u\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>))"
proof-
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(1))
  interpret \<KK>: is_functor \<alpha> \<open>op_cat \<CC>\<close> \<open>cat_Set \<alpha>\<close> \<KK> by (rule assms(2))
  note ua = \<KK>.universal_arrow_ofD[OF assms(4), unfolded cat_op_simps]
  note [cat_op_simps] = \<CC>.cat_op_cat_cf_Hom_snd[OF ua(1)]
  show ?thesis
    by 
      (
        intro cat_corepresentationI,
        rule assms(1),
        rule assms(2),
        rule ua(1),
        rule cat_representationD(2)
          [
            OF
              cat_representation_if_universal_arrow_of[OF assms(2,3,4)] 
              assms(2),
            unfolded cat_op_simps
          ]
      )
qed



subsection\<open>Limits and colimits as universal cones\<close>

lemma is_tm_cat_limit_if_cat_corepresentation:
  \<comment>\<open>See Definition 3.1.5 in Section 3.1 in \cite{riehl_category_2016}.\<close>
  assumes "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "cat_corepresentation \<alpha> (tm_cf_Cone \<alpha> \<FF>) r \<psi>"
    (is \<open>cat_corepresentation \<alpha> ?Cone r \<psi>\<close>)
  shows "ntcf_of_ntcf_arrow \<JJ> \<CC> (\<psi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>) :
    r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    (is \<open>ntcf_of_ntcf_arrow \<JJ> \<CC> ?\<psi>r1r : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>\<close>)
proof-

  let ?P = \<open>ntcf_paa 0\<close> and ?Funct = \<open>cat_Funct \<alpha> \<JJ> \<CC>\<close>

  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> by (rule assms(1))
  interpret Funct: category \<alpha> ?Funct
    by
      (
        cs_concl cs_shallow cs_intro: 
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  note r\<psi> = cat_corepresentationD[
      OF assms(2) \<FF>.HomCod.category_axioms \<FF>.tm_cf_cf_Cone_is_functor
      ]
  interpret \<psi>: is_iso_ntcf \<alpha> \<open>op_cat \<CC>\<close> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,r)\<close> ?Cone \<psi>
    by (rule r\<psi>(2))
  have 0: "0 \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" unfolding cat_Set_components by auto
  note ua = universal_arrow_of_if_cat_corepresentation[
      OF \<FF>.HomCod.category_axioms \<FF>.tm_cf_cf_Cone_is_functor assms(2) 0
      ]

  show ?thesis
  proof(rule is_tm_cat_limitI')
    
    from r\<psi>(1) have [cat_FUNCT_cs_simps]:
      "cf_of_cf_map \<JJ> \<CC> (cf_map (cf_const \<JJ> \<CC> r)) = cf_const \<JJ> \<CC> r"
      by
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<psi>.ntcf_NTMap_is_arr[unfolded cat_op_simps, OF r\<psi>(1)] r\<psi>(1) have 
      "\<psi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr> :
        Hom \<CC> r r \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom ?Funct (cf_map (cf_const \<JJ> \<CC> r)) (cf_map \<FF>)"
      by
        (
          cs_prems 
            cs_simp: cat_small_cs_simps cat_cs_simps cat_op_simps
            cs_intro: cat_cs_intros
        )
    with r\<psi>(1) have \<psi>r_r: 
      "?\<psi>r1r : cf_map (cf_const \<JJ> \<CC> r) \<mapsto>\<^bsub>?Funct\<^esub> cf_map \<FF>"
      by
        (
          cs_concl cs_shallow cs_intro:
            cat_Set_cs_intros cat_cs_intros in_Hom_iff[symmetric]
        )

    from r\<psi>(1) cat_Funct_is_arrD(1)[OF \<psi>r_r, unfolded cat_FUNCT_cs_simps]
    show "ntcf_of_ntcf_arrow \<JJ> \<CC> ?\<psi>r1r : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
      by (intro is_tm_cat_coneI) 
        (cs_concl cs_shallow cs_intro: cat_cs_intros cat_small_cs_intros)

    fix r' u' assume "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    then interpret u': is_tm_cat_cone \<alpha> r' \<JJ> \<CC> \<FF> u' .

    have Cone_r': "tm_cf_Cone \<alpha> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
      by (cs_concl cs_intro: cat_lim_cs_intros cat_cs_intros cat_op_intros)
    from r\<psi>(1) have Cone_r: "tm_cf_Cone \<alpha> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
      by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)
    from r\<psi>(1) have \<psi>r1r: 
      "\<psi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> \<in>\<^sub>\<circ> tm_cf_Cone \<alpha> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
      by
        (
          cs_concl cs_shallow
            cs_simp: cat_small_cs_simps cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros
        )
    have u': "ntcf_arrow u' \<in>\<^sub>\<circ> ?Cone\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"
      by
        (
          cs_concl 
            cs_simp: cat_small_cs_simps
            cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros cat_cs_intros
        )

    have [cat_cs_simps]: 
      "cf_of_cf_map \<JJ> \<CC> (cf_map \<FF>) = \<FF>"
      "cf_of_cf_map \<JJ> \<CC> (cf_map (cf_const \<JJ> \<CC> r)) = cf_const \<JJ> \<CC> r"
      by (cs_concl cs_simp: cat_FUNCT_cs_simps)+

    from Cone_r 0 \<psi>r1r r\<psi>(1) have \<psi>r1r_is_arr: "\<psi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> :
      cf_map (cf_const \<JJ> \<CC> r) \<mapsto>\<^bsub>?Funct\<^esub> cf_map \<FF>"
      by
        (
          cs_concl cs_shallow
            cs_simp: cat_cs_simps cat_small_cs_simps 
            cs_intro: cat_cs_intros cat_op_intros
        )

    from r\<psi>(1) have [cat_cs_intros]:
      "Hom ?Funct (cf_map (cf_const \<JJ> \<CC> r)) (cf_map \<FF>) \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
      unfolding cat_Set_components(1)
      by (intro Funct.cat_Hom_in_Vset)
        (
          cs_concl
            cs_simp: cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros cat_cs_intros
        )+

    note \<psi>r1r_is_arrD = cat_Funct_is_arrD[OF \<psi>r1r_is_arr, unfolded cat_cs_simps]

    from is_functor.universal_arrow_ofD(3)
      [
        OF \<FF>.tm_cf_cf_Cone_is_functor ua,
        unfolded cat_op_simps,
        OF u'.cat_cone_obj \<FF>.ntcf_paa_is_arr[OF 0 Cone_r' u'] 
      ]
    obtain f where f: "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      and Pf: "?P (?Cone\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>) (ntcf_arrow u') =
        umap_of ?Cone (set {0}) r (?P (?Cone\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>) ?\<psi>r1r) r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      and f_unique: "\<And>f'.
        \<lbrakk>
          f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r;
          ?P (?Cone\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>) (ntcf_arrow u') =
            umap_of ?Cone (set {0}) r (?P (?Cone\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>) ?\<psi>r1r) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
        \<rbrakk> \<Longrightarrow> f' = f"
      by metis

    show "\<exists>!f.
      f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and>
      u' = ntcf_of_ntcf_arrow \<JJ> \<CC> ?\<psi>r1r \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
    proof(intro ex1I conjI; (elim conjE)?)
      show "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by (rule f)
      from Pf Cone_r 0 f \<psi>r1r \<psi>r1r_is_arr \<psi>r1r_is_arrD(1) show
        "u' = ntcf_of_ntcf_arrow \<JJ> \<CC> ?\<psi>r1r \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
        by (subst (asm) \<psi>r1r_is_arrD(2))
          (
            cs_prems
              cs_simp: cat_FUNCT_cs_simps cat_small_cs_simps cat_cs_simps
              cs_intro:
                cat_small_cs_intros
                cat_cs_intros
                cat_FUNCT_cs_intros
                cat_prod_cs_intros
                cat_op_intros
          )

      fix f' assume prems: 
        "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
        "u' = ntcf_of_ntcf_arrow \<JJ> \<CC> ?\<psi>r1r \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
      from Pf Cone_r 0 f \<psi>r1r \<psi>r1r_is_arr \<psi>r1r_is_arrD(1) prems(1) have
        "?P (?Cone\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>) (ntcf_arrow u') =
          umap_of ?Cone (set {0}) r (?P (?Cone\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>) ?\<psi>r1r) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
        by (subst \<psi>r1r_is_arrD(2))
          (
            cs_concl
              cs_simp: cat_FUNCT_cs_simps cat_small_cs_simps cat_cs_simps prems(2)
              cs_intro:
                cat_small_cs_intros
                cat_FUNCT_cs_intros
                cat_cs_intros
                cat_prod_cs_intros
                cat_op_intros
          )
      from f_unique[OF prems(1) this] show "f' = f" .
    qed

  qed

qed

lemma cat_corepresentation_if_is_tm_cat_limit:
  \<comment>\<open>See Definition 3.1.5 in Section 3.1 in \cite{riehl_category_2016}.\<close>
  assumes "\<psi> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cat_corepresentation
    \<alpha> (tm_cf_Cone \<alpha> \<FF>) r (Yoneda_arrow \<alpha> (tm_cf_Cone \<alpha> \<FF>) r (ntcf_arrow \<psi>))"
    (is \<open>cat_corepresentation \<alpha> ?Cone r ?Y\<psi>\<close>)
proof-

  let ?Funct = \<open>cat_Funct \<alpha> \<JJ> \<CC>\<close>
    and ?P_\<psi> = \<open>ntcf_paa 0 (?Cone\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>) (ntcf_arrow \<psi>)\<close>
    and ?ntcf_of = \<open>ntcf_of_ntcf_arrow \<JJ> \<CC>\<close>

  interpret \<psi>: is_tm_cat_limit \<alpha> \<JJ> \<CC> \<FF> r \<psi> by (rule assms(1))
  interpret Funct: category \<alpha> ?Funct
    by
      (
        cs_concl cs_shallow cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  interpret Cone: is_functor \<alpha> \<open>op_cat \<CC>\<close> \<open>cat_Set \<alpha>\<close> \<open>?Cone\<close>
    by (rule \<psi>.NTCod.tm_cf_cf_Cone_is_functor)

  have 0: "0 \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" unfolding cat_Set_components by auto
  have ntcf_arrow_\<psi>: 
    "ntcf_arrow \<psi> : cf_map (cf_const \<JJ> \<CC> r) \<mapsto>\<^bsub>?Funct\<^esub> cf_map \<FF>"
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros)
  from \<psi>.cat_cone_obj 0 ntcf_arrow_\<psi> have P_\<psi>:
    "?P_\<psi> : set {0} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> ?Cone\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    by
      (
        cs_concl cs_shallow
          cs_intro: cat_cs_intros cat_op_intros 
          cs_simp: cat_small_cs_simps cat_FUNCT_cs_simps
      )

  have "universal_arrow_of ?Cone (set {0}) r ?P_\<psi>"
  proof(rule Cone.universal_arrow_ofI, unfold cat_op_simps, rule \<psi>.cat_cone_obj)

    from 0 \<psi>.cat_cone_obj show "?P_\<psi> : set {0} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> ?Cone\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
      by
        (
          cs_concl
            cs_intro:
              cat_small_cs_intros
              cat_cs_intros
              cat_FUNCT_cs_intros
              cat_op_intros
            cs_simp: cat_small_cs_simps
        )

    fix r' u' assume prems:
      "r' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "u' : set {0} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> ?Cone\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"

    let ?const_r' = \<open>cf_map (cf_const \<JJ> \<CC> r')\<close>
    let ?Hom_r\<FF> = \<open>Hom ?Funct ?const_r' (cf_map \<FF>)\<close>

    from prems(2,1) have u': "u' : set {0} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> ?Hom_r\<FF>"
      by
        (
          cs_prems cs_shallow
            cs_simp: cat_small_cs_simps cat_cs_simps cs_intro: cat_cs_intros
        )
    from prems(1) have [cat_FUNCT_cs_simps]:
      "cf_of_cf_map \<JJ> \<CC> ?const_r' = cf_const \<JJ> \<CC> r'"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps cs_intro: cat_cs_intros
        )

    from
      cat_Set_ArrVal_app_vrange[OF prems(2) vintersection_vsingleton] 
      prems(1)
    have "u'\<lparr>ArrVal\<rparr>\<lparr>0\<rparr> : ?const_r' \<mapsto>\<^bsub>?Funct\<^esub> cf_map \<FF>"
      by (cs_prems cs_shallow cs_simp: cat_small_cs_simps cat_cs_simps)
    note u'0 = cat_Funct_is_arrD[OF this, unfolded cat_FUNCT_cs_simps]

    interpret u'0: is_tm_cat_cone \<alpha> r' \<JJ> \<CC> \<FF> \<open>?ntcf_of (u'\<lparr>ArrVal\<rparr>\<lparr>0\<rparr>)\<close>
      by
        (
          rule is_tm_cat_coneI[
            OF is_tm_ntcfD(1)[OF u'0(1)] \<psi>.NTCod.is_tm_functor_axioms prems(1)
            ]
        )

    from \<psi>.tm_cat_lim_ua_fo[OF u'0.is_cat_cone_axioms] obtain f 
      where f: "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
        and u'0_def: "?ntcf_of (u'\<lparr>ArrVal\<rparr>\<lparr>0\<rparr>) = \<psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
        and f_unique: "\<And>f'.
          \<lbrakk>
            f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r;
            ?ntcf_of (u'\<lparr>ArrVal\<rparr>\<lparr>0\<rparr>) = \<psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'
          \<rbrakk> \<Longrightarrow> f' = f"
      by metis

    note [cat_FUNCT_cs_simps] = 
      \<psi>.ntcf_paa_ArrVal u'0(2)[symmetric] u'0_def[symmetric]

    show "\<exists>!f'.
      f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = umap_of ?Cone (set {0}) r ?P_\<psi> r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    proof(intro ex1I conjI; (elim conjE)?; (rule f)?)

      from f 0 u' ntcf_arrow_\<psi> show 
        "u' = umap_of ?Cone (set {0}) r ?P_\<psi> r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
        by (*slow*)
          (
            cs_concl
              cs_simp: cat_cs_simps
              cs_intro:
                cat_small_cs_intros
                cat_FUNCT_cs_intros
                cat_prod_cs_intros
                cat_cs_intros
                cat_op_intros
              cs_simp: cat_FUNCT_cs_simps cat_small_cs_simps
          )

      fix f' assume prems':
        "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
        "u' = umap_of ?Cone (set {0}) r ?P_\<psi> r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"

      let ?f' = \<open>ntcf_const \<JJ> \<CC> f'\<close>

      from prems'(2,1) 0 ntcf_arrow_\<psi> P_\<psi> have 
        "u' = ntcf_paa 0 ?Hom_r\<FF> (ntcf_arrow (\<psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?f'))"
        unfolding 
          Cone.umap_of_ArrVal_app[unfolded cat_op_simps, OF prems'(1) P_\<psi>]
        by (*very slow*)
          (
            cs_prems
              cs_simp: cat_FUNCT_cs_simps cat_small_cs_simps cat_cs_simps
              cs_intro:
                cat_small_cs_intros
                cat_FUNCT_cs_intros
                cat_prod_cs_intros
                cat_cs_intros
                cat_op_intros
          )
      then have
        "?ntcf_of (u'\<lparr>ArrVal\<rparr>\<lparr>0\<rparr>) =
          ?ntcf_of ((ntcf_paa 0 ?Hom_r\<FF> (ntcf_arrow (\<psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?f')))\<lparr>ArrVal\<rparr>\<lparr>0\<rparr>)"
        by simp
      from this prems'(1) have "?ntcf_of (u'\<lparr>ArrVal\<rparr>\<lparr>0\<rparr>) = \<psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?f'"
        by
          (
            cs_prems cs_shallow
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps cs_intro: cat_cs_intros
          )
      from f_unique[OF prems'(1) this] show "f' = f" . 

    qed

  qed

  from 
    cat_corepresentation_if_universal_arrow_of[
      OF \<psi>.NTDom.HomCod.category_axioms Cone.is_functor_axioms 0 this
      ]
  show "cat_corepresentation \<alpha> ?Cone r ?Y\<psi>"
    by (cs_prems cs_shallow cs_simp: cat_cs_simps)

qed

text\<open>\newpage\<close>

end