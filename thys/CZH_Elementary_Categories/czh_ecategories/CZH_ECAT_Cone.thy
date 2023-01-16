(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Cones and cocones\<close>
theory CZH_ECAT_Cone
  imports 
    CZH_ECAT_NTCF
    CZH_ECAT_Hom
    CZH_ECAT_FUNCT
begin



subsection\<open>Cone and cocone\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
In the context of this work, the concept of a cone corresponds to that of a cone
to the base of a functor from a vertex, as defined in Chapter III-4 in
\<^cite>\<open>"mac_lane_categories_2010"\<close>; the concept of a cocone corresponds to that
of a cone from the base of a functor to a vertex, as defined in Chapter III-3
in \<^cite>\<open>"mac_lane_categories_2010"\<close>.
\<close>

locale is_cat_cone = is_ntcf \<alpha> \<JJ> \<CC> \<open>cf_const \<JJ> \<CC> c\<close> \<FF> \<NN> for \<alpha> c \<JJ> \<CC> \<FF> \<NN> +
  assumes cat_cone_obj[cat_cs_intros]: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"

syntax "_is_cat_cone" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_cone \<alpha> c \<JJ> \<CC> \<FF> \<NN>"

locale is_cat_cocone = is_ntcf \<alpha> \<JJ> \<CC> \<FF> \<open>cf_const \<JJ> \<CC> c\<close> \<NN> for \<alpha> c \<JJ> \<CC> \<FF> \<NN> +
  assumes cat_cocone_obj[cat_cs_intros]: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"

syntax "_is_cat_cocone" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_cocone \<alpha> c \<JJ> \<CC> \<FF> \<NN>"


text\<open>Rules.\<close>

lemma (in is_cat_cone) is_cat_cone_axioms'[cat_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "c' = c" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "\<NN> : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_cone_axioms)

mk_ide rf is_cat_cone_def[unfolded is_cat_cone_axioms_def]
  |intro is_cat_coneI|
  |dest is_cat_coneD[dest!]|
  |elim is_cat_coneE[elim!]|

lemma (in is_cat_cone) is_cat_coneD'[cat_cs_intros]:
  assumes "c' = cf_const \<JJ> \<CC> c"
  shows "\<NN> : c' \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  unfolding assms by (cs_concl cs_shallow cs_intro: cat_cs_intros)

lemma (in is_cat_cocone) is_cat_cocone_axioms'[cat_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "c' = c" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "\<NN> : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_cocone_axioms)

mk_ide rf is_cat_cocone_def[unfolded is_cat_cocone_axioms_def]
  |intro is_cat_coconeI|
  |dest is_cat_coconeD[dest!]|
  |elim is_cat_coconeE[elim!]|

lemma (in is_cat_cocone) is_cat_coconeD'[cat_cs_intros]:
  assumes "c' = cf_const \<JJ> \<CC> c"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  unfolding assms by (cs_concl cs_shallow cs_intro: cat_cs_intros)


text\<open>Duality.\<close>

lemma (in is_cat_cone) is_cat_cocone_op:
  "op_ntcf \<NN> : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_coconeI)
    (
      cs_concl cs_shallow 
        cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros
    )+

lemma (in is_cat_cone) is_cat_cocone_op'[cat_op_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>" and "\<FF>' = op_cf \<FF>"
  shows "op_ntcf \<NN> : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_cocone_op)

lemmas [cat_op_intros] = is_cat_cone.is_cat_cocone_op'

lemma (in is_cat_cocone) is_cat_cone_op:
  "op_ntcf \<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_coneI)
    (
      cs_concl cs_shallow 
        cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros
    )

lemma (in is_cat_cocone) is_cat_cone_op'[cat_op_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>" and "\<FF>' = op_cf \<FF>"
  shows "op_ntcf \<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_cone_op)

lemmas [cat_op_intros] = is_cat_cocone.is_cat_cone_op'


text\<open>Elementary properties.\<close>

lemma (in is_cat_cone) cat_cone_LArr_app_is_arr: 
  assumes "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
proof-
  from assms have [simp]: "cf_const \<JJ> \<CC> c\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = c"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)
  from ntcf_NTMap_is_arr[OF assms] show ?thesis by simp 
qed

lemma (in is_cat_cone) cat_cone_LArr_app_is_arr'[cat_cs_intros]: 
  assumes "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" and "\<FF>j = \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>j"
  using assms(1) unfolding assms(2) by (rule cat_cone_LArr_app_is_arr)

lemmas [cat_cs_intros] = is_cat_cone.cat_cone_LArr_app_is_arr'

lemma (in is_cat_cocone) cat_cocone_LArr_app_is_arr: 
  assumes "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> c"
proof-
  from assms have [simp]: "cf_const \<JJ> \<CC> c\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = c"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)
  from ntcf_NTMap_is_arr[OF assms] show ?thesis by simp 
qed

lemma (in is_cat_cocone) cat_cocone_LArr_app_is_arr'[cat_cs_intros]: 
  assumes "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" and "\<FF>j = \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : \<FF>j \<mapsto>\<^bsub>\<CC>\<^esub> c"
  using assms(1) unfolding assms(2) by (rule cat_cocone_LArr_app_is_arr)

lemmas [cat_cs_intros] = is_cat_cocone.cat_cocone_LArr_app_is_arr'

lemma (in is_cat_cone) cat_cone_Comp_commute[cat_cs_simps]:
  assumes "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b"
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
  using ntcf_Comp_commute[symmetric, OF assms] assms 
  by (cs_prems cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

thm (*not ca_cs_simps*) is_cat_cone.cat_cone_Comp_commute

lemma (in is_cat_cocone) cat_cocone_Comp_commute[cat_cs_simps]:
  assumes "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
  using ntcf_Comp_commute[OF assms] assms 
  by
    (
      cs_prems 
        cs_simp: cat_cs_simps dghm_const_ArrMap_app cs_intro: cat_cs_intros
    )

thm (*not ca_cs_simps*) is_cat_cocone.cat_cocone_Comp_commute


text\<open>Utilities/helper lemmas.\<close>

lemma (in is_cat_cone) helper_cat_cone_ntcf_vcomp_Comp:
  assumes "\<NN>' : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c" 
    and "\<NN>' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'" 
    and "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
  shows "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  from assms(3) have "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
    by simp
  from this assms(1,2,4) show "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
    by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma (in is_cat_cone) helper_cat_cone_Comp_ntcf_vcomp:
  assumes "\<NN>' : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c" 
    and "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'" 
  shows "\<NN>' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
proof-
  interpret \<NN>': is_cat_cone \<alpha> c' \<JJ> \<CC> \<FF> \<NN>' by (rule assms(1))
  show ?thesis
  proof(rule ntcf_eqI[OF \<NN>'.is_ntcf_axioms])
    from assms(2) show 
      "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f' : cf_const \<JJ> \<CC> c' \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "\<NN>'\<lparr>NTMap\<rparr> = (\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold cat_cs_simps)
      show "vsv ((\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>)"
        by (cs_concl cs_intro: cat_cs_intros)
      from assms show "\<JJ>\<lparr>Obj\<rparr> = \<D>\<^sub>\<circ> ((\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>)"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      fix j assume prems': "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
      with assms(1,2) show "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps assms(3) cs_intro: cat_cs_intros)
    qed auto
  qed simp_all
qed

lemma (in is_cat_cone) helper_cat_cone_Comp_ntcf_vcomp_iff:
  assumes "\<NN>' : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> \<NN>' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f' \<longleftrightarrow>
    f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
  using 
    helper_cat_cone_ntcf_vcomp_Comp[OF assms]
    helper_cat_cone_Comp_ntcf_vcomp[OF assms]
  by (intro iffI; elim conjE; intro conjI) metis+

lemma (in is_cat_cocone) helper_cat_cocone_ntcf_vcomp_Comp:
  assumes "\<NN>' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" 
    and "\<NN>' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>" 
    and "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
  shows "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
proof-
  interpret \<NN>': is_cat_cocone \<alpha> c' \<JJ> \<CC> \<FF> \<NN>' by (rule assms(1))
  from assms(3) have "op_ntcf \<NN>' = op_ntcf (ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)" by simp
  from this assms(2) have op_\<NN>':
    "op_ntcf \<NN>' = op_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f'"
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros)
  have "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f'"
    by 
      (
        rule is_cat_cone.helper_cat_cone_ntcf_vcomp_Comp[
          OF is_cat_cone_op \<NN>'.is_cat_cone_op, 
          unfolded cat_op_simps, 
          OF assms(2) op_\<NN>' assms(4)
          ]
      )
  from this assms(2,4) show "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
    by 
      (
        cs_prems cs_shallow 
          cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros
      )
qed

lemma (in is_cat_cocone) helper_cat_cocone_Comp_ntcf_vcomp:
  assumes "\<NN>' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" 
    and "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" 
  shows "\<NN>' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>"
proof-
  interpret \<NN>': is_cat_cocone \<alpha> c' \<JJ> \<CC> \<FF> \<NN>' by (rule assms(1))
  from assms(2) have \<NN>'j: "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f'"
    if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    using that
    unfolding assms(3)[OF that] 
    by 
      (
        cs_concl cs_shallow 
          cs_simp: cat_op_simps cat_cs_simps cs_intro: cat_cs_intros
      )
  have op_\<NN>': 
    "op_ntcf \<NN>' = op_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f'"
    by 
      (
        rule is_cat_cone.helper_cat_cone_Comp_ntcf_vcomp[
          OF is_cat_cone_op \<NN>'.is_cat_cone_op,
          unfolded cat_op_simps, 
          OF assms(2) \<NN>'j, 
          simplified
          ]
      )
  from assms(2) show "\<NN>' = (ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
    by 
      (
        cs_concl  
          cs_simp: 
            cat_op_simps op_\<NN>' eq_op_ntcf_iff[symmetric, OF \<NN>'.is_ntcf_axioms]
          cs_intro: cat_cs_intros
      )
qed

lemma (in is_cat_cocone) helper_cat_cocone_Comp_ntcf_vcomp_iff:
  assumes "\<NN>' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<and> \<NN>' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> \<longleftrightarrow>
    f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
  using 
    helper_cat_cocone_ntcf_vcomp_Comp[OF assms]
    helper_cat_cocone_Comp_ntcf_vcomp[OF assms]
  by (intro iffI; elim conjE; intro conjI) metis+


subsubsection\<open>Vertical composition of a natural transformation and a cone\<close>

lemma ntcf_vcomp_is_cat_cone[cat_cs_intros]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  by 
    (
      intro is_cat_coneI ntcf_vcomp_is_ntcf, rule assms(1); 
      rule is_cat_coneD[OF assms(2)]
    )


subsubsection\<open>
Composition of a functor and a cone, composition of a functor and a cocone
\<close>

lemma cf_ntcf_comp_cf_cat_cone: 
  assumes "\<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_cat_cone \<alpha> c \<AA> \<BB> \<FF> \<NN> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  show ?thesis
    by (intro is_cat_coneI)
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros )+
qed

lemma cf_ntcf_comp_cf_cat_cone'[cat_cs_intros]: 
  assumes "\<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "c' = \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    and "\<GG>\<FF> = \<GG> \<circ>\<^sub>C\<^sub>F \<FF>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG>\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule cf_ntcf_comp_cf_cat_cone)

lemma cf_ntcf_comp_cf_cat_cocone:
  assumes "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<GG> \<circ>\<^sub>C\<^sub>F \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_cat_cocone \<alpha> c \<AA> \<BB> \<FF> \<NN> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  show ?thesis
    by
      (
        rule is_cat_cone.is_cat_cocone_op
          [
            OF cf_ntcf_comp_cf_cat_cone[
              OF \<NN>.is_cat_cone_op \<GG>.is_functor_op, unfolded cat_op_simps
              ], 
            unfolded cat_op_simps
          ]
      )
qed

lemma cf_ntcf_comp_cf_cat_cocone'[cat_cs_intros]: 
  assumes "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "c' = \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    and "\<GG>\<FF> = \<GG> \<circ>\<^sub>C\<^sub>F \<FF>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<GG>\<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule cf_ntcf_comp_cf_cat_cocone)


subsubsection\<open>Cones, cocones and constant natural transformations\<close>

lemma ntcf_vcomp_ntcf_const_is_cat_cone:
  assumes "\<NN> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<BB> f : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_cat_cone \<alpha> b \<AA> \<BB> \<FF> \<NN> by (rule assms(1))
  from assms(2) show ?thesis
    by (intro is_cat_coneI) (cs_concl cs_intro: cat_cs_intros)
qed

lemma ntcf_vcomp_ntcf_const_is_cat_cone'[cat_cs_intros]:
  assumes "\<NN> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM> = ntcf_const \<AA> \<BB> f"
    and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1,3) unfolding assms(2) by (rule ntcf_vcomp_ntcf_const_is_cat_cone)

lemma ntcf_vcomp_ntcf_const_is_cat_cocone:
  assumes "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e a : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "ntcf_const \<AA> \<BB> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e b : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_cat_cocone \<alpha> a \<AA> \<BB> \<FF> \<NN> by (rule assms(1))
  from is_cat_cone.is_cat_cocone_op
    [
      OF ntcf_vcomp_ntcf_const_is_cat_cone[
        OF \<NN>.is_cat_cone_op, unfolded cat_op_simps, OF assms(2)
        ],
      unfolded cat_op_simps, 
      folded op_ntcf_ntcf_const
    ]
    assms(2)
  show ?thesis
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros)
qed

lemma ntcf_vcomp_ntcf_const_is_cat_cocone'[cat_cs_intros]:
  assumes "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e a : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM> = ntcf_const \<AA> \<BB> f"
    and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e b : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1,3) 
  unfolding assms(2)
  by (rule ntcf_vcomp_ntcf_const_is_cat_cocone)

lemma ntcf_vcomp_ntcf_const_CId: 
  assumes "\<NN> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<BB> (\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) = \<NN>"
proof-

  interpret \<NN>: is_cat_cone \<alpha> b \<AA> \<BB> \<FF> \<NN> by (rule assms) 

  show ?thesis
  proof(rule ntcf_eqI)

    from \<NN>.cat_cone_obj show lhs_is_ntcf: 
      "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<BB> (\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) :
        cf_const \<AA> \<BB> b \<mapsto>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    then have dom_lhs: 
      "\<D>\<^sub>\<circ> ((\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<BB> (\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (simp add: cat_cs_simps)

    from \<NN>.cat_cone_obj show "\<NN> : cf_const \<AA> \<BB> b \<mapsto>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    then have dom_rhs: "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (simp add: cat_cs_simps)

    show "(\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<BB> (\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>))\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      from prems \<NN>.cat_cone_obj show 
        "(\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<BB> (\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed (use lhs_is_ntcf in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+

  qed simp_all

qed

lemma ntcf_vcomp_ntcf_const_CId'[cat_cs_simps]: 
  assumes "\<NN> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB>' = \<BB>"
  shows "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<BB> (\<BB>'\<lparr>CId\<rparr>\<lparr>b\<rparr>) = \<NN>"
  using assms(1) unfolding assms(2) by (rule ntcf_vcomp_ntcf_const_CId)



subsection\<open>Cone and cocone functors\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter V-1 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition cf_Cone :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_Cone \<alpha> \<beta> \<FF> = 
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>)(-,cf_map \<FF>) \<circ>\<^sub>C\<^sub>F
    op_cf (\<Delta>\<^sub>C\<^sub>F \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>))"

definition cf_Cocone :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_Cocone \<alpha> \<beta> \<FF> =
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>)(cf_map \<FF>,-) \<circ>\<^sub>C\<^sub>F
    (\<Delta>\<^sub>C\<^sub>F \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>))"


text\<open>An alternative form of the definition.\<close>

context is_functor
begin

lemma cf_Cone_def': 
  "cf_Cone \<alpha> \<beta> \<FF> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<AA> \<BB>(-,cf_map \<FF>) \<circ>\<^sub>C\<^sub>F op_cf (\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>)"
  unfolding cf_Cone_def cat_cs_simps by simp

lemma cf_Cocone_def': 
  "cf_Cocone \<alpha> \<beta> \<FF> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<AA> \<BB>(cf_map \<FF>,-) \<circ>\<^sub>C\<^sub>F (\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>)"
  unfolding cf_Cocone_def cat_cs_simps by simp

end


subsubsection\<open>Object map\<close>

lemma (in is_functor) cf_Cone_ObjMap_vsv[cat_cs_intros]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "vsv (cf_Cone \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>)"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps 
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_intros] = is_functor.cf_Cone_ObjMap_vsv

lemma (in is_functor) cf_Cocone_ObjMap_vsv[cat_cs_intros]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "vsv (cf_Cocone \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>)"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cocone_def'
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_intros] = is_functor.cf_Cocone_ObjMap_vsv

lemma (in is_functor) cf_Cone_ObjMap_vdomain[cat_cs_simps]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (cf_Cone \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms show ?thesis
    unfolding cf_Cone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_Cone_ObjMap_vdomain

lemma (in is_functor) cf_Cocone_ObjMap_vdomain[cat_cs_simps]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (cf_Cocone \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms show ?thesis
    unfolding cf_Cocone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_Cocone_ObjMap_vdomain

lemma (in is_functor) cf_Cone_ObjMap_app[cat_cs_simps]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "cf_Cone \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> =
    Hom (cat_FUNCT \<alpha> \<AA> \<BB>) (cf_map (cf_const \<AA> \<BB> b)) (cf_map \<FF>)"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2,3) show ?thesis
    unfolding cf_Cone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_Cone_ObjMap_app

lemma (in is_functor) cf_Cocone_ObjMap_app[cat_cs_simps]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "cf_Cocone \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> =
    Hom (cat_FUNCT \<alpha> \<AA> \<BB>) (cf_map \<FF>) (cf_map (cf_const \<AA> \<BB> b))"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2,3) show ?thesis
    unfolding cf_Cocone_def'
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_Cocone_ObjMap_app


subsubsection\<open>Arrow map\<close>

lemma (in is_functor) cf_Cone_ArrMap_vsv[cat_cs_intros]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "vsv (cf_Cone \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>)"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cone_def
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps 
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_intros] = is_functor.cf_Cone_ArrMap_vsv

lemma (in is_functor) cf_Cocone_ArrMap_vsv[cat_cs_intros]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "vsv (cf_Cocone \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>)"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cocone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps 
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_intros] = is_functor.cf_Cocone_ArrMap_vsv

lemma (in is_functor) cf_Cone_ArrMap_vdomain[cat_cs_simps]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (cf_Cone \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_Cone_ArrMap_vdomain

lemma (in is_functor) cf_Cocone_ArrMap_vdomain[cat_cs_simps]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (cf_Cocone \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cocone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_Cocone_ArrMap_vdomain

lemma (in is_functor) cf_Cone_ArrMap_app[cat_cs_simps]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "cf_Cone \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = cf_hom
    (cat_FUNCT \<alpha> \<AA> \<BB>)
    [ntcf_arrow (ntcf_const \<AA> \<BB> f), cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>cf_map \<FF>\<rparr>]\<^sub>\<circ>"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2,3) show ?thesis
    unfolding cf_Cone_def
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps 
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_Cone_ArrMap_app

lemma (in is_functor) cf_Cocone_ArrMap_app[cat_cs_simps]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "cf_Cocone \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = cf_hom
    (cat_FUNCT \<alpha> \<AA> \<BB>)
    [cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>cf_map \<FF>\<rparr>, ntcf_arrow (ntcf_const \<AA> \<BB> f)]\<^sub>\<circ>"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  from assms(2,3) show ?thesis
    unfolding cf_Cocone_def'
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_FUNCT_components(1) cat_op_simps 
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_Cocone_ArrMap_app


subsubsection\<open>The cone functor is a functor\<close>

lemma (in is_functor) tm_cf_cf_Cone_is_functor_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cf_Cone \<alpha> \<beta> \<FF> : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-
  from assms interpret FUNCT: category \<beta> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  from assms interpret op_\<Delta>: 
    is_functor \<beta> \<open>op_cat \<BB>\<close> \<open>op_cat (cat_FUNCT \<alpha> \<AA> \<BB>)\<close> \<open>op_cf (\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>)\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  have "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<AA> \<BB>(-,cf_map \<FF>) :
    op_cat (cat_FUNCT \<alpha> \<AA> \<BB>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_FUNCT_cs_simps 
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros
      )
  then show "cf_Cone \<alpha> \<beta> \<FF> : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    unfolding cf_Cone_def' by (cs_concl cs_intro: cat_cs_intros)
qed

lemma (in is_functor) tm_cf_cf_Cocone_is_functor_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cf_Cocone \<alpha> \<beta> \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-
  from assms interpret Funct: category \<beta> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  from assms interpret op_\<Delta>: is_functor \<beta> \<BB> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)+
  have "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<AA> \<BB>(cf_map \<FF>,-) :
    cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_FUNCT_cs_simps 
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros
      )
  then show "cf_Cocone \<alpha> \<beta>  \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    unfolding cf_Cocone_def' by (cs_concl cs_intro: cat_cs_intros)
qed

text\<open>\newpage\<close>

end