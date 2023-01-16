(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Limits and colimits\<close>
theory CZH_UCAT_Limit
  imports 
    CZH_UCAT_Universal
    CZH_Elementary_Categories.CZH_ECAT_Cone
    CZH_Elementary_Categories.CZH_ECAT_Small_Cone
begin



subsection\<open>Background\<close>

named_theorems cat_lim_cs_simps
named_theorems cat_lim_cs_intros



subsection\<open>Limit and colimit\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The concept of a limit is introduced in Chapter III-4 in
\<^cite>\<open>"mac_lane_categories_2010"\<close>; the concept of a colimit is introduced in
Chapter III-3 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.
\<close>

locale is_cat_limit = is_cat_cone \<alpha> r \<JJ> \<CC> \<FF> u for \<alpha> \<JJ> \<CC> \<FF> r u + 
  assumes cat_lim_ua_fo: "\<And>u' r'. u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
    \<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"

syntax "_is_cat_limit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r u"

locale is_cat_colimit = is_cat_cocone \<alpha> r \<JJ> \<CC> \<FF> u for \<alpha> \<JJ> \<CC> \<FF> r u +
  assumes cat_colim_ua_of: "\<And>u' r'. u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
    \<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"

syntax "_is_cat_colimit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r u"


text\<open>Rules.\<close>

lemma (in is_cat_limit) is_cat_limit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_limit_axioms)

mk_ide rf is_cat_limit_def[unfolded is_cat_limit_axioms_def]
  |intro is_cat_limitI|
  |dest is_cat_limitD[dest]|
  |elim is_cat_limitE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_limitD(1)

lemma (in is_cat_colimit) is_cat_colimit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_colimit_axioms)

mk_ide rf is_cat_colimit_def[unfolded is_cat_colimit_axioms_def]
  |intro is_cat_colimitI|
  |dest is_cat_colimitD[dest]|
  |elim is_cat_colimitE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_colimitD(1)


text\<open>Limits, colimits and universal arrows.\<close>

lemma (in is_cat_limit) cat_lim_is_universal_arrow_fo:
  "universal_arrow_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u)"
proof(intro is_functor.universal_arrow_foI)

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<beta>_def \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show "\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<JJ> \<CC>"
    by 
      (
        intro 
          \<beta> \<alpha>\<beta>
          cf_diagonal_is_functor 
          NTDom.HomDom.category_axioms 
          NTDom.HomCod.category_axioms
      )

  show "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (intro cat_cone_obj)
  then show "ntcf_arrow u : \<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
    by 
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_FUNCT_cs_intros
      )

  fix r' u' assume prems: 
    "r' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "u' : \<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
  from prems(1) have [cat_cs_simps]: 
    "cf_of_cf_map \<JJ> \<CC> (cf_map \<FF>) = \<FF>"
    "cf_of_cf_map \<JJ> \<CC> (cf_map (cf_const \<JJ> \<CC> r')) = cf_const \<JJ> \<CC> r'"
    by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)+
  from prems(2,1) have
    "u' : cf_map (cf_const \<JJ> \<CC> r') \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
    by (cs_prems cs_shallow cs_simp: cat_cs_simps)
  note u'[unfolded cat_cs_simps] = cat_FUNCT_is_arrD[OF this]

  from cat_lim_ua_fo[OF is_cat_coneI[OF u'(1) prems(1)]] obtain f 
    where f: "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      and [symmetric, cat_cs_simps]: 
        "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
      and f_unique: 
        "\<lbrakk>
          f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r;
          ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'
         \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis

  show "\<exists>!f'.
    f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and>
    u' = umap_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
  proof(intro ex1I conjI; (elim conjE)?)
    show "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by (rule f)
    with \<alpha>\<beta> cat_cone_obj show u'_def: 
      "u' = umap_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      by 
        (
          cs_concl
            cs_simp: u'(2)[symmetric] cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    fix f' assume prems': 
      "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      "u' = umap_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    from prems'(2) \<alpha>\<beta> f prems' cat_cone_obj have u'_def':
      "u' = ntcf_arrow (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    from prems'(1) have "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
      by 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps u'_def' cs_intro: cat_cs_intros
        )
    from f_unique[OF prems'(1) this] show "f' = f" .

  qed

qed

lemma (in is_cat_cone) cat_cone_is_cat_limit:
  assumes "universal_arrow_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>)"
  shows "\<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<beta>_def \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(intro is_cat_limitI is_cat_cone_axioms)
    fix u' c' assume prems: "u' : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"

    interpret u': is_cat_cone \<alpha> c' \<JJ> \<CC> \<FF> u' by (rule prems)

    from u'.cat_cone_obj have u'_is_arr:
      "ntcf_arrow u' : \<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
      by 
        (
          cs_concl cs_shallow
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    
    from is_functor.universal_arrow_foD(3)
      [
        OF
          cf_diagonal_is_functor[
            OF \<beta> \<alpha>\<beta> NTDom.HomDom.category_axioms NTDom.HomCod.category_axioms
            ]
          assms
          u'.cat_cone_obj
          u'_is_arr
      ]
    obtain f where f: "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> c"
      and u'_def': "ntcf_arrow u' =
        umap_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      and f'_unique:
        "\<lbrakk>
          f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c;
          ntcf_arrow u' =
            umap_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
         \<rbrakk> \<Longrightarrow> f' = f"
      for f'
      by metis

    from u'_def' \<alpha>\<beta> f cat_cone_obj have u'_def: 
      "u' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    
    show "\<exists>!f'. f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> u' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
    proof(intro ex1I conjI; (elim conjE)?, (rule f)?, (rule u'_def)?)
      fix f'' assume prems': 
        "f'' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c" "u' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f''"
      from \<alpha>\<beta> prems' have 
        "ntcf_arrow u' = 
          umap_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>"
        by
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
      from f'_unique[OF prems'(1) this] show "f'' = f".
    qed

  qed
  
qed

lemma (in is_cat_colimit) cat_colim_is_universal_arrow_of:
  "universal_arrow_of (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u)"
proof(intro is_functor.universal_arrow_ofI)

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<beta>_def \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show "\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<JJ> \<CC>"
    by 
      (
        intro 
          \<beta> \<alpha>\<beta>
          cf_diagonal_is_functor 
          NTDom.HomDom.category_axioms 
          NTDom.HomCod.category_axioms
      )

  show "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (intro cat_cocone_obj)

  then show "ntcf_arrow u : cf_map \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<JJ> \<CC>\<^esub> \<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    by 
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_FUNCT_cs_intros
      )

  fix r' u' assume prems: 
    "r' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "u' : cf_map \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<JJ> \<CC>\<^esub> \<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"
  from prems(1) have [cat_cs_simps]: 
    "cf_of_cf_map \<JJ> \<CC> (cf_map \<FF>) = \<FF>"
    "cf_of_cf_map \<JJ> \<CC> (cf_map (cf_const \<JJ> \<CC> r')) = cf_const \<JJ> \<CC> r'"
    by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)+
  from prems(2,1) have
    "u' : cf_map \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<JJ> \<CC>\<^esub> cf_map (cf_const \<JJ> \<CC> r')"
    by (cs_prems cs_shallow cs_simp: cat_cs_simps)
  note u'[unfolded cat_cs_simps] = cat_FUNCT_is_arrD[OF this]

  from cat_colim_ua_of[OF is_cat_coconeI[OF u'(1) prems(1)]] obtain f 
    where f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'"
      and [symmetric, cat_cs_simps]: 
        "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      and f_unique: 
        "\<lbrakk>
          f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r';
          ntcf_of_ntcf_arrow \<JJ> \<CC> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u
         \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis

  show " \<exists>!f'. 
    f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> 
    u' = umap_of (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
  proof(intro ex1I conjI; (elim conjE)?)
  
    show "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" by (rule f)
    with \<alpha>\<beta> cat_cocone_obj show u'_def: 
      "u' = umap_of (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      by 
        (
          cs_concl
            cs_simp: u'(2)[symmetric] cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  
    fix f' assume prems':
      "f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'"
      "u' = umap_of (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    from prems'(2) \<alpha>\<beta> f prems' cat_cocone_obj have u'_def':
      "u' = ntcf_arrow (ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u)"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    from prems'(1) have "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      by 
        (
          cs_concl cs_shallow 
            cs_simp: cat_FUNCT_cs_simps u'_def' cs_intro: cat_cs_intros
        )
    from f_unique[OF prems'(1) this] show "f' = f" .

  qed

qed

lemma (in is_cat_cocone) cat_cocone_is_cat_colimit:
  assumes "universal_arrow_of (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>)"
  shows "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<beta>_def \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(intro is_cat_colimitI is_cat_cocone_axioms)
  
    fix u' c' assume prems: "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"

    interpret u': is_cat_cocone \<alpha> c' \<JJ> \<CC> \<FF> u' by (rule prems)

    from u'.cat_cocone_obj have u'_is_arr:
      "ntcf_arrow u' : cf_map \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<JJ> \<CC>\<^esub> \<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr>"
      by
        (
          cs_concl cs_shallow 
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )

    from is_functor.universal_arrow_ofD(3)
      [
        OF
          cf_diagonal_is_functor[
            OF \<beta> \<alpha>\<beta> NTDom.HomDom.category_axioms NTDom.HomCod.category_axioms
            ]
          assms
          u'.cat_cocone_obj
          u'_is_arr
      ]
    obtain f where f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> c'"
      and u'_def': "ntcf_arrow u' =
        umap_of (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      and f'_unique:
        "\<lbrakk>
          f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c';
          ntcf_arrow u' =
            umap_of (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
         \<rbrakk> \<Longrightarrow> f' = f"
      for f'
      by metis

    from u'_def' \<alpha>\<beta> f cat_cocone_obj have u'_def: 
      "u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    
    show "\<exists>!f'. f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>"
    proof(intro ex1I conjI; (elim conjE)?, (rule f)?, (rule u'_def)?)
      fix f'' assume prems': 
        "f'' : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" "u' = ntcf_const \<JJ> \<CC> f'' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>"
      from \<alpha>\<beta> prems' have 
        "ntcf_arrow u' = 
          umap_of (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>"
        by
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
      from f'_unique[OF prems'(1) this] show "f'' = f".
    qed

  qed
  
qed


text\<open>Duality.\<close>

lemma (in is_cat_limit) is_cat_colimit_op:
  "op_ntcf u : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
proof(intro is_cat_colimitI)
  show "op_ntcf u : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by (cs_concl cs_shallow cs_simp: cs_intro: cat_op_intros)
  fix u' r' assume prems: 
    "u' : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  interpret u': is_cat_cocone \<alpha> r' \<open>op_cat \<JJ>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<FF>\<close> u' 
    by (rule prems)
  from cat_lim_ua_fo[OF u'.is_cat_cone_op[unfolded cat_op_simps]] obtain f 
    where f: "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      and op_u'_def: "op_ntcf u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
      and f_unique: 
        "\<lbrakk> f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r; op_ntcf u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f' \<rbrakk> \<Longrightarrow>
          f' = f"
    for f'
    by metis
  from op_u'_def have "op_ntcf (op_ntcf u') = op_ntcf (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f)"
    by simp
  from this f have u'_def: 
    "u' = ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf u"
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros)
  show "\<exists>!f'. 
    f' : r \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r' \<and> 
    u' = ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf u"
  proof(intro ex1I conjI; (elim conjE)?, (unfold cat_op_simps)?)
    fix f' assume prems': 
      "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      "u' = ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf u"
    from prems'(2) have 
      "op_ntcf u' = op_ntcf (ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf u)"
      by simp
    from this prems'(1) have "op_ntcf u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
      by 
        (
          cs_prems
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros
        )
    from f_unique[OF prems'(1) this] show "f' = f". 
  qed (intro u'_def f)+
qed

lemma (in is_cat_limit) is_cat_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_colimit_op)

lemmas [cat_op_intros] = is_cat_limit.is_cat_colimit_op'

lemma (in is_cat_colimit) is_cat_limit_op:
  "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
proof(intro is_cat_limitI)
  show "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by (cs_concl cs_shallow cs_simp: cs_intro: cat_op_intros)
  fix u' r' assume prems: 
    "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  interpret u': is_cat_cone \<alpha> r' \<open>op_cat \<JJ>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<FF>\<close> u' 
    by (rule prems)
  from cat_colim_ua_of[OF u'.is_cat_cocone_op[unfolded cat_op_simps]] obtain f 
    where f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'"
      and op_u'_def: "op_ntcf u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      and f_unique: 
        "\<lbrakk> f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'; op_ntcf u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u \<rbrakk> \<Longrightarrow>
          f' = f"
    for f'
    by metis
  from op_u'_def have "op_ntcf (op_ntcf u') = op_ntcf (ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u)"
    by simp
  from this f have u'_def: 
    "u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f"
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros)
  show "\<exists>!f'. 
    f' : r' \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r \<and> 
    u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f'"
  proof(intro ex1I conjI; (elim conjE)?, (unfold cat_op_simps)?)
    fix f' assume prems': 
      "f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'"
      "u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f'"
    from prems'(2) have 
      "op_ntcf u' = op_ntcf (op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f')"
      by simp
    from this prems'(1) have "op_ntcf u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros
        )
    from f_unique[OF prems'(1) this] show "f' = f". 
  qed (intro u'_def f)+
qed

lemma (in is_cat_colimit) is_cat_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_limit_op)

lemmas [cat_op_intros] = is_cat_colimit.is_cat_colimit_op'


subsubsection\<open>Universal property\<close>

lemma (in is_cat_limit) cat_lim_unique_cone':
  assumes "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
  by (fold helper_cat_cone_Comp_ntcf_vcomp_iff[OF assms(1)])
    (intro cat_lim_ua_fo assms)

lemma (in is_cat_limit) cat_lim_unique:
  assumes "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
  by (intro cat_lim_ua_fo[OF is_cat_limitD(1)[OF assms]])

lemma (in is_cat_limit) cat_lim_unique':
  assumes "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
  by (intro cat_lim_unique_cone'[OF is_cat_limitD(1)[OF assms]])

lemma (in is_cat_colimit) cat_colim_unique_cocone:
  assumes "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
proof-
  interpret u': is_cat_cocone \<alpha> r' \<JJ> \<CC> \<FF> u' by (rule assms(1))
  from u'.cat_cocone_obj have op_r': "r' \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
    unfolding cat_op_simps by simp
  from 
    is_cat_limit.cat_lim_ua_fo[
      OF is_cat_limit_op u'.is_cat_cone_op, folded op_ntcf_ntcf_const
      ]
  obtain f' where f': "f' : r' \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r"
    and [cat_cs_simps]: 
      "op_ntcf u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (ntcf_const \<JJ> \<CC> f')"
    and unique: 
      "\<lbrakk>
        f'' : r' \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r;
        op_ntcf u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (ntcf_const \<JJ> \<CC> f'')
       \<rbrakk> \<Longrightarrow> f'' = f'" 
    for f''
    by metis
  show ?thesis
  proof(intro ex1I conjI; (elim conjE)?)
    from f' show f': "f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" unfolding cat_op_simps by simp
    show "u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      by (rule eq_op_ntcf_iff[THEN iffD1], insert f')
        (cs_concl cs_intro: cat_cs_intros cs_simp: cat_cs_simps cat_op_simps)+
    fix f'' assume prems: "f'' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" "u' = ntcf_const \<JJ> \<CC> f'' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
    from prems(1) have "f'' : r' \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r" unfolding cat_op_simps by simp
    moreover from prems(1) have 
      "op_ntcf u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (ntcf_const \<JJ> \<CC> f'')"
      unfolding prems(2)
      by (cs_concl cs_intro: cat_cs_intros cs_simp: cat_cs_simps cat_op_simps)
    ultimately show "f'' = f'" by (rule unique)
  qed
qed

lemma (in is_cat_colimit) cat_colim_unique_cocone':
  assumes "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
  by (fold helper_cat_cocone_Comp_ntcf_vcomp_iff[OF assms(1)])
    (intro cat_colim_unique_cocone assms)

lemma (in is_cat_colimit) cat_colim_unique:
  assumes "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
  by (intro cat_colim_unique_cocone[OF is_cat_colimitD(1)[OF assms]])

lemma (in is_cat_colimit) cat_colim_unique':
  assumes "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
proof-
  interpret u': is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(1))
  show ?thesis
    by (fold helper_cat_cocone_Comp_ntcf_vcomp_iff[OF u'.is_cat_cocone_axioms])
      (intro cat_colim_unique assms)
qed

lemma cat_lim_ex_is_iso_arr:
  assumes "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r" and "u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
proof-
  interpret u: is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r u by (rule assms(1))
  interpret u': is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(2))
  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<beta>_def u.\<Z>_Limit_\<alpha>\<omega> u.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def u.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 
  have \<Delta>: "\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<JJ> \<CC>"
    by 
      (
        intro 
          \<beta> \<alpha>\<beta>
          cf_diagonal_is_functor 
          u.NTDom.HomDom.category_axioms 
          u.NTDom.HomCod.category_axioms
      )
  then interpret \<Delta>: is_functor \<beta> \<CC> \<open>cat_FUNCT \<alpha> \<JJ> \<CC>\<close> \<open>\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>\<close> by simp
  from is_functor.cf_universal_arrow_fo_ex_is_iso_arr[
    OF \<Delta> u.cat_lim_is_universal_arrow_fo u'.cat_lim_is_universal_arrow_fo
    ]
  obtain f where f: "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r"
    and u': "ntcf_arrow u' =
    umap_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
    by auto
  from f have "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by auto
  from u' this have "u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
    by
      (
        cs_prems  
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros
      )
  with f that show ?thesis by simp
qed

lemma cat_lim_ex_is_iso_arr':
  assumes "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r" 
    and "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  interpret u: is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r u by (rule assms(1))
  interpret u': is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(2))
  from assms obtain f 
    where iso_f: "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r" and u'_def: "u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
    by (rule cat_lim_ex_is_iso_arr)
  then have f: "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by auto
  then have "u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    by 
      (
        intro u.helper_cat_cone_ntcf_vcomp_Comp[
          OF u'.is_cat_cone_axioms f u'_def that
          ]
      )
  with iso_f that show ?thesis by simp
qed

lemma cat_colim_ex_is_iso_arr:
  assumes "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'" and "u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
proof-
  interpret u: is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r u by (rule assms(1))
  interpret u': is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(2))
  obtain f where f: "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>op_cat \<CC>\<^esub> r"
    and [cat_cs_simps]: 
      "op_ntcf u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f"
    by 
      (
        elim cat_lim_ex_is_iso_arr[
          OF u.is_cat_limit_op u'.is_cat_limit_op
          ]
      )
  from f have iso_f: "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'" unfolding cat_op_simps by simp
  then have f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" by auto
  have "u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
    by (rule eq_op_ntcf_iff[THEN iffD1], insert f)
      (cs_concl cs_intro: cat_cs_intros cs_simp: cat_cs_simps cat_op_simps)+
  from iso_f this that show ?thesis by simp
qed

lemma cat_colim_ex_is_iso_arr':
  assumes "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'"
    and "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
proof-
  interpret u: is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r u by (rule assms(1))
  interpret u': is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(2))
  from assms obtain f 
    where iso_f: "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'" and u'_def: "u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
    by (rule cat_colim_ex_is_iso_arr)
  then have f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" by auto
  then have "u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    by 
      (
        intro u.helper_cat_cocone_ntcf_vcomp_Comp[
          OF u'.is_cat_cocone_axioms f u'_def that
          ]
      )
  with iso_f that show ?thesis by simp
qed


subsubsection\<open>Further properties\<close>

lemma (in is_cat_limit) cat_lim_is_cat_limit_if_is_iso_arr:
  assumes "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r"
  shows "u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  note f = is_iso_arrD(1)[OF assms(1)]
  from f(1) interpret u': is_cat_cone \<alpha> r' \<JJ> \<CC> \<FF> \<open>u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f\<close> 
    by (cs_concl cs_intro: cat_lim_cs_intros cat_cs_intros)
  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<beta>_def \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 
  show ?thesis
  proof
    (
      intro u'.cat_cone_is_cat_limit, 
      rule is_functor.universal_arrow_fo_if_universal_arrow_fo,
      rule cf_diagonal_is_functor[OF \<beta> \<alpha>\<beta>],
      rule NTDom.HomDom.category_axioms,
      rule NTDom.HomCod.category_axioms,
      rule cat_lim_is_universal_arrow_fo
    )
    show "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r" by (rule assms(1))
    from \<alpha>\<beta> f show
      "ntcf_arrow (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f) =
        umap_fo (\<Delta>\<^sub>C\<^sub>F \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  qed
qed

lemma (in is_cat_colimit) cat_colim_is_cat_colimit_if_is_iso_arr:
  assumes "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'" 
  shows "ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  note f = is_iso_arrD[OF assms(1)]
  from f(1) interpret u': is_cat_cocone \<alpha> r' \<JJ> \<CC> \<FF> \<open>ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u\<close> 
    by (cs_concl cs_intro: cat_lim_cs_intros cat_cs_intros)
  from f have [symmetric, cat_op_simps]:
    "op_ntcf (ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u) =
      op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f"
    by
      (
        cs_concl cs_shallow 
          cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros
      )
  show ?thesis
    by 
      (
        rule is_cat_limit.is_cat_colimit_op
          [
            OF is_cat_limit.cat_lim_is_cat_limit_if_is_iso_arr[
              OF is_cat_limit_op, unfolded cat_op_simps, OF assms(1)
              ],
            unfolded cat_op_simps
          ]
      )
qed

lemma ntcf_cf_comp_is_cat_limit_if_is_iso_functor:
  assumes "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_cat_limitI)
  interpret u: is_cat_limit \<alpha> \<BB> \<CC> \<FF> r u by (rule assms(1)) 
  interpret \<GG>: is_iso_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(2))
  note [cf_cs_simps] = is_iso_functor_is_iso_arr(2,3)
  show u\<GG>: "u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (intro is_cat_coneI)
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  fix u' r' assume prems: "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  then interpret u': is_cat_cone \<alpha> r' \<AA> \<CC> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG>\<close> u' by simp
  have "u' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F inv_cf \<GG> : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (intro is_cat_coneI)
      (
        cs_concl
          cs_simp: cat_cs_simps cf_cs_simps
          cs_intro: cat_cs_intros cf_cs_intros
      )
  from is_cat_limit.cat_lim_ua_fo[OF assms(1) this] obtain f 
    where f: "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      and u'_\<GG>: "u' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F inv_cf \<GG> = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<BB> \<CC> f"
      and f'f:
        "\<lbrakk>
          f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r; 
          u' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F inv_cf \<GG> = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<BB> \<CC> f' 
         \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis
  from u'_\<GG> have u'_inv\<GG>_\<GG>:
    "(u' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F inv_cf \<GG>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> = (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<BB> \<CC> f) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>"
    by simp
  show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<CC> f'"
  proof(intro ex1I conjI; (elim conjE)?)
    show "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by (rule f)
    from u'_inv\<GG>_\<GG> f show "u' = u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<CC> f"
      by
        (
          cs_prems 
            cs_simp:
              cf_cs_simps cat_cs_simps
              ntcf_cf_comp_ntcf_cf_comp_assoc 
              ntcf_vcomp_ntcf_cf_comp[symmetric]
            cs_intro: cat_cs_intros cf_cs_intros
        )
    fix f' assume prems:
      "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" "u' = u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<CC> f'"
    from prems(2) have 
      "u' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F inv_cf \<GG> = 
        (u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<CC> f') \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F inv_cf \<GG>"
      by simp
    from this f prems(1) have "u' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F inv_cf \<GG> = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<BB> \<CC> f'"
      by
        (
          cs_prems 
            cs_simp:
              cat_cs_simps cf_cs_simps
              ntcf_vcomp_ntcf_cf_comp[symmetric]
              ntcf_cf_comp_ntcf_cf_comp_assoc
            cs_intro: cf_cs_intros cat_cs_intros
        )
    then show "f' = f" by (intro f'f prems(1))
  qed
qed

lemma ntcf_cf_comp_is_cat_limit_if_is_iso_functor'[cat_lim_cs_intros]:
  assumes "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<AA>' = \<FF> \<circ>\<^sub>C\<^sub>F \<GG>"
  shows "u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<AA>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) 
  unfolding assms(3)
  by (rule ntcf_cf_comp_is_cat_limit_if_is_iso_functor)



subsection\<open>Small limit and small colimit\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The concept of a limit is introduced in Chapter III-4 in
\<^cite>\<open>"mac_lane_categories_2010"\<close>; the concept of a colimit is introduced in
Chapter III-3 in \<^cite>\<open>"mac_lane_categories_2010"\<close>. The definitions of small
limits were tailored for ZFC in HOL.
\<close>

locale is_tm_cat_limit = is_tm_cat_cone \<alpha> r \<JJ> \<CC> \<FF> u for \<alpha> \<JJ> \<CC> \<FF> r u + 
  assumes tm_cat_lim_ua_fo: 
    "\<And>u' r'. u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"

syntax "_is_tm_cat_limit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_tm_cat_limit \<alpha> \<JJ> \<CC> \<FF> r u"

locale is_tm_cat_colimit = is_tm_cat_cocone \<alpha> r \<JJ> \<CC> \<FF> u for \<alpha> \<JJ> \<CC> \<FF> r u +
  assumes tm_cat_colim_ua_of: 
    "\<And>u' r'. u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"

syntax "_is_tm_cat_colimit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_tm_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r u"


text\<open>Rules.\<close>

lemma (in is_tm_cat_limit) is_tm_cat_limit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_limit_axioms)

mk_ide rf is_tm_cat_limit_def[unfolded is_tm_cat_limit_axioms_def]
  |intro is_tm_cat_limitI|
  |dest is_tm_cat_limitD[dest]|
  |elim is_tm_cat_limitE[elim]|

lemmas [cat_lim_cs_intros] = is_tm_cat_limitD(1)

lemma (in is_tm_cat_colimit) is_tm_cat_colimit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_colimit_axioms)

mk_ide rf is_tm_cat_colimit_def[unfolded is_tm_cat_colimit_axioms_def]
  |intro is_tm_cat_colimitI|
  |dest is_tm_cat_colimitD[dest]|
  |elim is_tm_cat_colimitE[elim]|

lemmas [cat_lim_cs_intros] = is_tm_cat_colimitD(1)

lemma is_tm_cat_limitI':
  assumes "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>u' r'. u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
  shows "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof(rule is_tm_cat_limitI, rule assms(1))
  interpret is_tm_cat_cone \<alpha> r \<JJ> \<CC> \<FF> u by (rule assms(1))  
  fix r' u' assume prems: "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  then interpret u': is_cat_cone \<alpha> r' \<JJ> \<CC> \<FF> u' . 
  have "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by
      (
        intro
          is_tm_cat_coneI 
          NTCod.is_tm_functor_axioms
          u'.cat_cone_obj 
          u'.is_ntcf_axioms
      )
  then show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
    by (rule assms(2))
qed

lemma is_tm_cat_colimitI':
  assumes "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>u' r'. u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
  shows "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_tm_cat_colimitI, rule assms(1))
  interpret is_tm_cat_cocone \<alpha> r \<JJ> \<CC> \<FF> u by (rule assms(1))
  fix r' u' assume prems: "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  then interpret u': is_cat_cocone \<alpha> r' \<JJ> \<CC> \<FF> u' . 
  have "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by
      (
        intro
          is_tm_cat_coconeI 
          NTDom.is_tm_functor_axioms
          u'.cat_cocone_obj 
          u'.is_ntcf_axioms
      )
  then show "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
    by (rule assms(2))
qed


text\<open>Elementary properties.\<close>

sublocale is_tm_cat_limit \<subseteq> is_cat_limit
  by (intro is_cat_limitI, rule is_cat_cone_axioms, rule tm_cat_lim_ua_fo)

sublocale is_tm_cat_colimit \<subseteq> is_cat_colimit
  by (intro is_cat_colimitI, rule is_cat_cocone_axioms, rule tm_cat_colim_ua_of)

lemma (in is_cat_limit) cat_lim_is_tm_cat_limit:
  assumes "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
proof(intro is_tm_cat_limitI)
  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> by (rule assms) 
  show "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by (intro is_tm_cat_coneI assms is_ntcf_axioms cat_cone_obj)
  fix u' r' assume prems: "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
    by (rule cat_lim_ua_fo[OF prems])
qed

lemma (in is_cat_colimit) cat_colim_is_tm_cat_colimit:
  assumes "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
proof(intro is_tm_cat_colimitI)
  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> by (rule assms) 
  show "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by (intro is_tm_cat_coconeI assms is_ntcf_axioms cat_cocone_obj)
  fix u' r' assume prems: "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  show "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
    by (rule cat_colim_ua_of[OF prems])
qed


text\<open>Limits, colimits and universal arrows.\<close>

lemma (in is_tm_cat_limit) tm_cat_lim_is_universal_arrow_fo:
  "universal_arrow_fo (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u)"
proof(intro is_functor.universal_arrow_foI)

  show "\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Funct \<alpha> \<JJ> \<CC>"
    by 
      (
        intro 
          tm_cf_diagonal_is_functor 
          NTCod.HomDom.tiny_category_axioms
          NTDom.HomCod.category_axioms
      )

  show "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (intro cat_cone_obj)
  then show "ntcf_arrow u : \<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
    by 
      (
        cs_concl
          cs_simp: cat_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )

  fix r' u' assume prems: 
    "r' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "u' : \<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
  from prems(1) have [cat_cs_simps]: 
    "cf_of_cf_map \<JJ> \<CC> (cf_map \<FF>) = \<FF>"
    "cf_of_cf_map \<JJ> \<CC> (cf_map (cf_const \<JJ> \<CC> r')) = cf_const \<JJ> \<CC> r'"
    by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)+
  from prems(2,1) have 
    "u' : cf_map (cf_const \<JJ> \<CC> r') \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
    by (cs_prems cs_shallow cs_simp: cat_cs_simps)
  note u'[unfolded cat_cs_simps] = cat_Funct_is_arrD[OF this]

  from 
    tm_cat_lim_ua_fo[
      OF is_cat_coneI[OF is_tm_ntcfD(1)[OF u'(1)] prems(1)]
      ] 
  obtain f 
    where f: "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      and [symmetric, cat_cs_simps]: 
        "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
      and f_unique: 
        "\<lbrakk>
          f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r;
          ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'
         \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis

  show "\<exists>!f'.
    f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and>
    u' = umap_fo (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
  proof(intro ex1I conjI; (elim conjE)?)
    show "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by (rule f)
    with cat_cone_obj show u'_def: 
      "u' = umap_fo (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m  \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: u'(2)[symmetric] cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    fix f' assume prems': 
      "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      "u' = umap_fo (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    from prems'(2) f prems' cat_cone_obj have u'_def':
      "u' = ntcf_arrow (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from prems'(1) have "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
      by (cs_concl cs_simp: cat_FUNCT_cs_simps u'_def' cs_intro: cat_cs_intros)
    from f_unique[OF prems'(1) this] show "f' = f" .

  qed

qed

lemma (in is_tm_cat_cone) tm_cat_cone_is_tm_cat_limit:
  assumes "universal_arrow_fo (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>)"
  shows "\<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_tm_cat_limitI' is_tm_cat_cone_axioms)

  fix u' c' assume prems: "u' : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"

  interpret u': is_tm_cat_cone \<alpha> c' \<JJ> \<CC> \<FF> u' by (rule prems)

  from u'.tm_cat_cone_obj have u'_is_arr:
    "ntcf_arrow u' : \<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
    by
      (
        cs_concl
          cs_simp: cat_cs_simps
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )

  from is_functor.universal_arrow_foD(3)
    [
      OF
        tm_cf_diagonal_is_functor[
          OF NTCod.HomDom.tiny_category_axioms NTDom.HomCod.category_axioms
          ]
        assms
        u'.cat_cone_obj
        u'_is_arr
    ]
  obtain f where f: "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and u'_def': "ntcf_arrow u' =
      umap_fo (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
    and f'_unique:
      "\<lbrakk>
        f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c;
        ntcf_arrow u' =
          umap_fo (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
       \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis

  from u'_def' f cat_cone_obj have u'_def: "u' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
    by
      (
        cs_prems 
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )

  show "\<exists>!f'. f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> u' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
  proof(intro ex1I conjI; (elim conjE)?, (rule f)?, (rule u'_def)?)
    fix f'' assume prems': 
      "f'' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c" "u' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f''"
    from prems' have 
      "ntcf_arrow u' =
        umap_fo (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>"
      by
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from f'_unique[OF prems'(1) this] show "f'' = f".
  qed

qed

lemma (in is_tm_cat_colimit) tm_cat_colim_is_universal_arrow_of:
  "universal_arrow_of (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u)"
proof(intro is_functor.universal_arrow_ofI)

  show "\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Funct \<alpha> \<JJ> \<CC>"
    by 
      (
        intro 
          tm_cf_diagonal_is_functor 
          NTDom.HomDom.tiny_category_axioms 
          NTDom.HomCod.category_axioms
      )

  show "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (intro cat_cocone_obj)

  then show "ntcf_arrow u : cf_map \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> \<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    by 
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )

  fix r' u' assume prems: 
    "r' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "u' : cf_map \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> \<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"
  from prems(1) have [cat_cs_simps]: 
    "cf_of_cf_map \<JJ> \<CC> (cf_map \<FF>) = \<FF>"
    "cf_of_cf_map \<JJ> \<CC> (cf_map (cf_const \<JJ> \<CC> r')) = cf_const \<JJ> \<CC> r'"
    by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)+
  from prems(2,1) have
    "u' : cf_map \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> cf_map (cf_const \<JJ> \<CC> r')"
    by (cs_prems cs_shallow cs_simp: cat_cs_simps)
  note u'[unfolded cat_cs_simps] = cat_Funct_is_arrD[OF this]

  from cat_colim_ua_of[OF is_cat_coconeI[OF is_tm_ntcfD(1)[OF u'(1)] prems(1)]]
  obtain f 
    where f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'"
      and [symmetric, cat_cs_simps]: 
        "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      and f_unique:
        "\<lbrakk>
          f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r';
          ntcf_of_ntcf_arrow \<JJ> \<CC> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u
         \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis

  show " \<exists>!f'.
    f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and>
    u' = umap_of (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
  proof(intro ex1I conjI; (elim conjE)?)
  
    show "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" by (rule f)

    with cat_cocone_obj show u'_def:
      "u' = umap_of (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      by 
        (
          cs_concl
            cs_simp: u'(2)[symmetric] cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
  
    fix f' assume prems':
      "f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'"
      "u' = umap_of (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    from prems'(2) f prems' cat_cocone_obj have u'_def':
      "u' = ntcf_arrow (ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u)"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from prems'(1) have "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      by 
        (
          cs_concl cs_shallow 
            cs_simp: cat_FUNCT_cs_simps u'_def' cs_intro: cat_cs_intros
        )
    from f_unique[OF prems'(1) this] show "f' = f" .

  qed

qed

lemma (in is_tm_cat_cocone) tm_cat_cocone_is_tm_cat_colimit:
  assumes "universal_arrow_of (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>)"
  shows "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_tm_cat_colimitI' is_tm_cat_cocone_axioms)
  
  fix u' c' assume prems: "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"

  interpret u': is_tm_cat_cocone \<alpha> c' \<JJ> \<CC> \<FF> u' by (rule prems)

  from u'.tm_cat_cocone_obj have u'_is_arr:
    "ntcf_arrow u' : cf_map \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> \<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr>"
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )

  from is_functor.universal_arrow_ofD(3)
    [
      OF
        tm_cf_diagonal_is_functor[
          OF NTDom.HomDom.tiny_category_axioms NTDom.HomCod.category_axioms
          ]
        assms
        u'.cat_cocone_obj
        u'_is_arr
    ]
  obtain f where f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> c'"
    and u'_def': "ntcf_arrow u' =
      umap_of (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
    and f'_unique:
      "\<lbrakk>
        f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c';
        ntcf_arrow u' =
          umap_of (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
       \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis

  from u'_def' f cat_cocone_obj have u'_def: "u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>"
    by
      (
        cs_prems
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  
  show "\<exists>!f'. f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>"
  proof(intro ex1I conjI; (elim conjE)?, (rule f)?, (rule u'_def)?)
    fix f'' assume prems': 
      "f'' : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" "u' = ntcf_const \<JJ> \<CC> f'' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>"
    from prems' have 
      "ntcf_arrow u' =
        umap_of (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) c (ntcf_arrow \<NN>) c'\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from f'_unique[OF prems'(1) this] show "f'' = f".
  qed

qed
  

text\<open>Duality.\<close>

lemma (in is_tm_cat_limit) is_tm_cat_colimit_op:
  "op_ntcf u : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
proof(intro is_tm_cat_colimitI')
  show "op_ntcf u : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by (cs_concl cs_shallow cs_simp: cs_intro: cat_op_intros)
  fix u' r' assume prems: 
    "u' : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  interpret u': is_tm_cat_cocone \<alpha> r' \<open>op_cat \<JJ>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<FF>\<close> u' 
    by (rule prems)
  from tm_cat_lim_ua_fo[OF u'.is_cat_cone_op[unfolded cat_op_simps]] obtain f 
    where f: "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      and op_u'_def: "op_ntcf u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
      and f_unique: 
        "\<lbrakk> f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r; op_ntcf u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f' \<rbrakk> \<Longrightarrow>
          f' = f"
    for f'
    by metis
  from op_u'_def have "op_ntcf (op_ntcf u') = op_ntcf (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f)"
    by simp
  from this f have u'_def: 
    "u' = ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf u"
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros)
  show "\<exists>!f'. 
    f' : r \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r' \<and> 
    u' = ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf u"
  proof(intro ex1I conjI; (elim conjE)?, (unfold cat_op_simps)?)
    fix f' assume prems': 
      "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      "u' = ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf u"
    from prems'(2) have "op_ntcf u' =
      op_ntcf (ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf u)"
      by simp
    from this prems'(1) have "op_ntcf u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros
        )
    from f_unique[OF prems'(1) this] show "f' = f". 
  qed (intro u'_def f)+
qed

lemma (in is_tm_cat_limit) is_tm_cat_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_colimit_op)

lemmas [cat_op_intros] = is_tm_cat_limit.is_tm_cat_colimit_op'

lemma (in is_tm_cat_colimit) is_tm_cat_limit_op:
  "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
proof(intro is_tm_cat_limitI')
  show "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by (cs_concl cs_shallow cs_simp: cs_intro: cat_op_intros)
  fix u' r' assume prems: 
    "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  interpret u': is_tm_cat_cone \<alpha> r' \<open>op_cat \<JJ>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<FF>\<close> u' 
    by (rule prems)
  from tm_cat_colim_ua_of[OF u'.is_cat_cocone_op[unfolded cat_op_simps]] obtain f 
    where f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'"
      and op_u'_def: "op_ntcf u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      and f_unique: 
        "\<lbrakk> f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'; op_ntcf u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis
  from op_u'_def have "op_ntcf (op_ntcf u') = op_ntcf (ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u)"
    by simp
  from this f have u'_def: 
    "u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f"
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros)
  show "\<exists>!f'. 
    f' : r' \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r \<and> 
    u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f'"
  proof(intro ex1I conjI; (elim conjE)?, (unfold cat_op_simps)?)
    fix f' assume prems': 
      "f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'"
      "u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f'"
    from prems'(2) have "op_ntcf u' =
      op_ntcf (op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f')"
      by simp
    from this prems'(1) have "op_ntcf u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros
        )
    from f_unique[OF prems'(1) this] show "f' = f". 
  qed (intro u'_def f)+
qed

lemma (in is_tm_cat_colimit) is_tm_cat_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_limit_op)

lemmas [cat_op_intros] = is_tm_cat_colimit.is_tm_cat_colimit_op'


subsubsection\<open>Further properties\<close>

lemma (in is_tm_cat_limit) tm_cat_lim_is_tm_cat_limit_if_iso_arr:
  assumes "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r"
  shows "u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  note f = is_iso_arrD(1)[OF assms]
  from f(1) interpret u': is_tm_cat_cone \<alpha> r' \<JJ> \<CC> \<FF> \<open>u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f\<close> 
    by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)
  show ?thesis
  proof
    (
      intro u'.tm_cat_cone_is_tm_cat_limit,
      rule is_functor.universal_arrow_fo_if_universal_arrow_fo,
      rule tm_cf_diagonal_is_functor,
      rule NTCod.HomDom.tiny_category_axioms,
      rule NTDom.HomCod.category_axioms,
      rule tm_cat_lim_is_universal_arrow_fo
    )
    show "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r" by (rule assms)
    from f show "ntcf_arrow (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f) =
      umap_fo (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
  qed
qed

lemma (in is_tm_cat_colimit) tm_cat_colim_is_tm_cat_colimit_if_iso_arr:
  assumes "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'"
  shows "ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  note f = is_iso_arrD(1)[OF assms]
  from f(1) interpret u': 
    is_tm_cat_cocone \<alpha> r' \<JJ> \<CC> \<FF> \<open>ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u\<close> 
    by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)
  from f have [symmetric, cat_op_simps]:
    "op_ntcf (ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u) =
      op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f"
    by
      (
        cs_concl cs_shallow 
          cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros
      )
  show ?thesis
    by 
      (
        rule is_tm_cat_limit.is_tm_cat_colimit_op
          [
            OF is_tm_cat_limit.tm_cat_lim_is_tm_cat_limit_if_iso_arr[
              OF is_tm_cat_limit_op, unfolded cat_op_simps, OF assms(1)
              ],
            unfolded cat_op_simps
          ]
      )
qed



subsection\<open>Finite limit and finite colimit\<close>

locale is_cat_finite_limit = 
  is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r u + NTDom.HomDom: finite_category \<alpha> \<JJ>
  for \<alpha> \<JJ> \<CC> \<FF> r u

syntax "_is_cat_finite_limit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_finite_limit \<alpha> \<JJ> \<CC> \<FF> r u"

locale is_cat_finite_colimit = 
  is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r u + NTDom.HomDom: finite_category \<alpha> \<JJ>
  for \<alpha> \<JJ> \<CC> \<FF> r u

syntax "_is_cat_finite_colimit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_finite_colimit \<alpha> \<JJ> \<CC> \<FF> r u"


text\<open>Rules.\<close>

lemma (in is_cat_finite_limit) is_cat_finite_limit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_limit_axioms)

mk_ide rf is_cat_finite_limit_def
  |intro is_cat_finite_limitI|
  |dest is_cat_finite_limitD[dest]|
  |elim is_cat_finite_limitE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_finite_limitD

lemma (in is_cat_finite_colimit) 
  is_cat_finite_colimit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n r' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_colimit_axioms)

mk_ide rf is_cat_finite_colimit_def[unfolded is_cat_colimit_axioms_def]
  |intro is_cat_finite_colimitI|
  |dest is_cat_finite_colimitD[dest]|
  |elim is_cat_finite_colimitE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_finite_colimitD


text\<open>Duality.\<close>

lemma (in is_cat_finite_limit) is_cat_finite_colimit_op:
  "op_ntcf u : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by
    (
      cs_concl cs_shallow
        cs_intro: is_cat_finite_colimitI cat_op_intros cat_small_cs_intros
    )

lemma (in is_cat_finite_limit) is_cat_finite_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n r : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_colimit_op)

lemmas [cat_op_intros] = is_cat_finite_limit.is_cat_finite_colimit_op'

lemma (in is_cat_finite_colimit) is_cat_finite_limit_op:
  "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by 
    (
      cs_concl cs_shallow 
        cs_intro: is_cat_finite_limitI cat_op_intros cat_small_cs_intros
    )

lemma (in is_cat_finite_colimit) is_cat_finite_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_limit_op)

lemmas [cat_op_intros] = is_cat_finite_colimit.is_cat_finite_colimit_op'


text\<open>Elementary properties.\<close>

sublocale is_cat_finite_limit \<subseteq> is_tm_cat_limit
  by
    (
      intro 
        is_tm_cat_limitI 
        is_tm_cat_coneI 
        is_ntcf_axioms 
        cat_lim_ua_fo 
        cat_cone_obj 
        NTCod.cf_is_tm_functor_if_HomDom_finite_category[
          OF NTDom.HomDom.finite_category_axioms
          ]
    )

sublocale is_cat_finite_colimit \<subseteq> is_tm_cat_colimit
  by
    (
      intro 
        is_tm_cat_colimitI 
        is_tm_cat_coconeI 
        is_ntcf_axioms 
        cat_colim_ua_of 
        cat_cocone_obj 
        NTDom.cf_is_tm_functor_if_HomDom_finite_category[
          OF NTDom.HomDom.finite_category_axioms
          ]
    )



subsection\<open>Creation of limits\<close>


text\<open>See Chapter V-1 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition cf_creates_limits :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "cf_creates_limits \<alpha> \<GG> \<FF> =
    (
      \<forall>\<tau> b.
        \<tau> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<GG>\<lparr>HomCod\<rparr> \<longrightarrow>
        (
          (
            \<exists>!\<sigma>a. \<exists>\<sigma> a. \<sigma>a = \<langle>\<sigma>, a\<rangle> \<and>
              \<sigma> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<FF>\<lparr>HomCod\<rparr> \<and>
              \<tau> = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<and>
              b = \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>
          ) \<and>
          (
            \<forall>\<sigma> a.
              \<sigma> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<FF>\<lparr>HomCod\<rparr> \<longrightarrow>
              \<tau> = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<longrightarrow>
              b = \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<longrightarrow>
              \<sigma> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<FF>\<lparr>HomCod\<rparr>
          )
        )
    )"


text\<open>Rules.\<close>

context
  fixes \<alpha> \<JJ> \<AA> \<BB> \<GG> \<FF>
  assumes \<FF>: "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and \<GG>: "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
begin

interpretation \<FF>: is_functor \<alpha> \<JJ> \<AA> \<FF> by (rule \<FF>)
interpretation \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule \<GG>)

mk_ide rf cf_creates_limits_def[
  where \<alpha>=\<alpha> and \<FF>=\<FF> and \<GG>=\<GG>, unfolded cat_cs_simps
  ]
  |intro cf_creates_limitsI|
  |dest cf_creates_limitsD'|
  |elim cf_creates_limitsE'|

end

lemmas cf_creates_limitsD[dest!] = cf_creates_limitsD'[rotated 2]
  and cf_creates_limitsE[elim!] = cf_creates_limitsE'[rotated 2]

lemma cf_creates_limitsE'':
  assumes "cf_creates_limits \<alpha> \<GG> \<FF>"
    and "\<tau> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains \<sigma> r where "\<sigma> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<tau> = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>"
    and "b = \<GG>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
proof-
  note cflD = cf_creates_limitsD[OF assms]
  from conjunct1[OF cflD] obtain \<sigma> r
    where \<sigma>: "\<sigma> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      and \<tau>_def: "\<tau> = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>"
      and b_def: "b = \<GG>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    by metis
  moreover have "\<sigma> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    by (rule conjunct2[OF cflD, rule_format, OF \<sigma> \<tau>_def b_def])
  ultimately show ?thesis using that by auto
qed



subsection\<open>Preservation of limits and colimits\<close>


subsubsection\<open>Definitions and elementary properties\<close>


text\<open>See Chapter V-4 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition cf_preserves_limits :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "cf_preserves_limits \<alpha> \<GG> \<FF> =
    (
      \<forall>\<sigma> a.
        \<sigma> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<FF>\<lparr>HomCod\<rparr> \<longrightarrow>
        \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<GG>\<lparr>HomCod\<rparr>
    )"

definition cf_preserves_colimits :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "cf_preserves_colimits \<alpha> \<GG> \<FF> =
    (
      \<forall>\<sigma> a.
        \<sigma> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m a : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<FF>\<lparr>HomCod\<rparr> \<longrightarrow>
        \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> : \<GG> \<circ>\<^sub>C\<^sub>F \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>HomDom\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<GG>\<lparr>HomCod\<rparr>
    )"


text\<open>Rules.\<close>

context
  fixes \<alpha> \<JJ> \<AA> \<BB> \<GG> \<FF>
  assumes \<FF>: "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and \<GG>: "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
begin

interpretation \<FF>: is_functor \<alpha> \<JJ> \<AA> \<FF> by (rule \<FF>)
interpretation \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule \<GG>)

mk_ide rf cf_preserves_limits_def[
  where \<alpha>=\<alpha> and \<FF>=\<FF> and \<GG>=\<GG>, unfolded cat_cs_simps
  ]
  |intro cf_preserves_limitsI|
  |dest cf_preserves_limitsD'|
  |elim cf_preserves_limitsE'|

mk_ide rf cf_preserves_colimits_def[
  where \<alpha>=\<alpha> and \<FF>=\<FF> and \<GG>=\<GG>, unfolded cat_cs_simps
  ]
  |intro cf_preserves_colimitsI|
  |dest cf_preserves_colimitsD'|
  |elim cf_preserves_colimitsE'|

end

lemmas cf_preserves_limitsD[dest!] = cf_preserves_limitsD'[rotated 2]
  and cf_preserves_limitsE[elim!] = cf_preserves_limitsE'[rotated 2]

lemmas cf_preserves_colimitsD[dest!] = cf_preserves_colimitsD'[rotated 2]
  and cf_preserves_colimitsE[elim!] = cf_preserves_colimitsE'[rotated 2]


text\<open>Duality.\<close>

lemma cf_preserves_colimits_op[cat_op_simps]:
  assumes "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows 
    "cf_preserves_colimits \<alpha> (op_cf \<GG>) (op_cf \<FF>) \<longleftrightarrow>
      cf_preserves_limits \<alpha> \<GG> \<FF>"
proof

  interpret \<FF>: is_functor \<alpha> \<JJ> \<AA> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(2))

  show "cf_preserves_limits \<alpha> \<GG> \<FF>"
    if "cf_preserves_colimits \<alpha> (op_cf \<GG>) (op_cf \<FF>)"
  proof(rule cf_preserves_limitsI, rule assms(1), rule assms(2))
    fix \<sigma> r assume "\<sigma> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    then interpret \<sigma>: is_cat_limit \<alpha> \<JJ> \<AA> \<FF> r \<sigma> .
    show "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by 
        (
          rule is_cat_colimit.is_cat_limit_op
            [
              OF cf_preserves_colimitsD
                [
                  OF that \<sigma>.is_cat_colimit_op \<FF>.is_functor_op \<GG>.is_functor_op,
                  folded op_cf_cf_comp op_ntcf_cf_ntcf_comp
                ],
              unfolded cat_op_simps
            ]
        )
  qed

  show "cf_preserves_colimits \<alpha> (op_cf \<GG>) (op_cf \<FF>)"
    if "cf_preserves_limits \<alpha> \<GG> \<FF>"
  proof
    (
      rule cf_preserves_colimitsI, 
      rule \<FF>.is_functor_op, 
      rule \<GG>.is_functor_op, 
      unfold cat_op_simps
    )
    fix \<sigma> r assume "\<sigma> : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>"
    then interpret \<sigma>: is_cat_colimit \<alpha> \<open>op_cat \<JJ>\<close> \<open>op_cat \<AA>\<close> \<open>op_cf \<FF>\<close> r \<sigma> . 
    show "op_cf \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> :
      op_cf \<GG> \<circ>\<^sub>C\<^sub>F op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m \<GG>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
      by 
        (
          rule is_cat_limit.is_cat_colimit_op
            [
              OF cf_preserves_limitsD[
                OF that \<sigma>.is_cat_limit_op[unfolded cat_op_simps] assms(1,2)
                ],
              unfolded cat_op_simps
            ]
        )
  qed

qed

lemma cf_preserves_limits_op[cat_op_simps]:
  assumes "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows 
    "cf_preserves_limits \<alpha> (op_cf \<GG>) (op_cf \<FF>) \<longleftrightarrow>
      cf_preserves_colimits \<alpha> \<GG> \<FF>"
proof

  interpret \<FF>: is_functor \<alpha> \<JJ> \<AA> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(2))

  show "cf_preserves_colimits \<alpha> \<GG> \<FF>" 
    if "cf_preserves_limits \<alpha> (op_cf \<GG>) (op_cf \<FF>)"
  proof(rule cf_preserves_colimitsI, rule assms(1), rule assms(2))
    fix \<sigma> r assume "\<sigma> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
    then interpret \<sigma>: is_cat_colimit \<alpha> \<JJ> \<AA> \<FF> r \<sigma> .
    show "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> : \<GG> \<circ>\<^sub>C\<^sub>F \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m \<GG>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by 
        (
          rule is_cat_limit.is_cat_colimit_op
            [
              OF cf_preserves_limitsD
                [
                  OF that \<sigma>.is_cat_limit_op \<FF>.is_functor_op \<GG>.is_functor_op,
                  folded op_cf_cf_comp op_ntcf_cf_ntcf_comp
                ],
              unfolded cat_op_simps
            ]
        )
  qed

  show "cf_preserves_limits \<alpha> (op_cf \<GG>) (op_cf \<FF>)"
    if "cf_preserves_colimits \<alpha> \<GG> \<FF>"
  proof
    (
      rule cf_preserves_limitsI, 
      rule \<FF>.is_functor_op, 
      rule \<GG>.is_functor_op, 
      unfold cat_op_simps
    )
    fix \<sigma> r assume "\<sigma> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>"
    then interpret \<sigma>: is_cat_limit \<alpha> \<open>op_cat \<JJ>\<close> \<open>op_cat \<AA>\<close> \<open>op_cf \<FF>\<close> r \<sigma> . 
    show "op_cf \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> :
      \<GG>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m op_cf \<GG> \<circ>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
      by 
        (
          rule is_cat_colimit.is_cat_limit_op
            [
              OF cf_preserves_colimitsD[
                OF that \<sigma>.is_cat_colimit_op[unfolded cat_op_simps] assms(1,2)
                ],
              unfolded cat_op_simps
            ]
        )
  qed
  
qed


subsubsection\<open>Further properties\<close>

lemma cf_preserves_limits_if_cf_creates_limits:
  \<comment>\<open>See Theorem 2 in Chapter V-4 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<psi> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "cf_creates_limits \<alpha> \<GG> \<FF>"
  shows "cf_preserves_limits \<alpha> \<GG> \<FF>"
proof-

  interpret \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<JJ> \<AA> \<FF> by (rule assms(2))
  interpret \<psi>: is_cat_limit \<alpha> \<JJ> \<BB> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> b \<psi>
    by (intro is_cat_limit.cat_lim_is_tm_cat_limit assms(3,4))

  show ?thesis
  proof
    (
      intro cf_preserves_limitsI,
      rule \<FF>.is_functor_axioms,
      rule \<GG>.is_functor_axioms
    )

    fix \<sigma> a assume prems: "\<sigma> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    then interpret \<sigma>: is_cat_limit \<alpha> \<JJ> \<AA> \<FF> a \<sigma> .

    obtain \<tau> A
      where \<tau>: "\<tau> : A <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        and \<psi>_def: "\<psi> = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau>"
        and b_def: "b = \<GG>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
      by 
        (
          rule cf_creates_limitsE''
            [
              OF 
                assms(4)  
                \<psi>.is_cat_limit_axioms
                \<FF>.is_functor_axioms
                \<GG>.is_functor_axioms
            ]  
        )
    from \<tau> interpret \<tau>: is_cat_limit \<alpha> \<JJ> \<AA> \<FF> A \<tau> .

    from cat_lim_ex_is_iso_arr[OF \<tau>.is_cat_limit_axioms prems] obtain f
      where f: "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<AA>\<^esub> A" and \<sigma>_def: "\<sigma> = \<tau> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<AA> f"
      by auto

    note f = f is_iso_arrD(1)[OF f]

    from f(2) have "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (intro is_cat_coneI)
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

    from \<sigma>_def have "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<tau> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<AA> f)" 
      by simp
    also from f(2) have "\<dots> = \<psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> (\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)"
      by (cs_concl_step cf_ntcf_comp_ntcf_vcomp)
        (
          cs_concl
            cs_simp: cat_cs_simps \<psi>_def[symmetric] cs_intro: cat_cs_intros
        )
    finally have \<GG>\<sigma>: "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> = \<psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> (\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)" .

    show "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by 
        (
          rule \<psi>.cat_lim_is_cat_limit_if_is_iso_arr
            [
              OF \<GG>.cf_ArrMap_is_iso_arr[OF f(1), folded b_def], 
              folded \<GG>\<sigma>
            ]
        )
    
  qed
  
qed



subsection\<open>Continuous and cocontinuous functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition is_cf_continuous :: "V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cf_continuous \<alpha> \<GG> \<longleftrightarrow>
    (\<forall>\<FF> \<JJ>. \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<GG>\<lparr>HomDom\<rparr> \<longrightarrow> cf_preserves_limits \<alpha> \<GG> \<FF>)"

definition is_cf_cocontinuous :: "V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cf_cocontinuous \<alpha> \<GG> \<longleftrightarrow>
    (\<forall>\<FF> \<JJ>. \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<GG>\<lparr>HomDom\<rparr> \<longrightarrow> cf_preserves_colimits \<alpha> \<GG> \<FF>)"


text\<open>Rules.\<close>

context
  fixes \<alpha> \<JJ> \<AA> \<BB> \<GG> \<FF>
  assumes \<GG>: "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
begin

interpretation \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule \<GG>)

mk_ide rf is_cf_continuous_def[where \<alpha>=\<alpha> and \<GG>=\<GG>, unfolded cat_cs_simps]
  |intro is_cf_continuousI|
  |dest is_cf_continuousD'|
  |elim is_cf_continuousE'|

mk_ide rf is_cf_cocontinuous_def[where \<alpha>=\<alpha> and \<GG>=\<GG>, unfolded cat_cs_simps]
  |intro is_cf_cocontinuousI|
  |dest is_cf_cocontinuousD'|
  |elim is_cf_cocontinuousE'|

end

lemmas is_cf_continuousD[dest!] = is_cf_continuousD'[rotated]
  and is_cf_continuousE[elim!] = is_cf_continuousE'[rotated]

lemmas is_cf_cocontinuousD[dest!] = is_cf_cocontinuousD'[rotated]
  and is_cf_cocontinuousE[elim!] = is_cf_cocontinuousE'[rotated]


text\<open>Duality.\<close>

lemma is_cf_continuous_op[cat_op_simps]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "is_cf_continuous \<alpha> (op_cf \<GG>) \<longleftrightarrow> is_cf_cocontinuous \<alpha> \<GG>"
proof
  interpret \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  show "is_cf_cocontinuous \<alpha> \<GG>" if "is_cf_continuous \<alpha> (op_cf \<GG>)"
  proof(intro is_cf_cocontinuousI, rule assms)
    fix \<FF> \<JJ> assume prems': "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    then interpret \<FF>: is_functor \<alpha> \<JJ> \<AA> \<FF> .
    show "cf_preserves_colimits \<alpha> \<GG> \<FF>"
      by 
        (
          rule cf_preserves_limits_op
            [
              THEN iffD1, 
              OF
                prems' 
                assms(1) 
                is_cf_continuousD[OF that \<FF>.is_functor_op \<GG>.is_functor_op] 
            ]
        )
  qed
  show "is_cf_continuous \<alpha> (op_cf \<GG>)" if "is_cf_cocontinuous \<alpha> \<GG>"
  proof(intro is_cf_continuousI, rule \<GG>.is_functor_op)
    fix \<FF> \<JJ> assume prems': "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>"
    then interpret \<FF>: is_functor \<alpha> \<JJ> \<open>op_cat \<AA>\<close> \<FF> .
    from that assms have op_op_bundle:
      "is_cf_cocontinuous \<alpha> (op_cf (op_cf \<GG>))"
      "op_cf (op_cf \<GG>) : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      unfolding cat_op_simps .
    show "cf_preserves_limits \<alpha> (op_cf \<GG>) \<FF>"
      by 
        (
          rule cf_preserves_colimits_op
            [
              THEN iffD1, 
              OF
                \<FF>.is_functor_axioms 
                \<GG>.is_functor_op 
                is_cf_cocontinuousD
                  [
                    OF
                      op_op_bundle(1) 
                      \<FF>.is_functor_op[unfolded cat_op_simps] 
                      op_op_bundle(2)
                  ]
            ]
        )
  qed
qed

lemma is_cf_cocontinuous_op[cat_op_simps]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "is_cf_cocontinuous \<alpha> (op_cf \<GG>) \<longleftrightarrow> is_cf_continuous \<alpha> \<GG>"
proof
  interpret \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  show "is_cf_continuous \<alpha> \<GG>" if "is_cf_cocontinuous \<alpha> (op_cf \<GG>)"
  proof(intro is_cf_continuousI, rule assms)
    fix \<FF> \<JJ> assume prems': "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    then interpret \<FF>: is_functor \<alpha> \<JJ> \<AA> \<FF> .
    show "cf_preserves_limits \<alpha> \<GG> \<FF>"
      by 
        (
          rule cf_preserves_colimits_op
            [
              THEN iffD1, 
              OF
                prems' 
                assms(1) 
                is_cf_cocontinuousD[OF that \<FF>.is_functor_op \<GG>.is_functor_op] 
            ]
        )
  qed
  show "is_cf_cocontinuous \<alpha> (op_cf \<GG>)" if "is_cf_continuous \<alpha> \<GG>"
  proof(intro is_cf_cocontinuousI, rule \<GG>.is_functor_op)
    fix \<FF> \<JJ> assume prems': "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>"
    then interpret \<FF>: is_functor \<alpha> \<JJ> \<open>op_cat \<AA>\<close> \<FF> .
    from that assms have op_op_bundle:
      "is_cf_continuous \<alpha> (op_cf (op_cf \<GG>))"
      "op_cf (op_cf \<GG>) : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      unfolding cat_op_simps .
    show "cf_preserves_colimits \<alpha> (op_cf \<GG>) \<FF>"
      by 
        (
          rule cf_preserves_limits_op
            [
              THEN iffD1, 
              OF
                \<FF>.is_functor_axioms 
                \<GG>.is_functor_op 
                is_cf_continuousD
                  [
                    OF
                      op_op_bundle(1) 
                      \<FF>.is_functor_op[unfolded cat_op_simps] 
                      op_op_bundle(2)
                  ]
            ]
        )
  qed
qed


subsubsection\<open>Category isomorphisms are continuous and cocontinuous\<close>

lemma (in is_iso_functor) iso_cf_is_cf_continuous: "is_cf_continuous \<alpha> \<FF>"
proof(intro is_cf_continuousI)
  fix \<JJ> \<GG> assume prems: "\<GG> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  then interpret \<GG>: is_functor \<alpha> \<JJ> \<AA> \<GG> .
  show "cf_preserves_limits \<alpha> \<FF> \<GG>"
  proof(intro cf_preserves_limitsI)
    fix a \<sigma> assume "\<sigma> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    then interpret \<sigma>: is_cat_limit \<alpha> \<JJ> \<AA> \<GG> a \<sigma> .
    show "\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> \<circ>\<^sub>C\<^sub>F \<GG> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    proof(intro is_cat_limitI)
      fix r' \<tau> assume "\<tau> : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> \<circ>\<^sub>C\<^sub>F \<GG> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      then interpret \<tau>: is_cat_cone \<alpha> r' \<JJ> \<BB> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG>\<close> \<tau> .
      note [cat_cs_simps] = cf_comp_assoc_helper[
          where \<HH>=\<open>inv_cf \<FF>\<close> and \<GG>=\<FF> and \<FF>=\<GG> and \<Q>=\<open>cf_id \<AA>\<close>
          ]
      have inv_\<tau>: "inv_cf \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau> :
        inv_cf \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cf_cs_simps
              cs_intro: cat_cs_intros cf_cs_intros
          )
      from is_cat_limit.cat_lim_unique_cone'[OF \<sigma>.is_cat_limit_axioms inv_\<tau>]
      obtain f where f: "f : inv_cf \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> a"
        and f_up: "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow>
          (inv_cf \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau>)\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f"
        and f_unique:
          "\<lbrakk>
            f' : inv_cf \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> a;
            \<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> 
              (inv_cf \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau>)\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f'
          \<rbrakk> \<Longrightarrow> f' = f"
        for f'
        by metis
      have [cat_cs_simps]: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<sigma>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
        if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
      proof-
        from f_up[OF that] that have 
          "inv_cf \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f"
          by (cs_prems cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        then have 
          "\<FF>\<lparr>ArrMap\<rparr>\<lparr>inv_cf \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>\<rparr>\<rparr> =
            \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<sigma>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr>"
          by simp
        from this that f show ?thesis 
          by 
            (
              cs_prems cs_shallow 
                cs_simp: cat_cs_simps cf_cs_simps cs_intro: cat_cs_intros
            ) 
            simp
      qed
      show "\<exists>!f'.
        f' : r' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<and> \<tau> = \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> f'"
      proof(intro ex1I conjI; (elim conjE)?)
        from f have 
          "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>inv_cf \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          by (cs_concl cs_shallow cs_intro: cat_cs_intros)
        then show "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : r' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          by (cs_prems cs_shallow cs_simp: cf_cs_simps cs_intro: cat_cs_intros)
        show "\<tau> = \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> (\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)"
        proof(rule ntcf_eqI, rule \<tau>.is_ntcf_axioms)
          from f show "\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> (\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>) :
            cf_const \<JJ> \<BB> r' \<mapsto>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F \<GG> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
            by
              (
                cs_concl
                  cs_simp: cat_cs_simps cf_cs_simps cs_intro: cat_cs_intros
              )
          then have dom_rhs:
            "\<D>\<^sub>\<circ> ((\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> (\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>))\<lparr>NTMap\<rparr>) = 
              \<JJ>\<lparr>Obj\<rparr>"
            by (cs_concl cs_simp: cat_cs_simps)
          show 
            "\<tau>\<lparr>NTMap\<rparr> = (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> (\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>))\<lparr>NTMap\<rparr>"
          proof(rule vsv_eqI, unfold \<tau>.ntcf_NTMap_vdomain dom_rhs)
            fix j assume "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
            with f show "\<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> =
              (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> (\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>))\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
              by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          qed (cs_concl cs_intro: V_cs_intros cat_cs_intros)+
        qed simp_all
        fix f' assume prems': 
          "f' : r' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          "\<tau> = \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> f'"
        have \<tau>j_def: "\<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<sigma>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f'"
          if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
        proof-
          from prems'(2) have
            "\<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<BB> f')\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
            by simp
          from this prems'(1) that show ?thesis
            by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        qed
        have "inv_cf \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> = f"
        proof(rule f_unique)
          from prems'(1) show 
            "inv_cf \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> : inv_cf \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> a"
            by
              (
                cs_concl 
                  cs_simp: cf_cs_simps cs_intro: cat_cs_intros cf_cs_intros
              )
          fix j assume "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
          from this prems'(1) show 
            "(inv_cf \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau>)\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = 
              \<sigma>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> inv_cf \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>"
            by
              (
                cs_concl 
                  cs_simp: cat_cs_simps cf_cs_simps \<tau>j_def
                  cs_intro: cat_cs_intros cf_cs_intros
              )
        qed
        then have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>inv_cf \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>" by simp
        from this prems'(1) show "f' = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
          by 
            (
              cs_prems cs_shallow 
                cs_simp: cat_cs_simps cf_cs_simps cs_intro: cat_cs_intros
            )
      qed
    qed (cs_concl cs_intro: cat_cs_intros cat_lim_cs_intros)
  qed (intro prems is_functor_axioms)+
qed (rule is_functor_axioms)

lemma (in is_iso_functor) iso_cf_is_cf_cocontinuous: "is_cf_cocontinuous \<alpha> \<FF>"
  using is_iso_functor.iso_cf_is_cf_continuous[OF is_iso_functor_op] 
  by (cs_prems cs_shallow cs_simp: cat_op_simps cs_intro: cat_cs_intros)



subsection\<open>Tiny-continuous and tiny-cocontinuous functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition is_tm_cf_continuous :: "V \<Rightarrow> V \<Rightarrow> bool"
  where "is_tm_cf_continuous \<alpha> \<GG> =
    (\<forall>\<FF> \<JJ>. \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<GG>\<lparr>HomDom\<rparr> \<longrightarrow> cf_preserves_limits \<alpha> \<GG> \<FF>)"


text\<open>Rules.\<close>

context
  fixes \<alpha> \<JJ> \<AA> \<BB> \<GG> \<FF>
  assumes \<GG>: "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
begin

interpretation \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule \<GG>)

mk_ide rf is_tm_cf_continuous_def[where \<alpha>=\<alpha> and \<GG>=\<GG>, unfolded cat_cs_simps]
  |intro is_tm_cf_continuousI|
  |dest is_tm_cf_continuousD'|
  |elim is_tm_cf_continuousE'|

end

lemmas is_tm_cf_continuousD[dest!] = is_tm_cf_continuousD'[rotated]
  and is_tm_cf_continuousE[elim!] = is_tm_cf_continuousE'[rotated]


text\<open>Elementary properties.\<close>

lemma (in is_functor) cf_continuous_is_tm_cf_continuous:
  assumes "is_cf_continuous \<alpha> \<FF>"
  shows "is_tm_cf_continuous \<alpha> \<FF>"
proof(intro is_tm_cf_continuousI, rule is_functor_axioms)
  fix \<FF>' \<JJ> assume "\<FF>' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
  then interpret \<FF>': is_tm_functor \<alpha> \<JJ> \<AA> \<FF>'.
  show "cf_preserves_limits \<alpha> \<FF> \<FF>'"
    by 
      (
        intro is_cf_continuousD[OF assms(1) _ is_functor_axioms], 
        rule \<FF>'.is_functor_axioms
      )
qed

text\<open>\newpage\<close>

end