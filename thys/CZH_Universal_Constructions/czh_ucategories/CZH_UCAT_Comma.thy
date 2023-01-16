(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Comma categories and universal constructions\<close>
theory CZH_UCAT_Comma
  imports CZH_UCAT_Limit_IT
begin



subsection\<open>
Relationship between the universal arrows, initial objects and terminal objects
\<close>

lemma (in is_functor) universal_arrow_of_if_obj_initial:
  \<comment>\<open>See Chapter III-1 in \cite{mac_lane_categories_2010}.\<close>
  assumes "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "obj_initial (c \<down>\<^sub>C\<^sub>F \<FF>) [0, r, u]\<^sub>\<circ>"
  shows "universal_arrow_of \<FF> c r u"
proof(intro universal_arrow_ofI)
  have ru: "[0, r, u]\<^sub>\<circ> \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    and f_unique: "C \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr> \<Longrightarrow> \<exists>!f. f : [0, r, u]\<^sub>\<circ> \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<FF>\<^esub> C"
    for C
    by (intro obj_initialD[OF assms(2)])+
  show r: "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and u: "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    by (intro cat_obj_cf_comma_ObjD[OF ru assms(1)])+
  fix r' u' assume prems: "r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "u' : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"
  from assms(1) prems have r'u': "[0, r', u']\<^sub>\<circ> \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    by (cs_concl cs_shallow cs_intro: cat_comma_cs_intros)
  from f_unique[OF r'u'] obtain F
    where F: "F : [0, r, u]\<^sub>\<circ> \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<FF>\<^esub> [0, r', u']\<^sub>\<circ>"
      and F_unique: "F' : [0, r, u]\<^sub>\<circ> \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<FF>\<^esub> [0, r', u']\<^sub>\<circ> \<Longrightarrow> F' = F"
    for F'
    by metis
  from cat_obj_cf_comma_is_arrE[OF F assms(1), simplified] obtain t 
    where F_def: "F = [[0, r, u]\<^sub>\<circ>, [0, r', u']\<^sub>\<circ>, [0, t]\<^sub>\<circ>]\<^sub>\<circ>"
      and t: "t : r \<mapsto>\<^bsub>\<AA>\<^esub> r'"
      and [cat_cs_simps]: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>t\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u = u'"
    by metis
  show "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<and> u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
  proof(intro ex1I conjI; (elim conjE)?; (rule t)?)
    from t u show "u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>t\<rparr>"
      by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    fix t' assume prems': "t' : r \<mapsto>\<^bsub>\<AA>\<^esub> r'" "u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>t'\<rparr>"
    from prems'(2,1) u have [symmetric, cat_cs_simps]: 
      "u' = \<FF>\<lparr>ArrMap\<rparr>\<lparr>t'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u"
      by (cs_prems cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    define F' where "F' = [[0, r, u]\<^sub>\<circ>, [0, r', u']\<^sub>\<circ>, [0, t']\<^sub>\<circ>]\<^sub>\<circ>"
    from assms(1) prems'(1) u  prems(2) have F':
      "F' : [0, r, u]\<^sub>\<circ> \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<FF>\<^esub> [0, r', u']\<^sub>\<circ>"
      unfolding F'_def
      by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_comma_cs_intros)
    from F_unique[OF this] show "t' = t" unfolding F'_def F_def by simp
  qed
qed

lemma (in is_functor) obj_initial_if_universal_arrow_of:
  \<comment>\<open>See Chapter III-1 in \cite{mac_lane_categories_2010}.\<close>
  assumes "universal_arrow_of \<FF> c r u" 
  shows "obj_initial (c \<down>\<^sub>C\<^sub>F \<FF>) [0, r, u]\<^sub>\<circ>"
proof-
  from universal_arrow_ofD[OF assms] have r: "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and u: "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and up: "\<lbrakk> r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; u' : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<rbrakk> \<Longrightarrow>
      \<exists>!f'. f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<and> u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    for r' u'
    by auto
  from u have c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by auto
  show ?thesis
  proof(intro obj_initialI)
    from r u show "[0, r, u]\<^sub>\<circ> \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_comma_cs_intros)
    fix B assume prems: "B \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    from cat_obj_cf_comma_ObjE[OF prems c] obtain r' u' 
      where B_def: "B = [0, r', u']\<^sub>\<circ>" 
        and r': "r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
        and u': "u' : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"
      by auto
    from up[OF r' u'] obtain f 
      where f: "f : r \<mapsto>\<^bsub>\<AA>\<^esub> r'" 
        and u'_def: "u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
        and up': "\<lbrakk> f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r'; u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr> \<rbrakk> \<Longrightarrow>
          f' = f"
      for f'
      by auto
    from u'_def f u have [symmetric, cat_cs_simps]: "u' = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u"
      by (cs_prems cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    define F where "F = [[0, r, u]\<^sub>\<circ>, [0, r', u']\<^sub>\<circ>, [0, f]\<^sub>\<circ>]\<^sub>\<circ>"
    show "\<exists>!f. f : [0, r, u]\<^sub>\<circ> \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<FF>\<^esub> B"
      unfolding B_def
    proof(rule ex1I)
      from c u f u' show "F : [0, r, u]\<^sub>\<circ> \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<FF>\<^esub> [0, r', u']\<^sub>\<circ>"
        unfolding F_def
        by 
          (
            cs_concl cs_shallow 
              cs_simp: cat_cs_simps cs_intro: cat_comma_cs_intros
          )
      fix F' assume prems': "F' : [0, r, u]\<^sub>\<circ> \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<FF>\<^esub> [0, r', u']\<^sub>\<circ>"
      from cat_obj_cf_comma_is_arrE[OF prems' c, simplified] obtain f' 
        where F'_def: "F' = [[0, r, u]\<^sub>\<circ>, [0, r', u']\<^sub>\<circ>, [0, f']\<^sub>\<circ>]\<^sub>\<circ>"
          and f': "f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r'"
          and [cat_cs_simps]: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u = u'"
        by auto
      from f' u have "u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from up'[OF f' this] show "F' = F" unfolding F'_def F_def by simp
    qed
  qed
qed

lemma (in is_functor) universal_arrow_fo_if_obj_terminal:
  \<comment>\<open>See Chapter III-1 in \cite{mac_lane_categories_2010}.\<close>
  assumes "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "obj_terminal (\<FF> \<^sub>C\<^sub>F\<down> c) [r, 0, u]\<^sub>\<circ>"
  shows "universal_arrow_fo \<FF> c r u"
proof-
  let ?op_\<FF>c = \<open>op_cat (\<FF> \<^sub>C\<^sub>F\<down> c)\<close> 
    and ?c_op_\<FF> = \<open>c \<down>\<^sub>C\<^sub>F (op_cf \<FF>)\<close>
    and ?iso = \<open>op_cf_obj_comma \<FF> c\<close> 
  from cat_cf_obj_comma_ObjD[OF obj_terminalD(1)[OF assms(2)] assms(1)] 
  have r: "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and u: "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
    by simp_all
  interpret \<FF>c: is_iso_functor \<alpha> ?op_\<FF>c ?c_op_\<FF> ?iso
    by (rule op_cf_obj_comma_is_iso_functor[OF assms(1)])
  have iso_cocontinuous: "is_cf_cocontinuous \<alpha> ?iso"
    by
      (
        rule is_iso_functor.iso_cf_is_cf_cocontinuous[
          OF \<FF>c.is_iso_functor_axioms
          ]
      )
  have iso_preserves: "cf_preserves_colimits \<alpha> ?iso (cf_0 ?op_\<FF>c)"
    by 
      (
        rule is_cf_cocontinuousD
          [
            OF 
              iso_cocontinuous 
              cf_0_is_functor[OF \<FF>c.HomDom.category_axioms] 
              \<FF>c.is_functor_axioms
          ]
      )
  from category.cat_obj_initial_is_cat_obj_empty_initial[
      OF \<FF>c.HomDom.category_axioms op_cat_obj_initial[THEN iffD2, OF assms(2)]
      ]
  interpret ntcf_0_op_\<FF>c: 
    is_cat_obj_empty_initial \<alpha> ?op_\<FF>c \<open>[r, 0, u]\<^sub>\<circ>\<close> \<open>ntcf_0 ?op_\<FF>c\<close>
    by simp
  have "cf_0 ?op_\<FF>c : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> ?op_\<FF>c" 
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  from 
    cf_preserves_colimitsD
      [
        OF 
          iso_preserves 
          ntcf_0_op_\<FF>c.is_cat_colimit_axioms
          this
          \<FF>c.is_functor_axioms
      ]
    assms(1) r u
  have "ntcf_0 ?c_op_\<FF> :
    cf_0 ?c_op_\<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m [0, r, u]\<^sub>\<circ> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> ?c_op_\<FF>"
    by
      (
        cs_prems cs_shallow
          cs_simp: cat_cs_simps cat_comma_cs_simps 
          cs_intro: cat_cs_intros cat_comma_cs_intros
      )
  then have obj_initial_ru: "obj_initial ?c_op_\<FF> [0, r, u]\<^sub>\<circ>"
    by
      (
        rule is_cat_obj_empty_initial.cat_oei_obj_initial[
          OF is_cat_obj_empty_initialI
          ]
      )
  from assms(1) have "c \<in>\<^sub>\<circ> op_cat \<BB>\<lparr>Obj\<rparr>" 
    by (cs_concl cs_shallow cs_intro: cat_op_intros)
  from
    is_functor.universal_arrow_of_if_obj_initial[
      OF is_functor_op this obj_initial_ru
      ] 
  have "universal_arrow_of (op_cf \<FF>) c r u"
    by simp
  then show ?thesis unfolding cat_op_simps .
qed

lemma (in is_functor) obj_terminal_if_universal_arrow_fo:
  \<comment>\<open>See Chapter III-1 in \cite{mac_lane_categories_2010}.\<close>
  assumes "universal_arrow_fo \<FF> c r u" 
  shows "obj_terminal (\<FF> \<^sub>C\<^sub>F\<down> c) [r, 0, u]\<^sub>\<circ>"
proof-
  let ?op_\<FF>c = \<open>op_cat (\<FF> \<^sub>C\<^sub>F\<down> c)\<close> 
    and ?c_op_\<FF> = \<open>c \<down>\<^sub>C\<^sub>F (op_cf \<FF>)\<close>
    and ?iso = \<open>inv_cf (op_cf_obj_comma \<FF> c)\<close>
  from universal_arrow_foD[OF assms] have r: "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and u: "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
    by auto
  then have c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by auto
  from u have c_op_\<FF>: "category \<alpha> ?c_op_\<FF>"
    by 
      (
        cs_concl cs_shallow cs_intro: 
          cat_cs_intros cat_comma_cs_intros cat_op_intros
      )
  interpret \<FF>c: is_iso_functor \<alpha> ?op_\<FF>c ?c_op_\<FF> \<open>op_cf_obj_comma \<FF> c\<close>
    by (rule op_cf_obj_comma_is_iso_functor[OF c])
  interpret inv_\<FF>c: is_iso_functor \<alpha> ?c_op_\<FF> ?op_\<FF>c ?iso
    by (cs_concl cs_shallow cs_intro: cf_cs_intros)
  have iso_cocontinuous: "is_cf_cocontinuous \<alpha> ?iso"
    by
      (
        rule is_iso_functor.iso_cf_is_cf_cocontinuous[
          OF inv_\<FF>c.is_iso_functor_axioms
          ]
      )
  have iso_preserves: "cf_preserves_colimits \<alpha> ?iso (cf_0 ?c_op_\<FF>)"
    by 
      (
        rule is_cf_cocontinuousD
          [
            OF
              iso_cocontinuous
              cf_0_is_functor[OF \<FF>c.HomCod.category_axioms] 
              inv_\<FF>c.is_functor_axioms
          ]
      )
  from assms have "universal_arrow_of (op_cf \<FF>) c r u" unfolding cat_op_simps.
  from is_cat_obj_empty_initialD
    [
      OF category.cat_obj_initial_is_cat_obj_empty_initial
        [
          OF c_op_\<FF> is_functor.obj_initial_if_universal_arrow_of[
            OF is_functor_op this
            ]
        ]
    ]
  have ntcf_0_c_op_\<FF>: "ntcf_0 ?c_op_\<FF> :
    cf_0 ?c_op_\<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m [0, r, u]\<^sub>\<circ> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> ?c_op_\<FF>".
  have cf_0_c_op_\<FF>: "cf_0 ?c_op_\<FF> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> ?c_op_\<FF>"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  from 
    cf_preserves_colimitsD[
      OF iso_preserves ntcf_0_c_op_\<FF> cf_0_c_op_\<FF> inv_\<FF>c.is_functor_axioms
      ]
    r u
  have "ntcf_0 ?op_\<FF>c : cf_0 ?op_\<FF>c >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m [r, 0, u]\<^sub>\<circ> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> ?op_\<FF>c"
    by 
      (
        cs_prems cs_shallow
          cs_simp: cat_cs_simps cat_comma_cs_simps \<FF>c.inv_cf_ObjMap_app 
          cs_intro: cat_cs_intros cat_comma_cs_intros cat_op_intros
      )
  from 
    is_cat_obj_empty_initial.cat_oei_obj_initial[
      OF is_cat_obj_empty_initialI[OF this]
      ]  
  show "obj_terminal (\<FF> \<^sub>C\<^sub>F\<down> c) [r, 0, u]\<^sub>\<circ>" 
    unfolding op_cat_obj_initial[symmetric].
qed



subsection\<open>
A projection for a comma category constructed from a functor and an object
creates small limits
\<close>

text\<open>See Chapter V-6 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

lemma cf_obj_cf_comma_proj_creates_limits:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<XX>"
    and "is_tm_cf_continuous \<alpha> \<GG>"
    and "x \<in>\<^sub>\<circ> \<XX>\<lparr>Obj\<rparr>"
    and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
  shows "cf_creates_limits \<alpha> (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG>) \<FF>"
proof(intro cf_creates_limitsI conjI allI impI)

  interpret \<GG>: is_functor \<alpha> \<AA> \<XX> \<GG> by (rule assms(1))
  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<open>x \<down>\<^sub>C\<^sub>F \<GG>\<close> \<FF> by (rule assms(4))
  interpret x\<GG>: is_functor \<alpha> \<open>x \<down>\<^sub>C\<^sub>F \<GG>\<close> \<AA> \<open>x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG>\<close>
    by (rule \<GG>.cf_obj_cf_comma_proj_is_functor[OF assms(3)])

  show "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>" by (rule \<FF>.is_functor_axioms)
  show "x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> : x \<down>\<^sub>C\<^sub>F \<GG> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" by (rule x\<GG>.is_functor_axioms)

  define \<psi> :: V
    where "\<psi> =
      [
        (\<lambda>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>),
        cf_const \<JJ> \<XX> x,
        \<GG> \<circ>\<^sub>C\<^sub>F (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>),
        \<JJ>,
        \<XX>
      ]\<^sub>\<circ>"
  
  have \<psi>_components: 
    "\<psi>\<lparr>NTMap\<rparr> = (\<lambda>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>)"
    "\<psi>\<lparr>NTDom\<rparr> = cf_const \<JJ> \<XX> x"
    "\<psi>\<lparr>NTCod\<rparr> = \<GG> \<circ>\<^sub>C\<^sub>F (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>)"
    "\<psi>\<lparr>NTDGDom\<rparr> = \<JJ>"
    "\<psi>\<lparr>NTDGCod\<rparr> = \<XX>"
    unfolding \<psi>_def nt_field_simps by (simp_all add: nat_omega_simps)

  have \<psi>_NTMap_app: "\<psi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f"
    if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" and "\<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = [a, b, f]\<^sub>\<circ>" for a b f j
    using that unfolding \<psi>_components by (simp add: nat_omega_simps)

  interpret \<psi>: is_cat_cone \<alpha> x \<JJ> \<XX> \<open>\<GG> \<circ>\<^sub>C\<^sub>F (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<close> \<psi>
  proof(intro is_cat_coneI is_ntcfI')
    show "vfsequence \<psi>" unfolding \<psi>_def by clarsimp
    show "vcard \<psi> = 5\<^sub>\<nat>" unfolding \<psi>_def by (simp add: nat_omega_simps)
    show "\<psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : 
      cf_const \<JJ> \<XX> x\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<XX>\<^esub> (\<GG> \<circ>\<^sub>C\<^sub>F (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>))\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for a
    proof-
      from that have "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> x \<down>\<^sub>C\<^sub>F \<GG>\<lparr>Obj\<rparr>"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      from \<GG>.cat_obj_cf_comma_ObjE[OF this assms(3)] obtain c g 
        where \<FF>a_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = [0, c, g]\<^sub>\<circ>"
          and c: "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
          and g: "g : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
        by auto
      from c g show ?thesis
        using that 
        by
          (
            cs_concl
              cs_simp: cat_comma_cs_simps cat_cs_simps \<FF>a_def \<psi>_NTMap_app 
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed
    show 
      "\<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> cf_const \<JJ> \<XX> x\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        (\<GG> \<circ>\<^sub>C\<^sub>F (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>))\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> \<psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" for a b f
    proof-
      from that have \<FF>f: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      from \<GG>.cat_obj_cf_comma_is_arrE[OF this assms(3)] obtain c h c' h' k 
        where \<FF>f_def: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = [[0, c, h]\<^sub>\<circ>, [0, c', h']\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
          and \<FF>a_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = [0, c, h]\<^sub>\<circ>"
          and \<FF>b_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = [0, c', h']\<^sub>\<circ>"
          and k: "k : c \<mapsto>\<^bsub>\<AA>\<^esub> c'"
          and h: "h : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
          and h': "h' : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr>" 
          and [cat_cs_simps]: "\<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> h = h'" 
        by metis
      from \<FF>f k h h' that show ?thesis
        unfolding \<FF>f_def \<FF>a_def \<FF>b_def
        by (*slow*)
          (
            cs_concl
              cs_simp:
                cat_cs_simps cat_comma_cs_simps
                \<FF>f_def \<FF>a_def \<FF>b_def \<psi>_NTMap_app
              cs_intro: cat_cs_intros
          )
    qed
  qed (auto simp: assms(3) \<psi>_components intro: cat_cs_intros)

  fix \<tau> b assume prems: "\<tau> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  interpret \<tau>: is_cat_limit \<alpha> \<JJ> \<AA> \<open>x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> b \<tau> by (rule prems)

  note x\<GG>_\<FF> = cf_comp_cf_obj_cf_comma_proj_is_tm_functor[OF assms(1,4,3)]
  have "cf_preserves_limits \<alpha> \<GG> (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>)"
    by (rule is_tm_cf_continuousD [OF assms(2) x\<GG>_\<FF> assms(1)])
  then have \<GG>\<tau>: "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau> :
    \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>) : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<XX>"
    by 
      (
        rule cf_preserves_limitsD[
          OF _ prems(1) is_tm_functorD(1)[OF x\<GG>_\<FF>] assms(1)
          ]
      )

  from is_cat_limit.cat_lim_unique_cone'[OF \<GG>\<tau> \<psi>.is_cat_cone_axioms] obtain f 
    where f: "f : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and \<psi>_f: "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow>
        \<psi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau>)\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f"
      and f_unique:
        "\<lbrakk>
          f' : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>; 
          \<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> \<psi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau>)\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f'
         \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis

  define \<sigma> :: V 
    where "\<sigma> =
      [
        (
          \<lambda>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>.
            [
              [0, b, f]\<^sub>\<circ>,
              [0, (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>, \<psi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>]\<^sub>\<circ>,
              [0, \<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>]\<^sub>\<circ>
            ]\<^sub>\<circ>
        ),
        cf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) [0, b, f]\<^sub>\<circ>,
        \<FF>,
        \<JJ>,
        x \<down>\<^sub>C\<^sub>F \<GG>
      ]\<^sub>\<circ>"

  have \<sigma>_components: "\<sigma>\<lparr>NTMap\<rparr> =
      (
        \<lambda>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>.
          [
            [0, b, f]\<^sub>\<circ>,
            [0, (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>, \<psi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>]\<^sub>\<circ>,
            [0, \<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>]\<^sub>\<circ>
          ]\<^sub>\<circ>
      )"
    and [cat_cs_simps]: "\<sigma>\<lparr>NTDom\<rparr> = cf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) [0, b, f]\<^sub>\<circ>"
    and [cat_cs_simps]: "\<sigma>\<lparr>NTCod\<rparr> = \<FF>"
    and [cat_cs_simps]: "\<sigma>\<lparr>NTDGDom\<rparr> = \<JJ>"
    and [cat_cs_simps]: "\<sigma>\<lparr>NTDGCod\<rparr> = x \<down>\<^sub>C\<^sub>F \<GG>"
    unfolding \<sigma>_def nt_field_simps by (simp_all add: nat_omega_simps)

  have \<sigma>_NTMap_app: "\<sigma>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> =
    [
      [0, b, f]\<^sub>\<circ>,
      [0, (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>, \<psi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>]\<^sub>\<circ>,
      [0, \<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>]\<^sub>\<circ>
    ]\<^sub>\<circ>"
    if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    using that unfolding \<sigma>_components by simp

  interpret \<sigma>: is_cat_cone \<alpha> \<open>[0, b, f]\<^sub>\<circ>\<close> \<JJ> \<open>x \<down>\<^sub>C\<^sub>F \<GG>\<close> \<FF> \<sigma> 
  proof(intro is_cat_coneI is_ntcfI')
    show "vfsequence \<sigma>" unfolding \<sigma>_def by auto
    show "vcard \<sigma> = 5\<^sub>\<nat>" unfolding \<sigma>_def by (simp add: nat_omega_simps)
    from f show "cf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) [0, b, f]\<^sub>\<circ> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
      by
        (
          cs_concl cs_intro: 
            cat_cs_intros cat_lim_cs_intros cat_comma_cs_intros
        )
    show "vsv (\<sigma>\<lparr>NTMap\<rparr>)" unfolding \<sigma>_components by auto
    show "\<D>\<^sub>\<circ> (\<sigma>\<lparr>NTMap\<rparr>) = \<JJ>\<lparr>Obj\<rparr>" unfolding \<sigma>_components by auto
    from assms(3) show "\<sigma>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
      cf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) [0, b, f]\<^sub>\<circ>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for a
    proof-
      from that have \<FF>a: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> x \<down>\<^sub>C\<^sub>F \<GG>\<lparr>Obj\<rparr>"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      from \<GG>.cat_obj_cf_comma_ObjE[OF this assms(3)] obtain c g 
        where \<FF>a_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = [0, c, g]\<^sub>\<circ>"
          and c: "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
          and g: "g : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
        by auto
      from \<psi>_f[OF that] that c f g \<FF>a have [symmetric, cat_cs_simps]: 
        "g = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<tau>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f"
        by
          (
            cs_prems cs_shallow
              cs_simp: cat_cs_simps \<psi>_NTMap_app \<FF>a_def cs_intro: cat_cs_intros
          )
      from that c f g \<FF>a show ?thesis
        unfolding \<FF>a_def
        by
          (
            cs_concl 
              cs_simp:
                cat_comma_cs_simps cat_cs_simps
                \<psi>_NTMap_app \<sigma>_NTMap_app \<FF>a_def
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed
    show
      "\<sigma>\<lparr>NTMap\<rparr>\<lparr>d\<rparr> \<circ>\<^sub>A\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> cf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) [0, b, f]\<^sub>\<circ>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> =
        \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
      if "g : c \<mapsto>\<^bsub>\<JJ>\<^esub> d" for c d g 
    proof-
      from that have \<FF>g: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      from \<GG>.cat_obj_cf_comma_is_arrE[OF this assms(3)] obtain e h e' h' k 
        where \<FF>g_def: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = [[0, e, h]\<^sub>\<circ>, [0, e', h']\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
          and \<FF>c_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> = [0, e, h]\<^sub>\<circ>"
          and \<FF>d_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr> = [0, e', h']\<^sub>\<circ>"
          and k: "k : e \<mapsto>\<^bsub>\<AA>\<^esub> e'"
          and h: "h : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>e\<rparr>"
          and h': "h' : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>e'\<rparr>" 
          and [cat_cs_simps]: "\<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> h = h'" 
        by metis
      from that have "c \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" by auto
      from \<psi>_f[OF this] that k f h have [symmetric, cat_cs_simps]: 
        "h = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<tau>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f"
        by
          (
            cs_prems 
              cs_simp: cat_cs_simps \<psi>_NTMap_app \<FF>c_def cs_intro: cat_cs_intros
          )
      from that have "d \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"by auto
      from \<psi>_f[OF this] that k f h' have [symmetric, cat_cs_simps]: 
        "h' = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<tau>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f"
        by
          (
            cs_prems cs_shallow
              cs_simp: cat_cs_simps \<psi>_NTMap_app \<FF>d_def cs_intro: cat_cs_intros
          )
      note \<tau>.cat_cone_Comp_commute[cat_cs_simps del]
      from \<tau>.ntcf_Comp_commute[OF that] that assms(3) k h h' 
      have [symmetric, cat_cs_simps]: "\<tau>\<lparr>NTMap\<rparr>\<lparr>d\<rparr> = k \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<tau>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
        by
          (
            cs_prems
              cs_simp: cat_comma_cs_simps cat_cs_simps \<FF>g_def \<FF>c_def \<FF>d_def
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
      from that f \<FF>g k h h' show ?thesis
        unfolding \<FF>g_def \<FF>c_def \<FF>d_def
        by
          (
            cs_concl
              cs_simp:
                cat_comma_cs_simps cat_cs_simps
                \<psi>_NTMap_app \<sigma>_NTMap_app \<FF>g_def \<FF>c_def \<FF>d_def
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed
  qed
    (
      use f in 
        \<open>
          cs_concl cs_shallow 
            cs_intro: cat_cs_intros cat_lim_cs_intros cat_comma_cs_intros 
            cs_simp: cat_cs_simps
        \<close>
    )+

  have \<tau>\<sigma>: "\<tau> = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>"
  proof(rule ntcf_eqI)
    show "\<tau> : cf_const \<JJ> \<AA> b \<mapsto>\<^sub>C\<^sub>F x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (rule \<tau>.is_ntcf_axioms)
    from f show "x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> : 
      cf_const \<JJ> \<AA> b \<mapsto>\<^sub>C\<^sub>F x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cat_comma_cs_simps 
            cs_intro: cat_lim_cs_intros cat_cs_intros cat_comma_cs_intros
        )
    have dom_lhs: "\<D>\<^sub>\<circ> (\<tau>\<lparr>NTMap\<rparr>) = \<JJ>\<lparr>Obj\<rparr>"
      by (cs_concl cs_shallow cs_simp: cat_cs_simps)
    have dom_rhs: "\<D>\<^sub>\<circ> ((x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>)\<lparr>NTMap\<rparr>) = \<JJ>\<lparr>Obj\<rparr>"
      by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "\<tau>\<lparr>NTMap\<rparr> = (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume prems': "a \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
      then have "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> x \<down>\<^sub>C\<^sub>F \<GG>\<lparr>Obj\<rparr>"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      from \<GG>.cat_obj_cf_comma_ObjE[OF this assms(3)] obtain c g 
        where \<FF>a_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = [0, c, g]\<^sub>\<circ>"
          and c: "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
          and g: "g : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
        by auto
      from \<psi>_f[OF prems'] prems' f g have [symmetric, cat_cs_simps]: 
        "g = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<tau>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f"
        by
          (
            cs_prems cs_shallow
              cs_simp: cat_cs_simps \<psi>_NTMap_app \<FF>a_def cs_intro: cat_cs_intros
          )
      with assms(3) prems' c g f show 
        "\<tau>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by
          (
            cs_concl cs_shallow
              cs_simp:
                cat_comma_cs_simps cat_cs_simps
                \<FF>a_def \<psi>_NTMap_app \<sigma>_NTMap_app
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed (simp_all add: \<tau>.ntcf_NTMap_vsv cat_cs_intros)
  qed simp_all

  from f have b_def: "b = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG>\<lparr>ObjMap\<rparr>\<lparr>0, b, f\<rparr>\<^sub>\<bullet>"
    by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_cs_intros)

  show \<sigma>a_unique: "\<exists>!\<sigma>a. \<exists>\<sigma> a.
    \<sigma>a = \<langle>\<sigma>, a\<rangle> \<and>
    \<sigma> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG> \<and>
    \<tau> = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma> \<and> b = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  proof
    (
      intro ex1I[where a=\<open>\<langle>\<sigma>, [0, b, f]\<^sub>\<circ>\<rangle>\<close>] exI conjI, simp only:; 
      (elim exE conjE)?
    )

    show "\<sigma> : [0, b, f]\<^sub>\<circ> <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
      by (rule \<sigma>.is_cat_cone_axioms)
    show "\<tau> = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>" by (rule \<tau>\<sigma>)
    show "b = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG>\<lparr>ObjMap\<rparr> \<lparr>0, b, f\<rparr>\<^sub>\<bullet>" by (rule b_def)

    fix \<sigma>a \<sigma>' a assume prems':
      "\<sigma>a = \<langle>\<sigma>', a\<rangle>"
      "\<sigma>' : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
      "\<tau> = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>'"
      "b = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" 
    interpret \<sigma>': is_cat_cone \<alpha> a \<JJ> \<open>x \<down>\<^sub>C\<^sub>F \<GG>\<close> \<FF> \<sigma>' by (rule prems'(2))

    from \<GG>.cat_obj_cf_comma_ObjE[OF \<sigma>'.cat_cone_obj assms(3)] obtain c g 
      where a_def'': "a = [0, c, g]\<^sub>\<circ>"
        and c': "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
        and g': "g : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
      by auto
    from prems'(4) c' g' assms(3) have bc: "b = c"
      by
        (
          cs_prems cs_shallow
            cs_simp: cat_comma_cs_simps a_def'' cs_intro: cat_comma_cs_intros
        )
    with a_def'' c' g' have a_def': "a = [0, b, g]\<^sub>\<circ>"
      and b: "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      and g: "g : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by auto

    from prems'(3) have \<tau>_eq_x\<GG>_\<sigma>': 
      "\<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>')\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" for j
      by simp

    have "\<psi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau>)\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> g"
      if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    proof-
      from that have \<sigma>'_j: "\<sigma>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : [0, b, g]\<^sub>\<circ> \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
        by 
          (
            cs_concl cs_shallow 
              cs_simp: cat_cs_simps a_def'[symmetric] cs_intro: cat_cs_intros
          )
      from \<GG>.cat_obj_cf_comma_is_arrE[OF this]  obtain e h k 
        where \<sigma>'_j_def: "\<sigma>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = [[0, b, g]\<^sub>\<circ>, [0, e, h]\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
          and \<FF>j_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = [0, e, h]\<^sub>\<circ>"
          and k: "k : b \<mapsto>\<^bsub>\<AA>\<^esub> e"
          and h: "h : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>e\<rparr>" 
          and [cat_cs_simps]: "\<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> g = h" 
        by (metis \<GG>.cat_obj_cf_comma_is_arrD(4,7) \<sigma>'_j assms(3))
      from that \<sigma>'_j show ?thesis
        unfolding \<sigma>'_j_def
        by
          (
            cs_concl cs_shallow 
              cs_simp:
                cat_cs_simps cat_comma_cs_simps
                \<sigma>'_j_def \<psi>_NTMap_app \<FF>j_def prems'(3)
              cs_intro: cat_cs_intros
          )
    qed
    from f_unique[OF g this] have gf: "g = f".
    with a_def' have a_def: "a = [0, b, f]\<^sub>\<circ>" by simp

    have \<sigma>\<sigma>': "\<sigma> = \<sigma>'"
    proof(rule ntcf_eqI)
      show "\<sigma> : cf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) [0, b, f]\<^sub>\<circ> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      then have dom_lhs: "\<D>\<^sub>\<circ> (\<sigma>\<lparr>NTMap\<rparr>) = \<JJ>\<lparr>Obj\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps)
      show "\<sigma>' : cf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) [0, b, f]\<^sub>\<circ> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
        by (cs_concl cs_shallow cs_simp: a_def cs_intro: cat_cs_intros)
      then have dom_rhs: "\<D>\<^sub>\<circ> (\<sigma>'\<lparr>NTMap\<rparr>) = \<JJ>\<lparr>Obj\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps)
      show "\<sigma>\<lparr>NTMap\<rparr> = \<sigma>'\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
        fix j assume prems'': "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
        then have \<sigma>'_j: "\<sigma>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : [0, b, f]\<^sub>\<circ> \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
          by 
            (
              cs_concl cs_shallow
                cs_simp: cat_cs_simps a_def'[symmetric] gf[symmetric] 
                cs_intro: cat_cs_intros
            )
        from \<GG>.cat_obj_cf_comma_is_arrE[OF this] obtain e h k 
          where \<sigma>'_j_def: "\<sigma>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = [[0, b, f]\<^sub>\<circ>, [0, e, h]\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
            and \<FF>j_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = [0, e, h]\<^sub>\<circ>"
            and k: "k : b \<mapsto>\<^bsub>\<AA>\<^esub> e"
            and h: "h : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>e\<rparr>" 
            and [cat_cs_simps]: "\<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f = h" 
          by (metis \<GG>.cat_obj_cf_comma_is_arrD(4,7) \<sigma>'_j assms(3))
        from prems'' k h assms(3) f h show "\<sigma>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<sigma>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
          by
            (
              cs_concl cs_shallow
                cs_simp:
                  cat_cs_simps cat_comma_cs_simps
                  \<tau>_eq_x\<GG>_\<sigma>' \<psi>_NTMap_app \<sigma>_NTMap_app \<FF>j_def \<sigma>'_j_def
                cs_intro: cat_cs_intros cat_comma_cs_intros
            )
      qed (cs_concl cs_shallow cs_intro: V_cs_intros)
    qed simp_all
    show "\<sigma>a = \<langle>\<sigma>, [[]\<^sub>\<circ>, b, f]\<^sub>\<circ>\<rangle>" unfolding prems'(1) \<sigma>\<sigma>' a_def by simp
  qed

  show "\<sigma>' : a' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
    if "\<sigma>' : a' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
      and "\<tau> = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>'"
      and "b = x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
    for \<sigma>' a'
  proof(rule is_cat_limitI)

    interpret \<sigma>': is_cat_cone \<alpha> a' \<JJ> \<open>x \<down>\<^sub>C\<^sub>F \<GG>\<close> \<FF> \<sigma>' by (rule that(1))

    from \<sigma>.is_cat_cone_axioms \<tau>\<sigma> b_def that \<sigma>a_unique have 
      "\<langle>\<sigma>', a'\<rangle> = \<langle>\<sigma>, [0, b, f]\<^sub>\<circ>\<rangle>" 
      by metis
    then have \<sigma>'_def: "\<sigma>' = \<sigma>" and a'_def: "a' = [0, b, f]\<^sub>\<circ>" by simp_all

    show "\<sigma>' : a' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
      by (rule \<sigma>'.is_cat_cone_axioms)

    fix \<sigma>'' a'' assume prems: "\<sigma>'' : a'' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
    then interpret \<sigma>'': is_cat_cone \<alpha> a'' \<JJ> \<open>x \<down>\<^sub>C\<^sub>F \<GG>\<close> \<FF> \<sigma>'' .
    from \<GG>.cat_obj_cf_comma_ObjE[OF \<sigma>''.cat_cone_obj assms(3)] obtain b' f' 
      where a''_def: "a'' = [0, b', f']\<^sub>\<circ>"
        and b': "b' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
        and f': "f' : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      by auto
    from b' f' have x\<GG>_A': "x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG>\<lparr>ObjMap\<rparr>\<lparr>a''\<rparr> = b'"
      unfolding a''_def
      by
        (
          cs_concl cs_shallow 
            cs_simp: cat_comma_cs_simps cs_intro: cat_comma_cs_intros
        )
    
    from \<tau>.cat_lim_unique_cone'[
        OF cf_ntcf_comp_cf_cat_cone[OF prems x\<GG>.is_functor_axioms],
        unfolded x\<GG>_A'
        ]
    obtain h where h: "h : b' \<mapsto>\<^bsub>\<AA>\<^esub> b"
      and x\<GG>_\<sigma>''_app: "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow>
        (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>'')\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> h"
      and h_unique:
        "\<lbrakk>
          h' : b' \<mapsto>\<^bsub>\<AA>\<^esub> b;
          \<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow>
            (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>'')\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> h'
         \<rbrakk> \<Longrightarrow> h' = h"
      for h'
      by metis

    define F where "F = [a'', a', [0, h]\<^sub>\<circ>]\<^sub>\<circ>"

    show "\<exists>!F'.
      F' : a'' \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> a' \<and> \<sigma>'' = \<sigma>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) F'"
      unfolding a''_def a'_def \<sigma>'_def
    proof(intro ex1I conjI; (elim conjE)?)
      from f' h have \<GG>h_f': "\<GG>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f' : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros )
      have "\<psi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<tau>)\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> (\<GG>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f')"
        if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
      proof-
        from that have \<sigma>''_j: 
          "\<sigma>''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : [0, b', f']\<^sub>\<circ> \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
          by 
            (
              cs_concl cs_shallow 
                cs_simp: cat_cs_simps a''_def[symmetric] 
                cs_intro: cat_cs_intros
            )
        from \<GG>.cat_obj_cf_comma_is_arrE[OF this] obtain e h' k 
          where \<sigma>''_j_def: "\<sigma>''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = [[0, b', f']\<^sub>\<circ>, [0, e, h']\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
            and \<FF>j_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = [0, e, h']\<^sub>\<circ>"
            and k: "k : b' \<mapsto>\<^bsub>\<AA>\<^esub> e"
            and [cat_cs_simps]: "\<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f' = h'" 
          by (metis \<GG>.cat_obj_cf_comma_is_arrD(4,7) \<sigma>''_j assms(3))
        from that \<sigma>''_j have \<psi>_NTMap_j: "\<psi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> =
          (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F (x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>''))\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f'"
          unfolding \<sigma>''_j_def \<FF>j_def
          by
            (
              cs_concl cs_shallow 
                cs_simp:
                  cat_cs_simps cat_comma_cs_simps \<sigma>''_j_def \<FF>j_def \<psi>_NTMap_app
                cs_intro: cat_cs_intros
            )+
        from that h f' show ?thesis
          unfolding \<psi>_NTMap_j
          by
            (
              cs_concl cs_shallow
                cs_simp:
                  cat_cs_simps
                  is_ntcf.cf_ntcf_comp_NTMap_app 
                  x\<GG>_\<sigma>''_app[OF that]
                cs_intro: cat_cs_intros
            )
      qed

      from f_unique[OF \<GG>h_f' this] have [cat_cs_simps]: 
        "\<GG>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f' = f".

      from assms(3) h f' f show F: "F : [0, b', f']\<^sub>\<circ> \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> [0, b, f]\<^sub>\<circ>"
        unfolding F_def a''_def a'_def 
        by
          (
            cs_concl cs_shallow
              cs_simp: cat_cs_simps cs_intro: cat_comma_cs_intros
          )

      show "\<sigma>'' = \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) F"
      proof(rule ntcf_eqI)
        show "\<sigma>'' : cf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) a'' \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
          by (rule \<sigma>''.is_ntcf_axioms)
        then have dom_lhs: "\<D>\<^sub>\<circ> (\<sigma>''\<lparr>NTMap\<rparr>) = \<JJ>\<lparr>Obj\<rparr>"
          by (cs_concl cs_shallow cs_simp: cat_cs_simps)
        from F show "\<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) F : 
          cf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) a'' \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> x \<down>\<^sub>C\<^sub>F \<GG>"
          unfolding a''_def by (cs_concl cs_shallow cs_intro: cat_cs_intros)
        then have dom_rhs: 
          "\<D>\<^sub>\<circ> ((\<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) F)\<lparr>NTMap\<rparr>) = \<JJ>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps)
        show "\<sigma>''\<lparr>NTMap\<rparr> = (\<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) F)\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix j assume prems': "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
          then have \<sigma>''_j: 
            "\<sigma>''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : [0, b', f']\<^sub>\<circ> \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
            by
              (
                cs_concl cs_shallow
                  cs_simp: cat_cs_simps a''_def[symmetric]
                  cs_intro: cat_cs_intros
              )
          from \<GG>.cat_obj_cf_comma_is_arrE[OF this] obtain e h' k 
            where \<sigma>''_j_def: "\<sigma>''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = [[0, b', f']\<^sub>\<circ>, [0, e, h']\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
              and \<FF>j_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = [0, e, h']\<^sub>\<circ>"
              and k: "k : b' \<mapsto>\<^bsub>\<AA>\<^esub> e"
              and h': "h' : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>e\<rparr>" 
              and [cat_cs_simps]: "\<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f' = h'" 
            by (metis \<GG>.cat_obj_cf_comma_is_arrD(4,7) \<sigma>''_j assms(3))
          from assms(3) prems' F k h' h f f' show  
            "\<sigma>''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) F)\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
            by (*very slow*)
              (
                cs_concl 
                  cs_simp:
                    cat_cs_simps cat_comma_cs_simps 
                    \<sigma>''_j_def x\<GG>_\<sigma>''_app[OF prems', symmetric] 
                    \<sigma>_NTMap_app F_def \<FF>j_def a''_def a'_def 
                  cs_intro: cat_cs_intros cat_comma_cs_intros 
                  cs_simp: \<psi>_f \<psi>_NTMap_app
              )
        qed (cs_concl cs_intro: V_cs_intros cat_cs_intros)+
      qed simp_all
      fix F' assume prems':
        "F' : [0, b', f']\<^sub>\<circ> \<mapsto>\<^bsub>x \<down>\<^sub>C\<^sub>F \<GG>\<^esub> [0, b, f]\<^sub>\<circ>"
        "\<sigma>'' = \<sigma> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> (x \<down>\<^sub>C\<^sub>F \<GG>) F'"
      from \<GG>.cat_obj_cf_comma_is_arrE[OF prems'(1) assms(3), simplified] 
      obtain k
        where F'_def: "F' = [[0, b', f']\<^sub>\<circ>, [0, b, f]\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
          and k: "k : b' \<mapsto>\<^bsub>\<AA>\<^esub> b"
          and [cat_cs_simps]: "\<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<XX>\<^esub> f' = f" 
        by metis
      have "k = h"
      proof(rule h_unique[OF k])
        fix j assume prems'': "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
        then have "\<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> \<in>\<^sub>\<circ> x \<down>\<^sub>C\<^sub>F \<GG>\<lparr>Obj\<rparr>"
          by (cs_concl cs_shallow cs_intro: cat_cs_intros)
        from \<GG>.cat_obj_cf_comma_ObjE[OF this assms(3)] obtain c g 
          where \<FF>j_def: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = [0, c, g]\<^sub>\<circ>"
            and c: "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
            and g: "g : x \<mapsto>\<^bsub>\<XX>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
          by auto
        from prems'' prems'(1) assms(3) c g f show 
          "(x \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<sigma>'')\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<tau>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> k"
          unfolding prems'(2) \<tau>\<sigma> F'_def 
          by (*very slow*)
            (
              cs_concl
                cs_simp: cat_comma_cs_simps cat_cs_simps
                cs_intro: cat_cs_intros cat_comma_cs_intros
                cs_simp: \<psi>_f \<sigma>_NTMap_app \<FF>j_def
            )
      qed
      then show "F' = F" unfolding F'_def F_def a''_def a'_def by simp
    qed

  qed

qed

text\<open>\newpage\<close>

end