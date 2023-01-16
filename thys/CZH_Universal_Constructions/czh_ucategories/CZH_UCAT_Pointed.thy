(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Pointed arrows and natural transformations\<close>
theory CZH_UCAT_Pointed
  imports 
    CZH_Elementary_Categories.CZH_ECAT_NTCF
    CZH_Elementary_Categories.CZH_ECAT_Hom
begin



subsection\<open>Pointed arrow\<close>


text\<open>
The terminology that is used in this section deviates from convention: a 
pointed arrow is merely an arrow in \<open>Set\<close> from a singleton set to another set.
\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-2 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition ntcf_paa :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_paa \<aa> B b = [(\<lambda>a\<in>\<^sub>\<circ>set {\<aa>}. b), set {\<aa>}, B]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_paa_components:
  shows "ntcf_paa \<aa> B b\<lparr>ArrVal\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>set {\<aa>}. b)"
    and [cat_cs_simps]: "ntcf_paa \<aa> B b\<lparr>ArrDom\<rparr> = set {\<aa>}"
    and [cat_cs_simps]: "ntcf_paa \<aa> B b\<lparr>ArrCod\<rparr> = B"
  unfolding ntcf_paa_def arr_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Arrow value\<close>

mk_VLambda ntcf_paa_components(1)
  |vsv ntcf_paa_ArrVal_vsv[cat_cs_intros]|
  |vdomain ntcf_paa_ArrVal_vdomain[cat_cs_simps]|
  |app ntcf_paa_ArrVal_app[unfolded vsingleton_iff, cat_cs_simps]|


subsubsection\<open>Pointed arrow is an arrow in \<open>Set\<close>\<close>

lemma (in \<Z>) ntcf_paa_is_arr:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "a \<in>\<^sub>\<circ> A"
  shows "ntcf_paa \<aa> A a : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A"
proof(intro cat_Set_is_arrI arr_SetI cat_cs_intros, unfold cat_cs_simps)
  show "vfsequence (ntcf_paa \<aa> A a)" unfolding ntcf_paa_def by simp
  show "vcard (ntcf_paa \<aa> A a) = 3\<^sub>\<nat>"
    unfolding ntcf_paa_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (ntcf_paa \<aa> A a\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> A"
    unfolding ntcf_paa_components by (intro vrange_VLambda_vsubset assms)
qed (use assms in \<open>auto simp: cat_Set_components(1) Limit_vsingleton_in_VsetI\<close>)

lemma (in \<Z>) ntcf_paa_is_arr'[cat_cs_intros]:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "a \<in>\<^sub>\<circ> A"
    and "A' = set {\<aa>}"
    and "B' = A"
    and "\<CC>' = cat_Set \<alpha>"
  shows "ntcf_paa \<aa> A a : A' \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) unfolding assms(4-6) by (rule ntcf_paa_is_arr) 

lemmas [cat_cs_intros] = \<Z>.ntcf_paa_is_arr'


subsubsection\<open>Further properties\<close>

lemma ntcf_paa_injective[cat_cs_simps]: 
  "ntcf_paa \<aa> A b = ntcf_paa \<aa> A c \<longleftrightarrow> b = c"
proof
  assume "ntcf_paa \<aa> A b = ntcf_paa \<aa> A c"
  then have "ntcf_paa \<aa> A b\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr> = ntcf_paa \<aa> A c\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>" by simp
  then show "b = c" by (cs_prems cs_simp: cat_cs_simps)
qed simp

lemma (in \<Z>) ntcf_paa_ArrVal:
  assumes "F : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X"
  shows "ntcf_paa \<aa> X (F\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>) = F"
proof-
  interpret F: arr_Set \<alpha> F
    rewrites [cat_cs_simps]: "F\<lparr>ArrDom\<rparr> = set {\<aa>}" 
      and [cat_cs_simps]: "F\<lparr>ArrCod\<rparr> = X"
    by (auto simp: cat_Set_is_arrD[OF assms])
  from F.arr_Par_ArrDom_in_Vset have \<aa>: "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  from assms \<aa> F.arr_Par_ArrCod_in_Vset have lhs_is_arr:
    "ntcf_paa \<aa> X (F\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>) : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X"
    by
      (
        cs_concl cs_shallow 
          cs_simp: cat_Set_components(1)
          cs_intro: V_cs_intros cat_Set_cs_intros cat_cs_intros
      )
  then have dom_lhs: "\<D>\<^sub>\<circ> (ntcf_paa \<aa> X (F\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ArrVal\<rparr>) = set {\<aa>}"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)
  from assms have dom_rhs: "\<D>\<^sub>\<circ> (F\<lparr>ArrVal\<rparr>) = set {\<aa>}" 
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)
  show ?thesis
  proof(rule arr_Set_eqI)
    from lhs_is_arr assms 
    show arr_Set_lhs: "arr_Set \<alpha> (ntcf_paa \<aa> X (F\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>))" 
      and arr_Set_rhs: "arr_Set \<alpha> F"
      by (auto dest: cat_Set_is_arrD)
    show "ntcf_paa \<aa> X (F\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ArrVal\<rparr> = F\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs vsingleton_iff; (simp only:)?)
      show "ntcf_paa \<aa> X (F\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr> = F\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed (use arr_Set_lhs arr_Set_rhs in auto)
  qed (use assms in \<open>cs_concl cs_shallow cs_simp: cat_cs_simps\<close>)+
qed

lemma (in \<Z>) ntcf_paa_ArrVal'(*not cat_cs_simps*):
  assumes "F : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X" and "a = \<aa>"
  shows "ntcf_paa \<aa> X (F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>) = F"
  using assms(1) unfolding assms(2) by (rule ntcf_paa_ArrVal)

lemma (in \<Z>) ntcf_paa_Comp_right[cat_cs_simps]:
  assumes "F : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" 
    and "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "a \<in>\<^sub>\<circ> A"
  shows "F \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ntcf_paa \<aa> A a = ntcf_paa \<aa> B (F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>)"
proof-
  from assms have F_paa:
    "F \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ntcf_paa \<aa> A a : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B"
    by (cs_concl cs_intro: cat_cs_intros)
  then have dom_lhs: "\<D>\<^sub>\<circ> ((F \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ntcf_paa \<aa> A a)\<lparr>ArrVal\<rparr>) = set {\<aa>}"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)
  from assms have paa: "ntcf_paa \<aa> B (F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>) : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B"
    by (cs_concl cs_shallow cs_intro: cat_Set_cs_intros cat_cs_intros)
  then have dom_rhs: "\<D>\<^sub>\<circ> ((ntcf_paa \<aa> B (F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>))\<lparr>ArrVal\<rparr>) = set {\<aa>}"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)
  show ?thesis
  proof(rule arr_Set_eqI)
    from F_paa paa assms 
    show arr_Set_lhs: "arr_Set \<alpha> (F \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ntcf_paa \<aa> A a)" 
      and arr_Set_rhs: "arr_Set \<alpha> (ntcf_paa \<aa> B (F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>))"
      by (auto dest: cat_Set_is_arrD)
    show 
      "(F \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ntcf_paa \<aa> A a)\<lparr>ArrVal\<rparr> =
        ntcf_paa \<aa> B (F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>)\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs vsingleton_iff; (simp only:)?)
      from assms show 
        "(F \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ntcf_paa \<aa> A a)\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr> =
          ntcf_paa \<aa> B (F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_cs_intros)
    qed (use arr_Set_lhs arr_Set_rhs in auto)
  qed (use F_paa paa in \<open>cs_concl cs_shallow cs_simp: cat_cs_simps\<close>)+
qed

lemmas [cat_cs_simps] = \<Z>.ntcf_paa_Comp_right



subsection\<open>Pointed natural transformation\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-2 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition ntcf_pointed :: "V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_pointed \<alpha> \<aa> =
    [
      (
        \<lambda>x\<in>\<^sub>\<circ>cat_Set \<alpha>\<lparr>Obj\<rparr>.
          [
            (\<lambda>f\<in>\<^sub>\<circ>Hom (cat_Set \<alpha>) (set {\<aa>}) x. f\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>),
            Hom (cat_Set \<alpha>) (set {\<aa>}) x,
            x
          ]\<^sub>\<circ>
      ),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-),
      cf_id (cat_Set \<alpha>),
      cat_Set \<alpha>,
      cat_Set \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_pointed_components:
  shows "ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr> =
      (
        \<lambda>x\<in>\<^sub>\<circ>cat_Set \<alpha>\<lparr>Obj\<rparr>.
          [
            (\<lambda>f\<in>\<^sub>\<circ>Hom (cat_Set \<alpha>) (set {\<aa>}) x. f\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>),
            Hom (cat_Set \<alpha>) (set {\<aa>}) x, 
            x
          ]\<^sub>\<circ>
      )"
    and [cat_cs_simps]: "ntcf_pointed \<alpha> \<aa>\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-)"
    and [cat_cs_simps]: "ntcf_pointed \<alpha> \<aa>\<lparr>NTCod\<rparr> = cf_id (cat_Set \<alpha>)"
    and [cat_cs_simps]: "ntcf_pointed \<alpha> \<aa>\<lparr>NTDGDom\<rparr> = cat_Set \<alpha>"
    and [cat_cs_simps]: "ntcf_pointed \<alpha> \<aa>\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding ntcf_pointed_def nt_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_pointed_components(1)
  |vsv ntcf_pointed_NTMap_vsv[cat_cs_intros]|
  |vdomain ntcf_pointed_NTMap_vdomain[cat_cs_simps]|
  |app ntcf_pointed_NTMap_app'|

lemma (in \<Z>) ntcf_pointed_NTMap_app_ArrVal_app[cat_cs_simps]: 
  assumes "X \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "F : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X"
  shows "ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>\<lparr>F\<rparr> = F\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>"
  by (simp add: assms(2) ntcf_pointed_NTMap_app'[OF assms(1)] arr_Rel_components)

lemma (in \<Z>) ntcf_pointed_NTMap_app_is_iso_arr: 
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "X \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr> :
    Hom (cat_Set \<alpha>) (set {\<aa>}) X \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> X"
proof-
  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)
  note app_X = ntcf_pointed_NTMap_app'[OF assms(2)]
  show ?thesis 
  proof(intro cat_Set_is_iso_arrI cat_Set_is_arrI arr_SetI)
    show ArrVal_vsv: "vsv (ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>)"
      unfolding app_X arr_Rel_components by simp
    show "vcard (ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>) = 3\<^sub>\<nat>"
      unfolding app_X arr_Rel_components by (simp add: nat_omega_simps)
    show ArrVal_vdomain: 
      "\<D>\<^sub>\<circ> (ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>) = Hom (cat_Set \<alpha>) (set {\<aa>}) X"
      unfolding app_X arr_Rel_components by simp
    show vrange_left: 
      "\<R>\<^sub>\<circ> (ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ>
        ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrCod\<rparr>"
      unfolding app_X arr_Rel_components 
      by
        (
          auto
            simp: in_Hom_iff
            intro: cat_Set_cs_intros
            intro!: vrange_VLambda_vsubset
        )
    show "\<R>\<^sub>\<circ> (ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>) = X"
    proof(intro vsubset_antisym)
      show "X \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>)"
      proof(intro vsubsetI)
        fix x assume prems: "x \<in>\<^sub>\<circ> X"
        from assms prems have F_in_vdomain: 
          "ntcf_paa \<aa> X x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>))"
          unfolding app_X arr_Rel_components vdomain_VLambda in_Hom_iff
          by (cs_concl cs_shallow cs_intro: cat_cs_intros)
        from assms prems have x_def: 
          "x = ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>\<lparr>ntcf_paa \<aa> X x\<rparr>"
          by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        show "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>)"
           by (subst x_def) (intro vsv.vsv_vimageI2 F_in_vdomain ArrVal_vsv)
      qed
    qed (use vrange_left in \<open>simp add: app_X arr_Rel_components\<close>)
    from assms show "ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      unfolding app_X arr_Rel_components cat_Set_components(1) 
      by (intro Set.cat_Hom_in_Vset[OF _ assms(2)])
        (auto simp: cat_Set_components(1))
    show "v11 (ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>)"
    proof(intro vsv.vsv_valeq_v11I ArrVal_vsv, unfold ArrVal_vdomain in_Hom_iff)
      fix F G assume prems:
        "F : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X"
        "G : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X"
        "ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>\<lparr>F\<rparr> =
          ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>\<lparr>G\<rparr>"
      note F = cat_Set_is_arrD[OF prems(1)] and G = cat_Set_is_arrD[OF prems(2)]
      from prems(3,1,2) assms have F_ArrVal_G_ArrVal: "F\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr> = G\<lparr>ArrVal\<rparr>\<lparr>\<aa>\<rparr>"
        by (cs_prems cs_simp: cat_cs_simps)
      interpret F: arr_Set \<alpha> F + G: arr_Set \<alpha> G by (simp_all add: F G)
      show "F = G"
      proof(rule arr_Set_eqI)
        show "arr_Set \<alpha> F" "arr_Set \<alpha> G" 
          by (intro F.arr_Set_axioms G.arr_Set_axioms)+
        show "F\<lparr>ArrVal\<rparr> = G\<lparr>ArrVal\<rparr>"
          by 
            (
              rule vsv_eqI, 
              unfold F.arr_Set_ArrVal_vdomain G.arr_Set_ArrVal_vdomain F(2) G(2)
            )
            (auto simp: F_ArrVal_G_ArrVal)
      qed (simp_all add: F G)
    qed
  qed (use assms in \<open>auto simp: app_X arr_Rel_components cat_Set_components(1)\<close>)
qed

lemma (in \<Z>) ntcf_pointed_NTMap_app_is_iso_arr'[cat_cs_intros]: 
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "X \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "A' = Hom (cat_Set \<alpha>) (set {\<aa>}) X"
    and "B' = X"
    and "\<CC>' = cat_Set \<alpha>"
  shows "ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr> : A' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B'"
  using assms(1,2)
  unfolding assms(3-5)
  by (rule ntcf_pointed_NTMap_app_is_iso_arr)

lemmas [cat_cs_intros] = \<Z>.ntcf_pointed_NTMap_app_is_iso_arr'

lemmas (in \<Z>) ntcf_pointed_NTMap_app_is_arr'[cat_cs_intros] = 
  is_iso_arrD(1)[OF \<Z>.ntcf_pointed_NTMap_app_is_iso_arr']

lemmas [cat_cs_intros] = \<Z>.ntcf_pointed_NTMap_app_is_arr'


subsubsection\<open>Pointed natural transformation is a natural isomorphism\<close>

lemma (in \<Z>) ntcf_pointed_is_iso_ntcf:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "ntcf_pointed \<alpha> \<aa> :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o cf_id (cat_Set \<alpha>) :
    cat_Set \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof(intro is_iso_ntcfI is_ntcfI')

  note \<aa> = assms[unfolded cat_Set_components(1)]
  from assms have set_\<aa>: "set {\<aa>} \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    unfolding cat_Set_components by auto

  show "vfsequence (ntcf_pointed \<alpha> \<aa>)" unfolding ntcf_pointed_def by auto
  show "vcard (ntcf_pointed \<alpha> \<aa>) = 5\<^sub>\<nat>"
    unfolding ntcf_pointed_def by (auto simp: nat_omega_simps)
  from assms set_\<aa> show 
    "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-) : cat_Set \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  show "ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
    cf_id (cat_Set \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" for a
    using assms that set_\<aa>
    by 
      (
        cs_concl cs_shallow 
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros
      )
  show 
    "ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha> (set {\<aa>},-)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        cf_id (cat_Set \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    if "f : a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> b" for a b f
  proof-
    let ?pb = \<open>ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<close>
      and ?pa = \<open>ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<close>
      and ?hom = \<open>cf_hom (cat_Set \<alpha>) [cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>set {\<aa>}\<rparr>, f]\<^sub>\<circ>\<close>
    from assms set_\<aa> that have pb_hom: 
      "?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?hom : Hom (cat_Set \<alpha>) (set {\<aa>}) a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> b"
      by 
        (
          cs_concl cs_shallow 
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
    then have dom_lhs: 
      "\<D>\<^sub>\<circ> ((?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?hom)\<lparr>ArrVal\<rparr>) = Hom (cat_Set \<alpha>) (set {\<aa>}) a"
      by (cs_concl cs_shallow cs_simp: cat_cs_simps)
    from assms set_\<aa> that have f_pa:
      "f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa : Hom (cat_Set \<alpha>) (set {\<aa>}) a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> b"
      by (cs_concl cs_intro: cat_cs_intros)
    then have dom_rhs: 
      "\<D>\<^sub>\<circ> ((f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa)\<lparr>ArrVal\<rparr>) = Hom (cat_Set \<alpha>) (set {\<aa>}) a"
      by (cs_concl cs_shallow cs_simp: cat_cs_simps)
    have [cat_cs_simps]: "?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?hom = f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa"
    proof(rule arr_Set_eqI)
      from pb_hom show arr_Set_pb_hom: "arr_Set \<alpha> (?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?hom)"
        by (auto dest: cat_Set_is_arrD(1))
      from f_pa show arr_Set_f_pa: "arr_Set \<alpha> (f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa)"
        by (auto dest: cat_Set_is_arrD(1))
      show "(?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?hom)\<lparr>ArrVal\<rparr> = (f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa)\<lparr>ArrVal\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
        fix g assume "g : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> a"
        with assms \<aa> set_\<aa> that show 
          "(?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?hom)\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> = (f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa)\<lparr>ArrVal\<rparr>\<lparr>g\<rparr>"
          by
            (
              cs_concl cs_shallow
                cs_simp: V_cs_simps cat_cs_simps 
                cs_intro:
                  V_cs_intros cat_cs_intros cat_op_intros cat_prod_cs_intros
            )
      qed (use arr_Set_pb_hom arr_Set_f_pa in auto)
    qed (use pb_hom f_pa in \<open>cs_concl cs_shallow cs_simp: cat_cs_simps\<close>)+
    from assms that set_\<aa> show ?thesis
      by 
        (
          cs_concl cs_shallow 
            cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros
        )
  qed
  show "ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub>
    cf_id (cat_Set \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" for a
    using assms \<aa> set_\<aa> that
    by 
      (
        cs_concl cs_shallow 
          cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros
      )

qed (auto simp: ntcf_pointed_components intro: cat_cs_intros)

lemma (in \<Z>) ntcf_pointed_is_iso_ntcf'[cat_cs_intros]:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "\<FF>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-)"
    and "\<GG>' = cf_id (cat_Set \<alpha>)"
    and "\<AA>' = cat_Set \<alpha>"
    and "\<BB>' = cat_Set \<alpha>"
    and "\<alpha>' = \<alpha>"
  shows "ntcf_pointed \<alpha> \<aa> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  using assms(1) unfolding assms(2-6) by (rule ntcf_pointed_is_iso_ntcf)

lemmas [cat_cs_intros] = \<Z>.ntcf_pointed_is_iso_ntcf'



subsection\<open>Inverse pointed natural transformation\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-2 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition ntcf_pointed_inv :: "V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_pointed_inv \<alpha> \<aa> =
    [
      (
        \<lambda>X\<in>\<^sub>\<circ>cat_Set \<alpha>\<lparr>Obj\<rparr>.
          [(\<lambda>x\<in>\<^sub>\<circ>X. ntcf_paa \<aa> X x), X, Hom (cat_Set \<alpha>) (set {\<aa>}) X]\<^sub>\<circ>
      ),
      cf_id (cat_Set \<alpha>),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-),
      cat_Set \<alpha>,
      cat_Set \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_pointed_inv_components:
  shows "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr> =
      (
        \<lambda>X\<in>\<^sub>\<circ>cat_Set \<alpha>\<lparr>Obj\<rparr>.
          [(\<lambda>x\<in>\<^sub>\<circ>X. ntcf_paa \<aa> X x), X, Hom (cat_Set \<alpha>) (set {\<aa>}) X]\<^sub>\<circ>
      )"
    and [cat_cs_simps]: "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTDom\<rparr> = cf_id (cat_Set \<alpha>)"
    and [cat_cs_simps]: 
      "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTCod\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-)"
    and [cat_cs_simps]: "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTDGDom\<rparr> = cat_Set \<alpha>"
    and [cat_cs_simps]: "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding ntcf_pointed_inv_def nt_field_simps
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_pointed_inv_components(1)
  |vsv ntcf_pointed_inv_NTMap_vsv[cat_cs_intros]|
  |vdomain ntcf_pointed_inv_NTMap_vdomain[cat_cs_simps]|
  |app ntcf_pointed_inv_NTMap_app'|

lemma (in \<Z>) ntcf_pointed_inv_NTMap_app_ArrVal_app[cat_cs_simps]: 
  assumes "X \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "x \<in>\<^sub>\<circ> X"
  shows "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> = ntcf_paa \<aa> X x"
  by 
    (
      simp add: 
        assms(2) ntcf_pointed_inv_NTMap_app'[OF assms(1)] arr_Rel_components
    )

lemma (in \<Z>) ntcf_pointed_inv_NTMap_app_is_arr: 
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "X \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr> :
    X \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom (cat_Set \<alpha>) (set {\<aa>}) X"
proof-
  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)
  note app_X = ntcf_pointed_inv_NTMap_app'[OF assms(2)]
  show ?thesis 
  proof(intro cat_Set_is_arrI arr_SetI)
    show ArrVal_vsv: "vsv (ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>)"
      unfolding app_X arr_Rel_components by simp
    show "vcard (ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>) = 3\<^sub>\<nat>"
      unfolding app_X arr_Rel_components by (simp add: nat_omega_simps)
    show ArrVal_vdomain: 
      "\<D>\<^sub>\<circ> (ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>) =
        ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrDom\<rparr>"
      unfolding app_X arr_Rel_components by simp
    from assms show vrange_left: 
      "\<R>\<^sub>\<circ> (ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ>
        ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrCod\<rparr>"
      unfolding app_X arr_Rel_components by (auto intro: cat_cs_intros)
    from assms show "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      unfolding app_X arr_Rel_components cat_Set_components(1) 
      by (intro Set.cat_Hom_in_Vset[OF _ assms(2)])
        (auto simp: cat_Set_components(1))  
  qed (use assms in \<open>auto simp: app_X arr_Rel_components cat_Set_components(1)\<close>)
qed

lemma (in \<Z>) ntcf_pointed_inv_NTMap_app_is_arr'[cat_cs_intros]: 
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "X \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "A' = X"
    and "B' = Hom (cat_Set \<alpha>) (set {\<aa>}) X"
    and "\<CC>' = cat_Set \<alpha>"
  shows "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr> : A' \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1,2) 
  unfolding assms(3-5) 
  by (rule ntcf_pointed_inv_NTMap_app_is_arr)

lemmas [cat_cs_intros] = \<Z>.ntcf_pointed_inv_NTMap_app_is_arr'

lemma (in \<Z>) is_inverse_ntcf_pointed_inv_NTMap_app:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "X \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows 
    "is_inverse
      (cat_Set \<alpha>)
      (ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>)
      (ntcf_pointed \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>X\<rparr>)"
  (is \<open>is_inverse (cat_Set \<alpha>) ?bwd ?fwd\<close>)
proof(intro is_inverseI)

  let ?Hom = \<open>Hom (cat_Set \<alpha>) (set {\<aa>}) X\<close>

  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)

  from assms(1) have set_\<aa>: "set {\<aa>} \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    unfolding cat_Set_components(1) by blast
  have Hom_\<aa>X: "?Hom \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
     by
       (
         auto 
          simp: cat_Set_components(1) 
          intro!: Set.cat_Hom_in_Vset set_\<aa> assms(2)
       )

  from assms show "?bwd : X \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> ?Hom"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  from assms show "?fwd : ?Hom \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)

  from assms set_\<aa> Hom_\<aa>X have lhs_is_arr:
    "?bwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?fwd : ?Hom \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> ?Hom"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  then have dom_lhs: "\<D>\<^sub>\<circ> ((?bwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?fwd)\<lparr>ArrVal\<rparr>) = ?Hom"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)

  from Hom_\<aa>X have rhs_is_arr: "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?Hom\<rparr> : ?Hom \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> ?Hom"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  then have dom_rhs: "\<D>\<^sub>\<circ> ((cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?Hom\<rparr>)\<lparr>ArrVal\<rparr>) = ?Hom"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)

  show "?bwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?fwd = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?Hom\<rparr>"
  proof(rule arr_Set_eqI)
    from lhs_is_arr show arr_Set_lhs: "arr_Set \<alpha> (?bwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?fwd)"
      by (auto dest: cat_Set_is_arrD)
    from rhs_is_arr show arr_Set_rhs: "arr_Set \<alpha> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?Hom\<rparr>)"
      by (auto dest: cat_Set_is_arrD)
    show "(?bwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?fwd)\<lparr>ArrVal\<rparr> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?Hom\<rparr>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix F assume "F : set {\<aa>} \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X"
      with assms Hom_\<aa>X show 
        "(?bwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?fwd)\<lparr>ArrVal\<rparr>\<lparr>F\<rparr> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?Hom\<rparr>\<lparr>ArrVal\<rparr>\<lparr>F\<rparr>"
        by
          (
            cs_concl  
              cs_simp: cat_cs_simps ntcf_paa_ArrVal
              cs_intro: V_cs_intros cat_Set_cs_intros cat_cs_intros
          )
    qed (use arr_Set_lhs arr_Set_rhs in auto)
  qed (use lhs_is_arr rhs_is_arr in \<open>cs_concl cs_shallow cs_simp: cat_cs_simps\<close>)+

  from assms have lhs_is_arr: "?fwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?bwd : X \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  then have dom_lhs: "\<D>\<^sub>\<circ> ((?fwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?bwd)\<lparr>ArrVal\<rparr>) = X"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)

  from assms have rhs_is_arr: "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>X\<rparr> : X \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> X"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  then have dom_rhs: "\<D>\<^sub>\<circ> ((cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>X\<rparr>)\<lparr>ArrVal\<rparr>) = X"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps)

  show "?fwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?bwd = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>X\<rparr>"
  proof(rule arr_Set_eqI)
    from lhs_is_arr show arr_Set_lhs: "arr_Set \<alpha> (?fwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?bwd)"
      by (auto dest: cat_Set_is_arrD)
    from rhs_is_arr show arr_Set_rhs: "arr_Set \<alpha> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>X\<rparr>)"
      by (auto dest: cat_Set_is_arrD)
    show "(?fwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?bwd)\<lparr>ArrVal\<rparr> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix x assume "x \<in>\<^sub>\<circ> X"
      with assms show 
        "(?fwd \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?bwd)\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>X\<rparr>\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed (use arr_Set_lhs arr_Set_rhs in auto)
  qed (use lhs_is_arr rhs_is_arr in \<open>cs_concl cs_shallow cs_simp: cat_cs_simps\<close>)+

qed


subsubsection\<open>Inverse pointed natural transformation is a natural isomorphism\<close>

lemma (in \<Z>) ntcf_pointed_inv_is_ntcf:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "ntcf_pointed_inv \<alpha> \<aa> :
    cf_id (cat_Set \<alpha>) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-) :
    cat_Set \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof(intro is_ntcfI')

  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)

  note \<aa> = assms[unfolded cat_Set_components(1)]
  from assms have set_\<aa>: "set {\<aa>} \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    unfolding cat_Set_components by auto

  show "vfsequence (ntcf_pointed_inv \<alpha> \<aa>)" 
    unfolding ntcf_pointed_inv_def by simp
  show "vcard (ntcf_pointed_inv \<alpha> \<aa>) = 5\<^sub>\<nat>"
    unfolding ntcf_pointed_inv_def by (simp add: nat_omega_simps)
  from set_\<aa> show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-) : cat_Set \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)

  show "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
    cf_id (cat_Set \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" for a
    using that assms set_\<aa>
    by 
      (
        cs_concl cs_shallow 
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros
      )

  show 
    "ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_id (cat_Set \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> =
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
        ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
    if "F : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" for A B F
  proof-
    let ?pb = \<open>ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>B\<rparr>\<close>
      and ?pa = \<open>ntcf_pointed_inv \<alpha> \<aa>\<lparr>NTMap\<rparr>\<lparr>A\<rparr>\<close>
      and ?hom = \<open>cf_hom (cat_Set \<alpha>) [cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>set {\<aa>}\<rparr>, F]\<^sub>\<circ>\<close>
    from assms set_\<aa> that have pb_F: 
      "?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom (cat_Set \<alpha>) (set {\<aa>}) B"
      by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_prod_cs_intros)
    then have dom_lhs: "\<D>\<^sub>\<circ> ((?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr>) = A"
      by (cs_concl cs_shallow cs_simp: cat_cs_simps)
    from that assms set_\<aa> that have hom_pa:
      "?hom \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom (cat_Set \<alpha>) (set {\<aa>}) B"
      by (cs_concl cs_intro: cat_cs_intros cat_prod_cs_intros cat_op_intros)
    then have dom_rhs: "\<D>\<^sub>\<circ> ((?hom \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa)\<lparr>ArrVal\<rparr>) = A"
      by (cs_concl cs_shallow cs_simp: cat_cs_simps)
    have [cat_cs_simps]: "?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F = ?hom \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa"
    proof(rule arr_Set_eqI)
      from pb_F show arr_Set_pb_F: "arr_Set \<alpha> (?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)"
        by (auto dest: cat_Set_is_arrD(1))
      from hom_pa show arr_Set_hom_pa: "arr_Set \<alpha> (?hom \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa)"
        by (auto dest: cat_Set_is_arrD(1))
      show "(?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr> = (?hom \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa)\<lparr>ArrVal\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
        fix a assume "a \<in>\<^sub>\<circ> A"
        with assms \<aa> set_\<aa> that show 
          "(?pb \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = (?hom \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?pa)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
          by
            (
              cs_concl 
                cs_simp: cat_cs_simps
                cs_intro: 
                  cat_Set_cs_intros
                  cat_cs_intros
                  cat_prod_cs_intros
                  cat_op_intros
            )
      qed (use arr_Set_pb_F arr_Set_hom_pa in auto)
    qed (use pb_F hom_pa in \<open>cs_concl cs_shallow cs_simp: cat_cs_simps\<close>)+
    from assms that set_\<aa> show ?thesis
      by 
        (
          cs_concl cs_shallow 
            cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros
        )
  qed

qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

lemma (in \<Z>) ntcf_pointed_inv_is_ntcf'[cat_cs_intros]:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "\<FF>' = cf_id (cat_Set \<alpha>)"
    and "\<GG>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-)"
    and "\<AA>' = cat_Set \<alpha>"
    and "\<BB>' = cat_Set \<alpha>"
    and "\<alpha>' = \<alpha>"
  shows "ntcf_pointed_inv \<alpha> \<aa> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  using assms(1) unfolding assms(2-6) by (rule ntcf_pointed_inv_is_ntcf)

lemmas [cat_cs_intros] = \<Z>.ntcf_pointed_inv_is_ntcf'

lemma (in \<Z>) inv_ntcf_ntcf_pointed[cat_cs_simps]:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "inv_ntcf (ntcf_pointed \<alpha> \<aa>) = ntcf_pointed_inv \<alpha> \<aa>"
  by 
    (
      rule iso_ntcf_if_is_inverse(3)[symmetric], 
      rule is_iso_ntcfD(1)[OF ntcf_pointed_is_iso_ntcf[OF assms]],
      rule ntcf_pointed_inv_is_ntcf[OF assms],
      rule is_inverse_ntcf_pointed_inv_NTMap_app[OF assms]
    )

lemma (in \<Z>) inv_ntcf_ntcf_pointed_inv[cat_cs_simps]:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "inv_ntcf (ntcf_pointed_inv \<alpha> \<aa>) = ntcf_pointed \<alpha> \<aa>"
  by
    (
      rule iso_ntcf_if_is_inverse(4)[symmetric], 
      rule is_iso_ntcfD(1)[OF ntcf_pointed_is_iso_ntcf[OF assms]],
      rule ntcf_pointed_inv_is_ntcf[OF assms],
      rule is_inverse_ntcf_pointed_inv_NTMap_app[OF assms]
    )

lemma (in \<Z>) ntcf_pointed_inv_is_iso_ntcf:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "ntcf_pointed_inv \<alpha> \<aa> :
    cf_id (cat_Set \<alpha>) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-) :
    cat_Set \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  by
    (
      rule iso_ntcf_if_is_inverse(2), 
      rule is_iso_ntcfD(1)[OF ntcf_pointed_is_iso_ntcf[OF assms]],
      rule ntcf_pointed_inv_is_ntcf[OF assms],
      rule is_inverse_ntcf_pointed_inv_NTMap_app[OF assms]
    )

lemma (in \<Z>) ntcf_pointed_inv_is_iso_ntcf'[cat_cs_intros]:
  assumes "\<aa> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "\<FF>' = cf_id (cat_Set \<alpha>)"
    and "\<GG>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Set \<alpha>(set {\<aa>},-)"
    and "\<AA>' = cat_Set \<alpha>"
    and "\<BB>' = cat_Set \<alpha>"
    and "\<alpha>' = \<alpha>"
  shows "ntcf_pointed_inv \<alpha> \<aa> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  using assms(1) unfolding assms(2-6) by (rule ntcf_pointed_inv_is_iso_ntcf)

lemmas [cat_cs_intros] = \<Z>.ntcf_pointed_inv_is_iso_ntcf'

text\<open>\newpage\<close>

end