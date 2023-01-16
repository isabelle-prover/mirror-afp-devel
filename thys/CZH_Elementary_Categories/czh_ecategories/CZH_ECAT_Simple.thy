(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Simple categories\<close>
theory CZH_ECAT_Simple
  imports 
    CZH_Foundations.CZH_SMC_Simple
    CZH_ECAT_NTCF
    CZH_ECAT_Small_Functor
begin



subsection\<open>Background\<close>


text\<open>
The section presents a variety of simple categories, 
(such as the empty category \<open>0\<close> and the singleton category \<open>1\<close>)
and functors between them (see \<^cite>\<open>"mac_lane_categories_2010"\<close>
for further information).
\<close>



subsection\<open>Empty category \<open>0\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition cat_0 :: "V"
  where "cat_0 = [0, 0, 0, 0, 0, 0]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_0_components:
  shows "cat_0\<lparr>Obj\<rparr> = 0"
    and "cat_0\<lparr>Arr\<rparr> = 0"
    and "cat_0\<lparr>Dom\<rparr> = 0"
    and "cat_0\<lparr>Cod\<rparr> = 0"
    and "cat_0\<lparr>Comp\<rparr> = 0"
    and "cat_0\<lparr>CId\<rparr> = 0"
  unfolding cat_0_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_cat_0: "cat_smc cat_0 = smc_0"
  unfolding cat_smc_def cat_0_def smc_0_def dg_field_simps
  by (simp add: nat_omega_simps)

lemmas_with (in \<Z>) [folded cat_smc_cat_0, unfolded slicing_simps]: 
  cat_0_is_arr_iff = smc_0_is_arr_iff


subsubsection\<open>\<open>0\<close> is a category\<close>

lemma (in \<Z>) category_cat_0[cat_cs_intros]: "category \<alpha> cat_0"
proof(intro categoryI)
  show "vfsequence cat_0" "vcard cat_0 = 6\<^sub>\<nat>" 
    by (simp_all add: cat_0_def nat_omega_simps)
qed 
  (
    auto simp: 
      \<Z>_axioms
      cat_0_components 
      cat_0_is_arr_iff 
      cat_smc_cat_0 
      \<Z>.semicategory_smc_0
  )

lemmas [cat_cs_intros] = \<Z>.category_cat_0


subsubsection\<open>Opposite of the category \<open>0\<close>\<close>

lemma op_cat_cat_0[cat_op_simps]: "op_cat (cat_0) = cat_0"
proof(rule cat_smc_eqI)
  define \<beta> where "\<beta> = \<omega> + \<omega>"
  interpret \<beta>: \<Z> \<beta> unfolding \<beta>_def by (rule \<Z>_\<omega>\<omega>)
  show "category \<beta> (op_cat cat_0)"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)
  show "category \<beta> cat_0" by (cs_concl cs_shallow cs_intro: cat_cs_intros)
qed 
  (
    simp_all add:
      cat_0_components op_cat_components cat_smc_cat_0 
      slicing_commute[symmetric] smc_op_simps
  )



subsection\<open>Empty functors\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_0 :: "V \<Rightarrow> V"
  where "cf_0 \<AA> = [0, 0, cat_0, \<AA>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_0_components:
  shows "cf_0 \<AA>\<lparr>ObjMap\<rparr> = 0"
    and "cf_0 \<AA>\<lparr>ArrMap\<rparr> = 0"
    and "cf_0 \<AA>\<lparr>HomDom\<rparr> = cat_0"
    and "cf_0 \<AA>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding cf_0_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cf_smcf_cf_0: "cf_smcf (cf_0 \<AA>) = smcf_0 (cat_smc \<AA>)"
  unfolding 
    dg_field_simps dghm_field_simps 
    cf_smcf_def cf_0_def smc_0_def cat_0_def smcf_0_def cat_smc_def 
  by (simp add: nat_omega_simps)


text\<open>Opposite empty category homomorphism.\<close>

lemma op_cf_cf_0: "op_cf (cf_0 \<CC>) = cf_0 (op_cat \<CC>)"
  unfolding 
    cf_0_def op_cat_def op_cf_def cat_0_def dghm_field_simps dg_field_simps
  by (simp add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma cf_0_ObjMap_vsv[cat_cs_intros]: "vsv (cf_0 \<CC>\<lparr>ObjMap\<rparr>)"
  unfolding cf_0_components by simp


subsubsection\<open>Arrow map\<close>

lemma cf_0_ArrMap_vsv[cat_cs_intros]: "vsv (cf_0 \<CC>\<lparr>ArrMap\<rparr>)"
  unfolding cf_0_components by simp


subsubsection\<open>Empty functor is a faithful functor\<close>

lemma cf_0_is_ft_functor: 
  assumes "category \<alpha> \<AA>"
  shows "cf_0 \<AA> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<AA>"
proof(rule is_ft_functorI)
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  show "cf_0 \<AA> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  proof(rule is_functorI, unfold cat_smc_cat_0 cf_smcf_cf_0)
    show "vfsequence (cf_0 \<AA>)" unfolding cf_0_def by simp
    show "vcard (cf_0 \<AA>) = 4\<^sub>\<nat>"
      unfolding cf_0_def by (simp add: nat_omega_simps)
    from \<Z>.smcf_0_is_ft_semifunctor assms show 
      "smcf_0 (cat_smc \<AA>) : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<AA>"   
      by auto
  qed (auto simp: assms \<AA>.category_cat_0 cat_0_components cf_0_components)
  show "cf_smcf (cf_0 \<AA>) : cat_smc cat_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> cat_smc \<AA>"
    by 
      (
        auto simp:
          assms 
          \<AA>.\<Z>_axioms
          \<AA>.smcf_0_is_ft_semifunctor  
          category.cat_semicategory 
          cf_smcf_cf_0 
          cat_smc_cat_0
      )
qed

lemma cf_0_is_ft_functor'[cf_cs_intros]:
  assumes "category \<alpha> \<AA>"
    and "\<BB>' = \<AA>"
    and "\<AA>' = cat_0"
  shows "cf_0 \<AA> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule cf_0_is_ft_functor)

lemma cf_0_is_functor: 
  assumes "category \<alpha> \<AA>"
  shows "cf_0 \<AA> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  using cf_0_is_ft_functor[OF assms] by auto

lemma cf_0_is_functor'[cat_cs_intros]: 
  assumes "category \<alpha> \<AA>"
    and "\<BB>' = \<AA>"
    and "\<AA>' = cat_0"
  shows "cf_0 \<AA> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule cf_0_is_functor)


subsubsection\<open>Further properties\<close>

lemma is_functor_is_cf_0_if_cat_0:
  assumes "\<FF> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<FF> = cf_0 \<CC>"
proof(rule cf_smcf_eqI)
  interpret \<FF>: is_functor \<alpha> cat_0 \<CC> \<FF> by (rule assms(1))
  show "\<FF> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms(1))
  then have dom_lhs: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = 0" "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = 0" 
    by (cs_concl cs_shallow cs_simp: cat_cs_simps cat_0_components)+
  show "cf_0 \<CC> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  show "cf_smcf \<FF> = cf_smcf (cf_0 \<CC>)"
    unfolding cf_smcf_cf_0
    by 
      (
        rule is_semifunctor_is_smcf_0_if_smc_0, 
        rule \<FF>.cf_is_semifunctor[unfolded slicing_simps cat_smc_cat_0]
      )
qed simp_all 

lemma (in is_functor) cf_comp_cf_cf_0[cat_cs_simps]: "\<FF> \<circ>\<^sub>C\<^sub>F cf_0 \<AA> = cf_0 \<BB>"
proof(rule cf_eqI)
  show "\<FF> \<circ>\<^sub>C\<^sub>F cf_0 \<AA> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (cs_concl cs_intro: cat_cs_intros)
  then have ObjMap_dom_lhs: "\<D>\<^sub>\<circ> ((\<FF> \<circ>\<^sub>C\<^sub>F cf_0 \<AA>)\<lparr>ObjMap\<rparr>) = cat_0\<lparr>Obj\<rparr>"
    and ArrMap_dom_lhs: "\<D>\<^sub>\<circ> ((\<FF> \<circ>\<^sub>C\<^sub>F cf_0 \<AA>)\<lparr>ArrMap\<rparr>) = cat_0\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)+
  show "cf_0 \<BB> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  then have ObjMap_dom_rhs: "\<D>\<^sub>\<circ> (cf_0 \<BB>\<lparr>ObjMap\<rparr>) = cat_0\<lparr>Obj\<rparr>"
    and ArrMap_dom_rhs: "\<D>\<^sub>\<circ> (cf_0 \<BB>\<lparr>ArrMap\<rparr>) = cat_0\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)+
  show "(\<FF> \<circ>\<^sub>C\<^sub>F cf_0 \<AA>)\<lparr>ObjMap\<rparr> = cf_0 \<BB>\<lparr>ObjMap\<rparr>"
    by 
      (
        rule vsv_eqI, 
        unfold ObjMap_dom_lhs ObjMap_dom_rhs ArrMap_dom_lhs ArrMap_dom_rhs
      )
      (auto simp: cat_0_components intro: cat_cs_intros)
  show "(\<FF> \<circ>\<^sub>C\<^sub>F cf_0 \<AA>)\<lparr>ArrMap\<rparr> = cf_0 \<BB>\<lparr>ArrMap\<rparr>"
    by 
      (
        rule vsv_eqI, 
        unfold ObjMap_dom_lhs ObjMap_dom_rhs ArrMap_dom_lhs ArrMap_dom_rhs
      )
      (auto simp: cat_0_components intro: cat_cs_intros)
qed simp_all

lemmas [cat_cs_simps] = is_functor.cf_comp_cf_cf_0



subsection\<open>Empty natural transformation\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter X-1 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition ntcf_0 :: "V \<Rightarrow> V" 
  where "ntcf_0 \<CC> = [0, cf_0 \<CC>, cf_0 \<CC>, cat_0, \<CC>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_0_components:
  shows "ntcf_0 \<CC>\<lparr>NTMap\<rparr> = 0"
    and [cat_cs_simps]: "ntcf_0 \<CC>\<lparr>NTDom\<rparr> = cf_0 \<CC>"
    and [cat_cs_simps]: "ntcf_0 \<CC>\<lparr>NTCod\<rparr> = cf_0 \<CC>"
    and [cat_cs_simps]: "ntcf_0 \<CC>\<lparr>NTDGDom\<rparr> = cat_0"
    and [cat_cs_simps]: "ntcf_0 \<CC>\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntcf_0_def nt_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma ntcf_ntsmcf_ntcf_0: "ntcf_ntsmcf (ntcf_0 \<AA>) = ntsmcf_0 (cat_smc \<AA>)"
  unfolding 
    ntcf_ntsmcf_def ntcf_0_def ntsmcf_0_def cat_smc_def
    cf_smcf_def smcf_0_def cf_0_def cat_0_def smc_0_def
    dg_field_simps dghm_field_simps nt_field_simps
  by (simp add: nat_omega_simps)


text\<open>Duality.\<close>

lemma op_ntcf_ntcf_0: "op_ntcf (ntcf_0 \<CC>) = ntcf_0 (op_cat \<CC>)"
  by
    (
      simp_all add:
        op_ntcf_def ntcf_0_def op_cat_def op_cf_cf_0 cat_0_def
        nt_field_simps dg_field_simps nat_omega_simps
    )


subsubsection\<open>Natural transformation map\<close>

lemma ntcf_0_NTMap_vsv[cat_cs_intros]: "vsv (ntcf_0 \<CC>\<lparr>NTMap\<rparr>)"
  unfolding ntcf_0_components by simp

lemma ntcf_0_NTMap_vdomain[cat_cs_simps]: "\<D>\<^sub>\<circ> (ntcf_0 \<CC>\<lparr>NTMap\<rparr>) = 0"
  unfolding ntcf_0_components by simp

lemma ntcf_0_NTMap_vrange[cat_cs_simps]: "\<R>\<^sub>\<circ> (ntcf_0 \<CC>\<lparr>NTMap\<rparr>) = 0"
  unfolding ntcf_0_components by simp


subsubsection\<open>Empty natural transformation is a natural transformation\<close>

lemma (in category) cat_ntcf_0_is_ntcfI: 
  "ntcf_0 \<CC> : cf_0 \<CC> \<mapsto>\<^sub>C\<^sub>F cf_0 \<CC> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_ntcfI)
  show "vfsequence (ntcf_0 \<CC>)" unfolding ntcf_0_def by simp
  show "vcard (ntcf_0 \<CC>) = 5\<^sub>\<nat>"
    unfolding ntcf_0_def by (simp add: nat_omega_simps)
  show "ntcf_ntsmcf (ntcf_0 \<CC>) :
    cf_smcf (cf_0 \<CC>) \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf (cf_0 \<CC>) :
    cat_smc cat_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
    unfolding ntcf_ntsmcf_ntcf_0 cf_smcf_cf_0 cat_smc_cat_0
    by (cs_concl cs_shallow cs_intro: smc_cs_intros slicing_intros)
qed (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

lemma (in category) cat_ntcf_0_is_ntcfI'[cat_cs_intros]:
  assumes "\<FF>' = cf_0 \<CC>"
    and "\<GG>' = cf_0 \<CC>"
    and "\<AA>' = cat_0"
    and "\<BB>' = \<CC>"
    and "\<FF>' = \<FF>"
    and "\<GG>' = \<GG>"
  shows "ntcf_0 \<CC> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule cat_ntcf_0_is_ntcfI)

lemmas [cat_cs_intros] = category.cat_ntcf_0_is_ntcfI'

lemma is_ntcf_is_ntcf_0_if_cat_0:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<NN> = ntcf_0 \<CC>" and "\<FF> = cf_0 \<CC>" and "\<GG> = cf_0 \<CC>"
proof-
  interpret \<NN>: is_ntcf \<alpha> cat_0 \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  note is_ntsmcf_is_ntsmcf_0_if_smc_0 = is_ntsmcf_is_ntsmcf_0_if_smc_0
    [
      OF \<NN>.ntcf_is_ntsmcf[unfolded cat_smc_cat_0], 
      folded smcf_dghm_smcf_0 ntsmcf_tdghm_ntsmcf_0
    ]
  show \<FF>_def: "\<FF> = cf_0 \<CC>" and \<GG>_def: "\<GG> = cf_0 \<CC>"
    by (all\<open>intro is_functor_is_cf_0_if_cat_0\<close>)
      (cs_concl cs_shallow cs_intro: cat_cs_intros)+
  show "\<NN> = ntcf_0 \<CC>" 
  proof(rule ntcf_ntsmcf_eqI)
    show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms(1))
    show "ntcf_0 \<CC> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_shallow cs_simp: \<FF>_def \<GG>_def cs_intro: cat_cs_intros)
  qed 
    (
      simp_all add: 
        \<FF>_def \<GG>_def is_ntsmcf_is_ntsmcf_0_if_smc_0 ntcf_ntsmcf_ntcf_0
    )
qed


subsubsection\<open>Further properties\<close>

lemma ntcf_vcomp_ntcf_ntcf_0[cat_cs_simps]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_0 \<CC> = ntcf_0 \<CC>"
proof(rule ntcf_ntsmcf_eqI)
  interpret \<NN>: is_ntcf \<alpha> cat_0 \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  show "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_0 \<CC> : cf_0 \<CC> \<mapsto>\<^sub>C\<^sub>F cf_0 \<CC> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    unfolding is_ntcf_is_ntcf_0_if_cat_0[OF assms]
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  show "ntcf_0 \<CC> : cf_0 \<CC> \<mapsto>\<^sub>C\<^sub>F cf_0 \<CC> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  show "ntcf_ntsmcf (\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_0 \<CC>) = ntcf_ntsmcf (ntcf_0 \<CC>)"
    unfolding 
      slicing_commute[symmetric]
      ntsmcf_vcomp_ntsmcf_ntsmcf_0
        [
          OF \<NN>.ntcf_is_ntsmcf[unfolded cat_smc_cat_0], 
          folded ntcf_ntsmcf_ntcf_0
        ]
      ..
qed simp_all

lemma ntcf_vcomp_ntcf_0_ntcf[cat_cs_simps]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "ntcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_0 \<CC>"
proof(rule ntcf_ntsmcf_eqI)
  interpret \<NN>: is_ntcf \<alpha> cat_0 \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  show "ntcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : cf_0 \<CC> \<mapsto>\<^sub>C\<^sub>F cf_0 \<CC> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    unfolding is_ntcf_is_ntcf_0_if_cat_0[OF assms]
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  show "ntcf_0 \<CC> : cf_0 \<CC> \<mapsto>\<^sub>C\<^sub>F cf_0 \<CC> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  show "ntcf_ntsmcf (ntcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = ntcf_ntsmcf (ntcf_0 \<CC>)"
    unfolding 
      slicing_commute[symmetric]
      ntsmcf_vcomp_ntsmcf_0_ntsmcf
        [
          OF \<NN>.ntcf_is_ntsmcf[unfolded cat_smc_cat_0], 
          folded ntcf_ntsmcf_ntcf_0
        ]
      ..
  qed simp_all

lemma (in is_functor) cf_ntcf_comp_cf_ntcf_0[cat_cs_simps]: 
  "\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_0 \<AA> = ntcf_0 \<BB>"
proof(rule ntcf_eqI)
  show "\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_0 \<AA> : cf_0 \<BB> \<mapsto>\<^sub>C\<^sub>F cf_0 \<BB> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  then have dom_lhs: "\<D>\<^sub>\<circ> ((\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_0 \<AA>)\<lparr>NTMap\<rparr>) = cat_0\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  show "ntcf_0 \<BB> : cf_0 \<BB> \<mapsto>\<^sub>C\<^sub>F cf_0 \<BB> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  then have dom_rhs: "\<D>\<^sub>\<circ> (ntcf_0 \<BB>\<lparr>NTMap\<rparr>) = cat_0\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  show "(\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_0 \<AA>)\<lparr>NTMap\<rparr> = ntcf_0 \<BB>\<lparr>NTMap\<rparr>"
    by (rule vsv_eqI, unfold dom_lhs dom_rhs)
      (auto simp: cat_0_components intro!: cat_cs_intros)+
qed simp_all

lemmas [cat_cs_simps] = is_functor.cf_ntcf_comp_cf_ntcf_0



subsection\<open>\<open>1\<close>: category with one object and one arrow\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition cat_1 :: "V \<Rightarrow> V \<Rightarrow> V"
  where "cat_1 \<aa> \<ff> =
    [
      set {\<aa>},
      set {\<ff>},
      set {\<langle>\<ff>, \<aa>\<rangle>},
      set {\<langle>\<ff>, \<aa>\<rangle>},
      set {\<langle>[\<ff>, \<ff>]\<^sub>\<circ>, \<ff>\<rangle>},
      set {\<langle>\<aa>, \<ff>\<rangle>}
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_1_components:
  shows "cat_1 \<aa> \<ff>\<lparr>Obj\<rparr> = set {\<aa>}"
    and "cat_1 \<aa> \<ff>\<lparr>Arr\<rparr> = set {\<ff>}"
    and "cat_1 \<aa> \<ff>\<lparr>Dom\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
    and "cat_1 \<aa> \<ff>\<lparr>Cod\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
    and "cat_1 \<aa> \<ff>\<lparr>Comp\<rparr> = set {\<langle>[\<ff>, \<ff>]\<^sub>\<circ>, \<ff>\<rangle>}"
    and "cat_1 \<aa> \<ff>\<lparr>CId\<rparr> = set {\<langle>\<aa>, \<ff>\<rangle>}"
  unfolding cat_1_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_cat_1: "cat_smc (cat_1 \<aa> \<ff>) = smc_1 \<aa> \<ff>"
  unfolding cat_smc_def cat_1_def smc_1_def dg_field_simps
  by (simp add: nat_omega_simps)

lemmas_with [folded smc_cat_1, unfolded slicing_simps]: 
  cat_1_is_arrI = smc_1_is_arrI
  and cat_1_is_arrD = smc_1_is_arrD
  and cat_1_is_arrE = smc_1_is_arrE
  and cat_1_is_arr_iff = smc_1_is_arr_iff
  and cat_1_Comp_app[cat_cs_simps] = smc_1_Comp_app


subsubsection\<open>Object\<close>

lemma cat_1_ObjI[cat_cs_intros]:
  assumes "a = \<aa>"
  shows "a \<in>\<^sub>\<circ> cat_1 \<aa> \<ff> \<lparr>Obj\<rparr>"
  unfolding cat_1_components(1) assms by simp


subsubsection\<open>Identity\<close>

lemma cat_1_CId_app: "cat_1 \<aa> \<ff>\<lparr>CId\<rparr>\<lparr>\<aa>\<rparr> = \<ff>" 
  unfolding cat_1_components by simp


subsubsection\<open>\<open>1\<close> is a category\<close>

lemma (in \<Z>) category_cat_1: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "category \<alpha> (cat_1 \<aa> \<ff>)"
proof(intro categoryI, unfold smc_cat_1)
  show "vfsequence (cat_1 \<aa> \<ff>)"
    unfolding cat_1_def by (simp add: nat_omega_simps)
  show "vcard (cat_1 \<aa> \<ff>) = 6\<^sub>\<nat>"
    unfolding cat_1_def by (simp add: nat_omega_simps)
qed (auto simp: assms semicategory_smc_1 cat_1_is_arr_iff cat_1_components)

lemmas [cat_cs_intros] = \<Z>.category_cat_1

lemma (in \<Z>) finite_category_cat_1: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "finite_category \<alpha> (cat_1 \<aa> \<ff>)"
  by (intro finite_categoryI')
    (auto simp: cat_1_components intro: category_cat_1[OF assms])

lemmas [cat_small_cs_intros] = \<Z>.finite_category_cat_1


subsubsection\<open>Opposite of the category \<open>1\<close>\<close>

lemma (in \<Z>) cat_1_op[cat_op_simps]:
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "op_cat (cat_1 \<aa> \<ff>) = cat_1 \<aa> \<ff>"
proof(rule cat_eqI, unfold cat_op_simps)
  from assms show "category \<alpha> (op_cat (cat_1 \<aa> \<ff>))"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_op_intros)
  from assms show "category \<alpha> (cat_1 \<aa> \<ff>)"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros)
  show "op_cat (cat_1 \<aa> \<ff>)\<lparr>Comp\<rparr> = cat_1 \<aa> \<ff>\<lparr>Comp\<rparr>"
    unfolding cat_1_components op_cat_components fflip_vsingleton ..
qed (simp_all add: cat_1_components)

lemma (in \<Z>) cat_1_op_0[cat_op_simps]: "op_cat (cat_1 0 0) = cat_1 0 0"
  by 
    (
      cs_concl cs_shallow 
        cs_simp: cat_op_simps cs_intro: V_cs_intros cat_cs_intros
    )


subsubsection\<open>Further properties\<close>

lemma cf_const_if_HomCod_is_cat_1:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_1 \<aa> \<ff>"
  shows "\<KK> = cf_const \<BB> (cat_1 \<aa> \<ff>) \<aa>"
proof(rule cf_eqI)
  interpret \<KK>: is_functor \<alpha> \<BB> \<open>cat_1 \<aa> \<ff>\<close> \<KK> by (rule assms(1))
  show "cf_const \<BB> (cat_1 \<aa> \<ff>) \<aa> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_1 \<aa> \<ff>"
    by (cs_concl cs_intro: cat_cs_intros)
  have ObjMap_dom_lhs: "\<D>\<^sub>\<circ> (\<KK>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>" by (simp add: cat_cs_simps)
  have ObjMap_dom_rhs: "\<D>\<^sub>\<circ> (cf_const \<BB> (cat_1 \<aa> \<ff>) \<aa>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
    by (simp add: cat_cs_simps)
  have ArrMap_dom_lhs: "\<D>\<^sub>\<circ> (\<KK>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>" by (simp add: cat_cs_simps)
  have ArrMap_dom_rhs: "\<D>\<^sub>\<circ> (cf_const \<BB> (cat_1 \<aa> \<ff>) \<aa>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
    by (simp add: cat_cs_simps)
  show "\<KK>\<lparr>ObjMap\<rparr> = cf_const \<BB> (cat_1 \<aa> \<ff>) \<aa>\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
    fix a assume prems: "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    then have "\<KK>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> cat_1 \<aa> \<ff>\<lparr>Obj\<rparr>"
      by (auto intro: \<KK>.cf_ObjMap_app_in_HomCod_Obj)
    then have "\<KK>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<aa>" by (auto simp: cat_1_components)
    with prems show "\<KK>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = cf_const \<BB> (cat_1 \<aa> \<ff>) \<aa>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by (auto simp: cat_cs_simps)
  qed (auto intro: cat_cs_intros)
  show "\<KK>\<lparr>ArrMap\<rparr> = cf_const \<BB> (cat_1 \<aa> \<ff>) \<aa>\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
    fix a assume prems: "a \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
    then have "\<KK>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> cat_1 \<aa> \<ff>\<lparr>Arr\<rparr>"
      by (auto intro: \<KK>.cf_ArrMap_app_in_HomCod_Arr)
    then have "\<KK>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<ff>" by (auto simp: cat_1_components)
    with prems show "\<KK>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = cf_const \<BB> (cat_1 \<aa> \<ff>) \<aa>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
      by (auto simp: cat_1_CId_app cat_cs_simps)
  qed (auto intro: cat_cs_intros)
qed (simp_all add: assms)

lemma cf_const_if_HomDom_is_cat_1:
  assumes "\<KK> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<KK> = cf_const (cat_1 \<aa> \<ff>) \<CC> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)"
proof-

  interpret \<KK>: is_functor \<alpha> \<open>cat_1 \<aa> \<ff>\<close> \<CC> \<KK> by (rule assms(1))

  from cat_1_components(1) have \<aa>: "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto simp: \<KK>.HomDom.cat_in_Obj_in_Vset)
  from cat_1_components(2) have \<ff>: "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto simp: \<KK>.HomDom.cat_in_Arr_in_Vset)

  from \<aa> \<ff> interpret cf_1: 
    is_tm_functor \<alpha> \<open>cat_1 \<aa> \<ff>\<close> \<CC> \<open>cf_const (cat_1 \<aa> \<ff>) \<CC> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<close>
    by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)
  
  show ?thesis
  proof(rule cf_eqI)
    show "cf_const (cat_1 \<aa> \<ff>) \<CC> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>) : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_shallow cs_intro: cat_cs_intros)
    have ObjMap_dom_lhs: "\<D>\<^sub>\<circ> (\<KK>\<lparr>ObjMap\<rparr>) = set {\<aa>}" 
      by (simp add: cat_cs_simps cat_1_components)
    have ObjMap_dom_rhs: 
      "\<D>\<^sub>\<circ> (cf_const (cat_1 \<aa> \<ff>) \<CC> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ObjMap\<rparr>) = set {\<aa>}"
      by (simp add: cat_cs_simps cat_1_components)
    show "\<KK>\<lparr>ObjMap\<rparr> = cf_const (cat_1 \<aa> \<ff>) \<CC> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> set {\<aa>}"
      then have a_def: "a = \<aa>" by simp
      show "\<KK>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = cf_const (cat_1 \<aa> \<ff>) \<CC> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by 
          (
            cs_concl cs_shallow 
              cs_simp: cat_1_components(1) cat_cs_simps a_def 
              cs_intro: V_cs_intros
          )
    qed auto

    have ArrMap_dom_lhs: "\<D>\<^sub>\<circ> (\<KK>\<lparr>ArrMap\<rparr>) = set {\<ff>}" 
      by (simp add: cat_cs_simps cat_1_components)
    have ArrMap_dom_rhs: 
      "\<D>\<^sub>\<circ> (cf_const (cat_1 \<aa> \<ff>) \<CC> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ArrMap\<rparr>) = set {\<ff>}"
      by (simp add: cat_cs_simps cat_1_components)
    
    show "\<KK>\<lparr>ArrMap\<rparr> = cf_const (cat_1 \<aa> \<ff>) \<CC> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      fix f assume "f \<in>\<^sub>\<circ> set {\<ff>}"
      then have f_def: "f = \<ff>" by simp
      show "\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = cf_const (cat_1 \<aa> \<ff>) \<CC> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        unfolding f_def
        by (subst cat_1_CId_app[symmetric, of \<ff> \<aa>])
          (
            cs_concl cs_shallow
              cs_simp: cat_1_components(1,2) cat_cs_simps 
              cs_intro: V_cs_intros cat_cs_intros
          )
    qed auto

  qed (simp_all add: assms)

qed

text\<open>\newpage\<close>

end