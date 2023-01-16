(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Simple semicategories\<close>
theory CZH_SMC_Simple
  imports 
    CZH_DG_Simple
    CZH_SMC_NTSMCF
begin



subsection\<open>Background\<close>


text\<open>
The section presents a variety of simple semicategories, such as the empty
semicategory \<open>0\<close> and a semicategory with one object and one arrow \<open>1\<close>.
All of the entities presented in this section are generalizations of certain
simple categories, whose definitions can be found 
in \<^cite>\<open>"mac_lane_categories_2010"\<close>.
\<close>



subsection\<open>Empty semicategory \<open>0\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition smc_0 :: "V"
  where "smc_0 = [0, 0, 0, 0, 0]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_0_components:
  shows "smc_0\<lparr>Obj\<rparr> = 0"
    and "smc_0\<lparr>Arr\<rparr> = 0"
    and "smc_0\<lparr>Dom\<rparr> = 0"
    and "smc_0\<lparr>Cod\<rparr> = 0"
    and "smc_0\<lparr>Comp\<rparr> = 0"
  unfolding smc_0_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_smc_0: "smc_dg smc_0 = dg_0"
  unfolding smc_dg_def smc_0_def dg_0_def dg_field_simps
  by (simp add: nat_omega_simps)

lemmas_with (in \<Z>) [folded smc_dg_smc_0, unfolded slicing_simps]: 
  smc_0_is_arr_iff = dg_0_is_arr_iff


subsubsection\<open>\<open>0\<close> is a semicategory\<close>

lemma (in \<Z>) semicategory_smc_0[smc_cs_intros]: "semicategory \<alpha> smc_0"
proof(intro semicategoryI)
  show "vfsequence smc_0" unfolding smc_0_def by (simp add: nat_omega_simps)
  show "vcard smc_0 = 5\<^sub>\<nat>" unfolding smc_0_def by (simp add: nat_omega_simps)
  show "digraph \<alpha> (smc_dg smc_0)"
    by (simp add: smc_dg_smc_0 \<Z>.digraph_dg_0 \<Z>_axioms)
qed (auto simp: smc_0_components smc_0_is_arr_iff)

lemmas [smc_cs_intros] = \<Z>.semicategory_smc_0


subsubsection\<open>Opposite of the semicategory \<open>0\<close>\<close>

lemma op_smc_smc_0[smc_op_simps]: "op_smc (smc_0) = smc_0"
proof(rule smc_dg_eqI)
  define \<beta> where "\<beta> = \<omega> + \<omega>"
  interpret \<beta>: \<Z> \<beta> unfolding \<beta>_def by (rule \<Z>_\<omega>\<omega>)
  show "semicategory \<beta> (op_smc smc_0)"
    by (cs_concl cs_shallow cs_intro: smc_cs_intros smc_op_intros)
  show "semicategory \<beta> smc_0" by (cs_concl cs_shallow cs_intro: smc_cs_intros)
qed 
  (
    simp_all add: 
      smc_0_components op_smc_components smc_dg_smc_0 
      slicing_commute[symmetric] dg_op_simps
  )


subsubsection\<open>A semicategory without objects is empty\<close>

lemma (in semicategory) smc_smc_0_if_Obj_0:
  assumes "\<CC>\<lparr>Obj\<rparr> = 0"
  shows "\<CC> = smc_0"
  by (rule smc_eqI[of \<alpha>])
    (
      auto simp:
        smc_cs_intros
        assms
        semicategory_smc_0 
        smc_0_components 
        smc_Arr_vempty_if_Obj_vempty 
        smc_Cod_vempty_if_Arr_vempty 
        smc_Dom_vempty_if_Arr_vempty
        smc_Comp_vempty_if_Arr_vempty
    )



subsection\<open>Empty semifunctor\<close>


text\<open>
An empty semifunctor is defined as a semifunctor between an
empty semicategory and an arbitrary semicategory.
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smcf_0 :: "V \<Rightarrow> V"
  where "smcf_0 \<AA> = [0, 0, smc_0, \<AA>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smcf_0_components:
  shows "smcf_0 \<AA>\<lparr>ObjMap\<rparr> = 0"
    and "smcf_0 \<AA>\<lparr>ArrMap\<rparr> = 0"
    and "smcf_0 \<AA>\<lparr>HomDom\<rparr> = smc_0"
    and "smcf_0 \<AA>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding smcf_0_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smcf_dghm_smcf_0: "smcf_dghm (smcf_0 \<AA>) = dghm_0 (smc_dg \<AA>)"
  unfolding 
    smcf_dghm_def smcf_0_def dg_0_def smc_0_def dghm_0_def smc_dg_def 
    dg_field_simps dghm_field_simps 
  by (simp add: nat_omega_simps)


text\<open>Opposite empty semicategory homomorphism.\<close>

lemma op_smcf_smcf_0: "op_smcf (smcf_0 \<CC>) = smcf_0 (op_smc \<CC>)"
  unfolding 
    smcf_0_def op_smc_def op_smcf_def smc_0_def dghm_field_simps dg_field_simps
  by (simp add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma smcf_0_ObjMap_vsv[smc_cs_intros]: "vsv (smcf_0 \<CC>\<lparr>ObjMap\<rparr>)"
  unfolding smcf_0_components by simp


subsubsection\<open>Arrow map\<close>

lemma smcf_0_ArrMap_vsv[smc_cs_intros]: "vsv (smcf_0 \<CC>\<lparr>ArrMap\<rparr>)"
  unfolding smcf_0_components by simp


subsubsection\<open>Empty semifunctor is a faithful semifunctor\<close>

lemma (in \<Z>) smcf_0_is_ft_semifunctor: 
  assumes "semicategory \<alpha> \<AA>"
  shows "smcf_0 \<AA> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<AA>"
proof(rule is_ft_semifunctorI)
  show "smcf_0 \<AA> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  proof(rule is_semifunctorI, unfold smc_dg_smc_0 smcf_dghm_smcf_0)
    show "vfsequence (smcf_0 \<AA>)" unfolding smcf_0_def by simp
    show "vcard (smcf_0 \<AA>) = 4\<^sub>\<nat>"
      unfolding smcf_0_def by (simp add: nat_omega_simps)
    show "dghm_0 (smc_dg \<AA>) : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<AA>"
      by 
        (
          simp add: 
            assms 
            dghm_0_is_ft_dghm 
            is_ft_dghm.axioms(1) 
            semicategory.smc_digraph
        )
  qed (auto simp: assms semicategory_smc_0 smcf_0_components smc_0_is_arr_iff)
  show "smcf_dghm (smcf_0 \<AA>) : smc_dg smc_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> smc_dg \<AA>"
    by 
      (
        auto simp: 
          assms 
          \<Z>.dghm_0_is_ft_dghm
          \<Z>_axioms 
          smc_dg_smc_0 
          semicategory.smc_digraph 
          smcf_dghm_smcf_0
      )
qed

lemma (in \<Z>) smcf_0_is_ft_semifunctor'[smcf_cs_intros]:
  assumes "semicategory \<alpha> \<AA>"
    and "\<BB>' = \<AA>"
    and "\<AA>' = smc_0"
  shows "smcf_0 \<AA> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule smcf_0_is_ft_semifunctor)

lemmas [smcf_cs_intros] = \<Z>.smcf_0_is_ft_semifunctor'

lemma (in \<Z>) smcf_0_is_semifunctor: 
  assumes "semicategory \<alpha> \<AA>"
  shows "smcf_0 \<AA> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  using smcf_0_is_ft_semifunctor[OF assms] by auto

lemma (in \<Z>) smcf_0_is_semifunctor'[smc_cs_intros]: 
  assumes "semicategory \<alpha> \<AA>"
    and "\<BB>' = \<AA>"
    and "\<AA>' = smc_0"
  shows "smcf_0 \<AA> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule smcf_0_is_semifunctor)

lemmas [smc_cs_intros] = \<Z>.smcf_0_is_semifunctor'


subsubsection\<open>Further properties\<close>

lemma is_semifunctor_is_smcf_0_if_smc_0:
  assumes "\<FF> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<FF> = smcf_0 \<CC>"
proof(rule smcf_dghm_eqI)
  interpret \<FF>: is_semifunctor \<alpha> smc_0 \<CC> \<FF> by (rule assms(1))
  show "\<FF> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms(1))
  then have dom_lhs: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = 0" "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = 0" 
    by (cs_concl cs_simp: smc_cs_simps smc_0_components)+
  show "smcf_0 \<CC> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (cs_concl cs_intro: smc_cs_intros)
  show "smcf_dghm \<FF> = smcf_dghm (smcf_0 \<CC>)"
    unfolding smcf_dghm_smcf_0
    by 
      (
        rule is_dghm_is_dghm_0_if_dg_0, 
        rule \<FF>.smcf_is_dghm[unfolded slicing_simps smc_dg_smc_0]
      )
qed simp_all 



subsection\<open>Empty natural transformation of semifunctors\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntsmcf_0 :: "V \<Rightarrow> V" 
  where "ntsmcf_0 \<CC> = [0, smcf_0 \<CC>, smcf_0 \<CC>, smc_0, \<CC>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntsmcf_0_components:
  shows "ntsmcf_0 \<CC>\<lparr>NTMap\<rparr> = 0"
    and [smc_cs_simps]: "ntsmcf_0 \<CC>\<lparr>NTDom\<rparr> = smcf_0 \<CC>"
    and [smc_cs_simps]: "ntsmcf_0 \<CC>\<lparr>NTCod\<rparr> = smcf_0 \<CC>"
    and [smc_cs_simps]: "ntsmcf_0 \<CC>\<lparr>NTDGDom\<rparr> = smc_0"
    and [smc_cs_simps]: "ntsmcf_0 \<CC>\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntsmcf_0_def nt_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma ntsmcf_tdghm_ntsmcf_0: "ntsmcf_tdghm (ntsmcf_0 \<AA>) = tdghm_0 (smc_dg \<AA>)"
  unfolding 
    ntsmcf_tdghm_def ntsmcf_0_def tdghm_0_def smcf_dghm_def 
    smcf_0_def smc_dg_def smc_0_def dghm_0_def dg_0_def
    dg_field_simps dghm_field_simps nt_field_simps
  by (simp add: nat_omega_simps)


text\<open>Duality.\<close>

lemma op_ntsmcf_ntsmcf_0: "op_ntsmcf (ntsmcf_0 \<CC>) = ntsmcf_0 (op_smc \<CC>)"
  by
    (
      simp_all add:
        op_ntsmcf_def ntsmcf_0_def op_smc_def op_smcf_smcf_0 smc_0_def
        nt_field_simps dg_field_simps nat_omega_simps
    )


subsubsection\<open>Natural transformation map\<close>

lemma ntsmcf_0_NTMap_vsv[smc_cs_intros]: "vsv (ntsmcf_0 \<CC>\<lparr>NTMap\<rparr>)"
  unfolding ntsmcf_0_components by simp

lemma ntsmcf_0_NTMap_vdomain[smc_cs_simps]: "\<D>\<^sub>\<circ> (ntsmcf_0 \<CC>\<lparr>NTMap\<rparr>) = 0"
  unfolding ntsmcf_0_components by simp

lemma ntsmcf_0_NTMap_vrange[smc_cs_simps]: "\<R>\<^sub>\<circ> (ntsmcf_0 \<CC>\<lparr>NTMap\<rparr>) = 0"
  unfolding ntsmcf_0_components by simp


subsubsection\<open>
Empty natural transformation of semifunctors
is a natural transformation of semifunctors
\<close>

lemma (in semicategory) smc_ntsmcf_0_is_ntsmcfI: 
  "ntsmcf_0 \<CC> : smcf_0 \<CC> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_0 \<CC> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_ntsmcfI)
  show "vfsequence (ntsmcf_0 \<CC>)" unfolding ntsmcf_0_def by simp
  show "vcard (ntsmcf_0 \<CC>) = 5\<^sub>\<nat>"
    unfolding ntsmcf_0_def by (simp add: nat_omega_simps)
  show "ntsmcf_tdghm (ntsmcf_0 \<CC>) :
    smcf_dghm (smcf_0 \<CC>) \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm (smcf_0 \<CC>) :
    smc_dg smc_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
    unfolding ntsmcf_tdghm_ntsmcf_0 smcf_dghm_smcf_0 smc_dg_smc_0
    by (cs_concl cs_shallow cs_intro: dg_cs_intros slicing_intros)
  show
    "ntsmcf_0 \<CC>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> smcf_0 \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
      smcf_0 \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ntsmcf_0 \<CC>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    if "f : a \<mapsto>\<^bsub>smc_0\<^esub> b" for a b f
    using that by (elim is_arrE) (auto simp: smc_0_components)
qed 
  (
    cs_concl cs_shallow 
      cs_simp: smc_cs_simps smc_0_components(1) cs_intro: smc_cs_intros
  )+

lemma (in semicategory) smc_ntsmcf_0_is_ntsmcfI'[smc_cs_intros]:
  assumes "\<FF>' = smcf_0 \<CC>"
    and "\<GG>' = smcf_0 \<CC>"
    and "\<AA>' = smc_0"
    and "\<BB>' = \<CC>"
    and "\<FF>' = \<FF>"
    and "\<GG>' = \<GG>"
  shows "ntsmcf_0 \<CC> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule smc_ntsmcf_0_is_ntsmcfI)

lemmas [smc_cs_intros] = semicategory.smc_ntsmcf_0_is_ntsmcfI'

lemma is_ntsmcf_is_ntsmcf_0_if_smc_0:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<NN> = ntsmcf_0 \<CC>" and "\<FF> = smcf_0 \<CC>" and "\<GG> = smcf_0 \<CC>"
proof-
  interpret \<NN>: is_ntsmcf \<alpha> smc_0 \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  note is_tdghm_is_tdghm_0_if_dg_0 = is_tdghm_is_tdghm_0_if_dg_0
    [
      OF \<NN>.ntsmcf_is_tdghm[unfolded smc_dg_smc_0], 
      folded smcf_dghm_smcf_0 ntsmcf_tdghm_ntsmcf_0
    ]
  show \<FF>_def: "\<FF> = smcf_0 \<CC>" and \<GG>_def: "\<GG> = smcf_0 \<CC>"
    by (all\<open>intro is_semifunctor_is_smcf_0_if_smc_0\<close>)
      (cs_concl cs_shallow cs_intro: smc_cs_intros)+
  show "\<NN> = ntsmcf_0 \<CC>" 
  proof(rule ntsmcf_tdghm_eqI)
    show "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms(1))
    show "ntsmcf_0 \<CC> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: \<FF>_def \<GG>_def cs_intro: smc_cs_intros)
  qed (simp_all add: \<FF>_def \<GG>_def is_tdghm_is_tdghm_0_if_dg_0)
qed


subsubsection\<open>Further properties\<close>

lemma ntsmcf_vcomp_ntsmcf_ntsmcf_0[smc_cs_simps]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntsmcf_0 \<CC> = ntsmcf_0 \<CC>"
proof-
  interpret \<NN>: is_ntsmcf \<alpha> smc_0 \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  show ?thesis
    unfolding is_ntsmcf_is_ntsmcf_0_if_smc_0[OF assms]
  proof(rule ntsmcf_eqI)
    show "ntsmcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntsmcf_0 \<CC> :
      smcf_0 \<CC> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_0 \<CC> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: smc_cs_intros)
    then have dom_lhs: "\<D>\<^sub>\<circ> ((ntsmcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntsmcf_0 \<CC>)\<lparr>NTMap\<rparr>) = 0"
      by
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_0_components cs_intro: smc_cs_intros
        )
    show "ntsmcf_0 \<CC> : smcf_0 \<CC> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_0 \<CC> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: smc_cs_intros)
    then have dom_rhs: "\<D>\<^sub>\<circ> (ntsmcf_0 \<CC>\<lparr>NTMap\<rparr>) = 0"
      by
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_0_components cs_intro: smc_cs_intros
        )
    show "(ntsmcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntsmcf_0 \<CC>)\<lparr>NTMap\<rparr> = ntsmcf_0 \<CC>\<lparr>NTMap\<rparr>"
      by (rule vsv_eqI, unfold dom_lhs dom_rhs) (auto intro: smc_cs_intros)
  qed simp_all
qed

lemma ntsmcf_vcomp_ntsmcf_0_ntsmcf[smc_cs_simps]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "ntsmcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> = ntsmcf_0 \<CC>"
proof-
  interpret \<NN>: is_ntsmcf \<alpha> smc_0 \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  show ?thesis
    unfolding is_ntsmcf_is_ntsmcf_0_if_smc_0[OF assms]
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
qed



subsection\<open>\<open>10\<close>: semicategory with one object and no arrows\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smc_10 :: "V \<Rightarrow> V"
  where "smc_10 \<aa> = [set {\<aa>}, 0, 0, 0, 0]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_10_components:
  shows "smc_10 \<aa>\<lparr>Obj\<rparr> = set {\<aa>}"
    and "smc_10 \<aa>\<lparr>Arr\<rparr> = 0"
    and "smc_10 \<aa>\<lparr>Dom\<rparr> = 0"
    and "smc_10 \<aa>\<lparr>Cod\<rparr> = 0"
    and "smc_10 \<aa>\<lparr>Comp\<rparr> = 0"
  unfolding smc_10_def dg_field_simps by (auto simp: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_smc_10: "smc_dg (smc_10 \<aa>) = (dg_10 \<aa>)"
  unfolding smc_dg_def smc_10_def dg_10_def dg_field_simps
  by (simp add: nat_omega_simps)

lemmas_with (in \<Z>) [folded smc_dg_smc_10, unfolded slicing_simps]: 
  smc_10_is_arr_iff = dg_10_is_arr_iff


subsubsection\<open>\<open>10\<close> is a semicategory\<close>

lemma (in \<Z>) semicategory_smc_10: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "semicategory \<alpha> (smc_10 \<aa>)"
proof(intro semicategoryI)
  show "vfsequence (smc_10 \<aa>)" 
    unfolding smc_10_def by (simp add: nat_omega_simps)
  show "vcard (smc_10 \<aa>) = 5\<^sub>\<nat>" 
    unfolding smc_10_def by (simp add: nat_omega_simps)
  show "digraph \<alpha> (smc_dg (smc_10 \<aa>))"
    unfolding smc_dg_smc_10 by (rule digraph_dg_10[OF assms])
qed (auto simp: smc_10_components smc_10_is_arr_iff vsubset_vsingleton_leftI)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma smc_10_is_arr_iff: "\<FF> : \<AA> \<mapsto>\<^bsub>smc_10 \<aa>\<^esub> \<BB> \<longleftrightarrow> False"
  unfolding is_arr_def smc_10_components by simp



subsection\<open>\<open>1\<close>: semicategory with one object and one arrow\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smc_1 :: "V \<Rightarrow> V \<Rightarrow> V"
  where "smc_1 \<aa> \<ff> = 
    [set {\<aa>}, set {\<ff>}, set {\<langle>\<ff>, \<aa>\<rangle>}, set {\<langle>\<ff>, \<aa>\<rangle>}, set {\<langle>[\<ff>, \<ff>]\<^sub>\<circ>, \<ff>\<rangle>}]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_1_components:
  shows "smc_1 \<aa> \<ff>\<lparr>Obj\<rparr> = set {\<aa>}"
    and "smc_1 \<aa> \<ff>\<lparr>Arr\<rparr> = set {\<ff>}"
    and "smc_1 \<aa> \<ff>\<lparr>Dom\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
    and "smc_1 \<aa> \<ff>\<lparr>Cod\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
    and "smc_1 \<aa> \<ff>\<lparr>Comp\<rparr> = set {\<langle>[\<ff>, \<ff>]\<^sub>\<circ>, \<ff>\<rangle>}"
  unfolding smc_1_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma dg_smc_1: "smc_dg (smc_1 \<aa> \<ff>) = dg_1 \<aa> \<ff>"
  unfolding smc_dg_def smc_1_def dg_1_def dg_field_simps
  by (simp add: nat_omega_simps)

lemmas_with [folded dg_smc_1, unfolded slicing_simps]: 
  smc_1_is_arrI = dg_1_is_arrI
  and smc_1_is_arrD = dg_1_is_arrD
  and smc_1_is_arrE = dg_1_is_arrE
  and smc_1_is_arr_iff = dg_1_is_arr_iff


subsubsection\<open>Composition\<close>

lemma smc_1_Comp_app[simp]: "\<ff> \<circ>\<^sub>A\<^bsub>smc_1 \<aa> \<ff>\<^esub> \<ff> = \<ff>"
  unfolding smc_1_components by simp


subsubsection\<open>\<open>1\<close> is a semicategory\<close>

lemma (in \<Z>) semicategory_smc_1: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "semicategory \<alpha> (smc_1 \<aa> \<ff>)"
proof(intro semicategoryI, unfold dg_smc_1)
  show "vfsequence (smc_1 \<aa> \<ff>)"
    unfolding smc_1_def by (simp add: nat_omega_simps)
  show "vcard (smc_1 \<aa> \<ff>) = 5\<^sub>\<nat>"
    unfolding smc_1_def by (simp add: nat_omega_simps)
qed 
  (
    auto simp: 
      assms
      digraph_dg_1 
      smc_1_is_arr_iff 
      smc_1_components  
      vsubset_vsingleton_leftI
  )

text\<open>\newpage\<close>

end