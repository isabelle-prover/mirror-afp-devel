(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Simple digraphs\<close>
theory CZH_DG_Simple
  imports CZH_DG_TDGHM
begin



subsection\<open>Background\<close>


text\<open>
The section presents a variety of simple digraphs, such as the empty digraph \<open>0\<close>
and a digraph with one object and one arrow \<open>1\<close>. All of the entities 
presented in this section are generalizations of certain simple categories,
whose definitions can be found in \<^cite>\<open>"mac_lane_categories_2010"\<close>.
\<close>



subsection\<open>Empty digraph \<open>0\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition dg_0 :: V
  where "dg_0 = [0, 0, 0, 0]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_0_components:
  shows "dg_0\<lparr>Obj\<rparr> = 0"
    and "dg_0\<lparr>Arr\<rparr> = 0"
    and "dg_0\<lparr>Dom\<rparr> = 0"
    and "dg_0\<lparr>Cod\<rparr> = 0"
  unfolding dg_0_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>\<open>0\<close> is a digraph\<close>

lemma (in \<Z>) digraph_dg_0[dg_cs_intros]: "digraph \<alpha> dg_0"
proof(intro digraphI)
  show "vfsequence dg_0" unfolding dg_0_def by (simp add: nat_omega_simps)
  show "vcard dg_0 = 4\<^sub>\<nat>" unfolding dg_0_def by (simp add: nat_omega_simps)
qed (auto simp: dg_0_components)

lemmas [dg_cs_intros] = \<Z>.digraph_dg_0


subsubsection\<open>Opposite of the digraph \<open>0\<close>\<close>

lemma op_dg_dg_0[dg_op_simps]: "op_dg (dg_0) = dg_0"
proof(rule dg_eqI, unfold dg_op_simps)
  define \<beta> where "\<beta> = \<omega> + \<omega>"
  interpret \<beta>: \<Z> \<beta> unfolding \<beta>_def by (rule \<Z>_\<omega>\<omega>)
  show "digraph \<beta> (op_dg dg_0)"
    by (cs_concl cs_shallow cs_intro: dg_cs_intros dg_op_intros)
  show "digraph \<beta> dg_0" by (cs_concl cs_shallow cs_intro: dg_cs_intros)
qed (simp_all add: dg_0_components op_dg_components)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_0_is_arr_iff[simp]: "\<FF> : \<AA> \<mapsto>\<^bsub>dg_0\<^esub> \<BB> \<longleftrightarrow> False" 
  by (rule iffI; (elim is_arrE)?) (auto simp: dg_0_components)


subsubsection\<open>A digraph without objects is empty\<close>

lemma (in digraph) dg_dg_0_if_Obj_0:
  assumes "\<CC>\<lparr>Obj\<rparr> = 0"
  shows "\<CC> = dg_0"
  by (rule dg_eqI[of \<alpha>])
    (
      auto simp:
        dg_cs_intros
        assms
        digraph_dg_0 
        dg_0_components 
        dg_Arr_vempty_if_Obj_vempty 
        dg_Cod_vempty_if_Arr_vempty 
        dg_Dom_vempty_if_Arr_vempty
    )



subsection\<open>Empty digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dghm_0 :: "V \<Rightarrow> V"
  where "dghm_0 \<AA> = [0, 0, dg_0, \<AA>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_0_components:
  shows "dghm_0 \<AA>\<lparr>ObjMap\<rparr> = 0"
    and "dghm_0 \<AA>\<lparr>ArrMap\<rparr> = 0"
    and "dghm_0 \<AA>\<lparr>HomDom\<rparr> = dg_0"
    and "dghm_0 \<AA>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding dghm_0_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Opposite empty digraph homomorphism.\<close>

lemma op_dghm_dghm_0: "op_dghm (dghm_0 \<CC>) = dghm_0 (op_dg \<CC>)"
  unfolding 
    dghm_0_def op_dg_def op_dghm_def dg_0_def dghm_field_simps dg_field_simps
  by (simp add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma dghm_0_ObjMap_vsv[dg_cs_intros]: "vsv (dghm_0 \<CC>\<lparr>ObjMap\<rparr>)"
  unfolding dghm_0_components by simp


subsubsection\<open>Arrow map\<close>

lemma dghm_0_ArrMap_vsv[dg_cs_intros]: "vsv (dghm_0 \<CC>\<lparr>ArrMap\<rparr>)"
  unfolding dghm_0_components by simp


subsubsection\<open>Empty digraph homomorphism is a faithful digraph homomorphism\<close>

lemma (in \<Z>) dghm_0_is_ft_dghm: 
  assumes "digraph \<alpha> \<AA>"
  shows "dghm_0 \<AA> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<AA>"
proof(rule is_ft_dghmI)
  show "dghm_0 \<AA> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
  proof(rule is_dghmI)
    show "vfsequence (dghm_0 \<AA>)" unfolding dghm_0_def by simp
    show "vcard (dghm_0 \<AA>) = 4\<^sub>\<nat>"
      unfolding dghm_0_def by (simp add: nat_omega_simps)
  qed (auto simp: assms digraph_dg_0 dghm_0_components dg_0_components)
qed (auto simp: dg_0_components dghm_0_components)

lemma (in \<Z>) dghm_0_is_ft_dghm'[dghm_cs_intros]:
  assumes "digraph \<alpha> \<AA>"
    and "\<BB>' = \<AA>"
    and "\<AA>' = dg_0"
  shows "dghm_0 \<AA> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule dghm_0_is_ft_dghm)

lemmas [dghm_cs_intros] = \<Z>.dghm_0_is_ft_dghm'

lemma (in \<Z>) dghm_0_is_dghm: 
  assumes "digraph \<alpha> \<AA>"
  shows "dghm_0 \<AA> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
  using dghm_0_is_ft_dghm[OF assms] by auto

lemma (in \<Z>) dghm_0_is_dghm'[dg_cs_intros]: 
  assumes "digraph \<alpha> \<AA>"
    and "\<BB>' = \<AA>"
    and "\<AA>' = dg_0"
  shows "dghm_0 \<AA> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule dghm_0_is_dghm)

lemmas [dg_cs_intros] = \<Z>.dghm_0_is_dghm'


subsubsection\<open>Further properties\<close>

lemma is_dghm_is_dghm_0_if_dg_0:
  assumes "\<FF> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<FF> = dghm_0 \<CC>"
proof(rule dghm_eqI)
  interpret \<FF>: is_dghm \<alpha> dg_0 \<CC> \<FF> by (rule assms(1))
  show "\<FF> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms(1))
  then have dom_lhs: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = 0" "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = 0" 
    by (cs_concl cs_simp: dg_cs_simps dg_0_components)+
  show "dghm_0 \<CC> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" by (cs_concl cs_intro: dg_cs_intros)
  then have dom_rhs: "\<D>\<^sub>\<circ> (dghm_0 \<CC>\<lparr>ObjMap\<rparr>) = 0" "\<D>\<^sub>\<circ> (dghm_0 \<CC>\<lparr>ArrMap\<rparr>) = 0" 
    by (cs_concl cs_simp: dg_cs_simps dg_0_components)+
  show "\<FF>\<lparr>ObjMap\<rparr> = dghm_0 \<CC>\<lparr>ObjMap\<rparr>"
    by (rule vsv_eqI, unfold dom_lhs dom_rhs) (auto intro: dg_cs_intros)
  show "\<FF>\<lparr>ArrMap\<rparr> = dghm_0 \<CC>\<lparr>ArrMap\<rparr>"
    by (rule vsv_eqI, unfold dom_lhs dom_rhs) (auto intro: dg_cs_intros)
qed simp_all



subsection\<open>Empty transformation of digraph homomorphisms\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition tdghm_0 :: "V \<Rightarrow> V" 
  where "tdghm_0 \<CC> = [0, dghm_0 \<CC>, dghm_0 \<CC>, dg_0, \<CC>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma tdghm_0_components:
  shows "tdghm_0 \<CC>\<lparr>NTMap\<rparr> = 0"
    and [dg_cs_simps]: "tdghm_0 \<CC>\<lparr>NTDom\<rparr> = dghm_0 \<CC>"
    and [dg_cs_simps]: "tdghm_0 \<CC>\<lparr>NTCod\<rparr> = dghm_0 \<CC>"
    and [dg_cs_simps]: "tdghm_0 \<CC>\<lparr>NTDGDom\<rparr> = dg_0"
    and [dg_cs_simps]: "tdghm_0  \<CC>\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding tdghm_0_def nt_field_simps by (simp_all add: nat_omega_simps)


text\<open>Duality.\<close>

lemma op_tdghm_tdghm_0: "op_tdghm (tdghm_0 \<CC>) = tdghm_0 (op_dg \<CC>)"
  by
    (
      simp_all add:
        tdghm_0_def op_tdghm_def op_dg_def dg_0_def op_dghm_dghm_0 
        nt_field_simps dg_field_simps nat_omega_simps
    )


subsubsection\<open>Transformation map\<close>

lemma tdghm_0_NTMap_vsv[dg_cs_intros]: "vsv (tdghm_0 \<CC>\<lparr>NTMap\<rparr>)"
  unfolding tdghm_0_components by simp

lemma tdghm_0_NTMap_vdomain[dg_cs_simps]: "\<D>\<^sub>\<circ> (tdghm_0 \<CC>\<lparr>NTMap\<rparr>) = 0"
  unfolding tdghm_0_components by simp

lemma tdghm_0_NTMap_vrange[dg_cs_simps]: "\<R>\<^sub>\<circ> (tdghm_0 \<CC>\<lparr>NTMap\<rparr>) = 0"
  unfolding tdghm_0_components by simp


subsubsection\<open>
Empty transformation of digraph homomorphisms
is a transformation of digraph homomorphisms
\<close>

lemma (in digraph) dg_tdghm_0_is_tdghmI: 
  "tdghm_0 \<CC> : dghm_0 \<CC> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_0 \<CC> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_tdghmI)
  show "vfsequence (tdghm_0 \<CC>)" unfolding tdghm_0_def by simp
  show "vcard (tdghm_0 \<CC>) = 5\<^sub>\<nat>"
    unfolding tdghm_0_def by (simp add: nat_omega_simps)
  show "tdghm_0 \<CC>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : dghm_0 \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> dghm_0 \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> dg_0\<lparr>Obj\<rparr>" for a 
    using that unfolding dg_0_components by simp
qed 
  (
    cs_concl cs_shallow 
      cs_simp: dg_cs_simps dg_0_components(1) cs_intro: dg_cs_intros
  )+

lemma (in digraph) dg_tdghm_0_is_tdghmI'[dg_cs_intros]:
  assumes "\<FF>' = dghm_0 \<CC>"
    and "\<GG>' = dghm_0 \<CC>"
    and "\<AA>' = dg_0"
    and "\<BB>' = \<CC>"
    and "\<FF>' = \<FF>"
    and "\<GG>' = \<GG>"
  shows "tdghm_0 \<CC> : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule dg_tdghm_0_is_tdghmI)

lemmas [dg_cs_intros] = digraph.dg_tdghm_0_is_tdghmI'

lemma is_tdghm_is_tdghm_0_if_dg_0:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<NN> = tdghm_0 \<CC>" and "\<FF> = dghm_0 \<CC>" and "\<GG> = dghm_0 \<CC>"
proof-
  interpret \<NN>: is_tdghm \<alpha> dg_0 \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  show \<FF>_def: "\<FF> = dghm_0 \<CC>" and \<GG>_def: "\<GG> = dghm_0 \<CC>"
    by (auto intro: is_dghm_is_dghm_0_if_dg_0 dg_cs_intros)
  show "\<NN> = tdghm_0 \<CC>"
  proof(rule tdghm_eqI)
    show "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms(1))
    then have dom_lhs: "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = 0"
      by (cs_concl cs_simp: dg_cs_simps dg_0_components(1))
    show "tdghm_0 \<CC> : dghm_0 \<CC> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_0 \<CC> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: dg_cs_intros)
    then have dom_rhs: "\<D>\<^sub>\<circ> (tdghm_0 \<CC>\<lparr>NTMap\<rparr>) = 0"
      by (cs_concl cs_simp: dg_cs_simps dg_0_components(1))
    show "\<NN>\<lparr>NTMap\<rparr> = tdghm_0 \<CC>\<lparr>NTMap\<rparr>"
      by (rule vsv_eqI, unfold dom_lhs dom_rhs) (auto intro: dg_cs_intros)
  qed (auto simp: \<FF>_def \<GG>_def)
qed



subsection\<open>\<open>10\<close>: digraph with one object and no arrows\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dg_10 :: "V \<Rightarrow> V"
  where "dg_10 \<aa> = [set {\<aa>}, 0, 0, 0]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_10_components:
  shows "dg_10 \<aa>\<lparr>Obj\<rparr> = set {\<aa>}"
    and "dg_10 \<aa>\<lparr>Arr\<rparr> = 0"
    and "dg_10 \<aa>\<lparr>Dom\<rparr> = 0"
    and "dg_10 \<aa>\<lparr>Cod\<rparr> = 0"
  unfolding dg_10_def dg_field_simps by (auto simp: nat_omega_simps)


subsubsection\<open>\<open>10\<close> is a digraph\<close>

lemma (in \<Z>) digraph_dg_10: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "digraph \<alpha> (dg_10 \<aa>)"
proof(intro digraphI)
  show "vfsequence (dg_10 \<aa>)" unfolding dg_10_def by (simp add: nat_omega_simps)
  show "vcard (dg_10 \<aa>) = 4\<^sub>\<nat>" unfolding dg_10_def by (simp add: nat_omega_simps)
  show "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B. Hom (dg_10 \<aa>) a' b') \<in>\<^sub>\<circ> Vset \<alpha>" for A B
  proof-
    have "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B. Hom (dg_10 \<aa>) a' b') \<subseteq>\<^sub>\<circ> dg_10 \<aa>\<lparr>Arr\<rparr>" by auto
    moreover have "dg_10 \<aa>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> 0" unfolding dg_10_components by auto
    ultimately show ?thesis using vempty_is_zet vsubset_in_VsetI by presburger
  qed
qed (auto simp: assms dg_10_components vsubset_vsingleton_leftI)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_10_is_arr_iff: "\<FF> : \<AA> \<mapsto>\<^bsub>dg_10 \<aa>\<^esub> \<BB> \<longleftrightarrow> False"
  unfolding is_arr_def dg_10_components by simp



subsection\<open>\<open>1\<close>: digraph with one object and one arrow\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dg_1 :: "V \<Rightarrow> V \<Rightarrow> V"
  where "dg_1 \<aa> \<ff> = [set {\<aa>}, set {\<ff>}, set {\<langle>\<ff>, \<aa>\<rangle>}, set {\<langle>\<ff>, \<aa>\<rangle>}]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_1_components:
  shows "dg_1 \<aa> \<ff>\<lparr>Obj\<rparr> = set {\<aa>}"
    and "dg_1 \<aa> \<ff>\<lparr>Arr\<rparr> = set {\<ff>}"
    and "dg_1 \<aa> \<ff>\<lparr>Dom\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
    and "dg_1 \<aa> \<ff>\<lparr>Cod\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
  unfolding dg_1_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>\<open>1\<close> is a digraph\<close>

lemma (in \<Z>) digraph_dg_1: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "digraph \<alpha> (dg_1 \<aa> \<ff>)"
proof(intro digraphI)
  show "vfsequence (dg_1 \<aa> \<ff>)" unfolding dg_1_def by (simp add: nat_omega_simps)
  show "vcard (dg_1 \<aa> \<ff>) = 4\<^sub>\<nat>" unfolding dg_1_def by (simp add: nat_omega_simps)
  show "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B. Hom (dg_1 \<aa> \<ff>) a' b') \<in>\<^sub>\<circ> Vset \<alpha>" for A B
  proof-
    have "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B. Hom (dg_1 \<aa> \<ff>) a' b') \<subseteq>\<^sub>\<circ> dg_1 \<aa> \<ff>\<lparr>Arr\<rparr>" by auto
    moreover have "dg_1 \<aa> \<ff>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> set {\<ff>}" unfolding dg_1_components by auto
    moreover from assms(2) have "set {\<ff>} \<in>\<^sub>\<circ> Vset \<alpha>" 
      by (simp add: Limit_vsingleton_in_VsetI)
    ultimately show ?thesis 
      unfolding dg_1_components by (auto simp: vsubset_in_VsetI)
  qed
qed (auto simp: assms dg_1_components vsubset_vsingleton_leftI)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_1_is_arrI:
  assumes "a = \<aa>" and "b = \<aa>" and "f = \<ff>" 
  shows "f : a \<mapsto>\<^bsub>dg_1 \<aa> \<ff>\<^esub> b"
  using assms by (intro is_arrI) (auto simp: dg_1_components)

lemma dg_1_is_arrD:
  assumes "f : a \<mapsto>\<^bsub>dg_1 \<aa> \<ff>\<^esub> b"
  shows "a = \<aa>" and "b = \<aa>" and "f = \<ff>" 
  using assms by (all\<open>elim is_arrE\<close>) (auto simp: dg_1_components)

lemma dg_1_is_arrE:
  assumes "f : a \<mapsto>\<^bsub>dg_1 \<aa> \<ff>\<^esub> b"
  obtains "a = \<aa>" and "b = \<aa>" and "f = \<ff>" 
  using assms by (elim is_arrE) (force simp: dg_1_components)

lemma dg_1_is_arr_iff: "f : a \<mapsto>\<^bsub>dg_1 \<aa> \<ff>\<^esub> b \<longleftrightarrow> (a = \<aa> \<and> b = \<aa> \<and> f = \<ff>)" 
  by (rule iffI; (elim is_arrE)?) 
    (auto simp: dg_1_components intro: dg_1_is_arrI)

text\<open>\newpage\<close>

end