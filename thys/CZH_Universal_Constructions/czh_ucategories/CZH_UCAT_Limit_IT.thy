(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Initial and terminal objects as limits and colimits\<close>
theory CZH_UCAT_Limit_IT
  imports 
    CZH_UCAT_Limit
    CZH_Elementary_Categories.CZH_ECAT_Comma
begin



subsection\<open>Initial and terminal objects as limits/colimits of an empty diagram\<close>


subsubsection\<open>Definition and elementary properties\<close>

text\<open>
See 
\<^cite>\<open>"noauthor_nlab_nodate"\<close>\footnote{
\url{https://ncatlab.org/nlab/show/initial+object}
}, \<^cite>\<open>"noauthor_nlab_nodate"\<close>\footnote{
\url{https://ncatlab.org/nlab/show/terminal+object}
} and Chapter X-1 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.
\<close>

locale is_cat_obj_empty_terminal = is_cat_limit \<alpha> cat_0 \<CC> \<open>cf_0 \<CC>\<close> z \<ZZ> 
  for \<alpha> \<CC> z \<ZZ>

syntax "_is_cat_obj_empty_terminal" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>1 0\<^sub>C\<^sub>F :/ 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51] 51)
translations "\<ZZ> : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>1 0\<^sub>C\<^sub>F : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_empty_terminal \<alpha> \<CC> z \<ZZ>"

locale is_cat_obj_empty_initial = is_cat_colimit \<alpha> cat_0 \<CC> \<open>cf_0 \<CC>\<close> z \<ZZ> 
  for \<alpha> \<CC> z \<ZZ>

syntax "_is_cat_obj_empty_initial" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ 0\<^sub>C\<^sub>F >\<^sub>C\<^sub>F\<^sub>.\<^sub>0 _ :/ 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51] 51)
translations "\<ZZ> : 0\<^sub>C\<^sub>F >\<^sub>C\<^sub>F\<^sub>.\<^sub>0 z : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_empty_initial \<alpha> \<CC> z \<ZZ>"


text\<open>Rules.\<close>

lemma (in is_cat_obj_empty_terminal) 
  is_cat_obj_empty_terminal_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "z' = z" and "\<CC>' = \<CC>" 
  shows "\<ZZ> : z' <\<^sub>C\<^sub>F\<^sub>.\<^sub>1 0\<^sub>C\<^sub>F : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_empty_terminal_axioms)

mk_ide rf is_cat_obj_empty_terminal_def
  |intro is_cat_obj_empty_terminalI|
  |dest is_cat_obj_empty_terminalD[dest]|
  |elim is_cat_obj_empty_terminalE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_empty_terminalD

lemma (in is_cat_obj_empty_initial) 
  is_cat_obj_empty_initial_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "z' = z" and "\<CC>' = \<CC>" 
  shows "\<ZZ> : 0\<^sub>C\<^sub>F >\<^sub>C\<^sub>F\<^sub>.\<^sub>0 z' : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_empty_initial_axioms)

mk_ide rf is_cat_obj_empty_initial_def
  |intro is_cat_obj_empty_initialI|
  |dest is_cat_obj_empty_initialD[dest]|
  |elim is_cat_obj_empty_initialE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_empty_initialD


text\<open>Duality.\<close>

lemma (in is_cat_obj_empty_terminal) is_cat_obj_empty_initial_op:
  "op_ntcf \<ZZ> : 0\<^sub>C\<^sub>F >\<^sub>C\<^sub>F\<^sub>.\<^sub>0 z : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_obj_empty_initialI)
    (
      cs_concl cs_shallow
        cs_simp: cat_op_simps op_cf_cf_0 cs_intro: cat_cs_intros cat_op_intros
    )

lemma (in is_cat_obj_empty_terminal) is_cat_obj_empty_initial_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<ZZ> : 0\<^sub>C\<^sub>F >\<^sub>C\<^sub>F\<^sub>.\<^sub>0 z : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_empty_initial_op)

lemmas [cat_op_intros] = is_cat_obj_empty_terminal.is_cat_obj_empty_initial_op'

lemma (in is_cat_obj_empty_initial) is_cat_obj_empty_terminal_op:
  "op_ntcf \<ZZ> : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>1 0\<^sub>C\<^sub>F : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_obj_empty_terminalI)
    (
      cs_concl cs_shallow
        cs_simp: cat_op_simps op_cf_cf_0 cs_intro: cat_cs_intros cat_op_intros
    )

lemma (in is_cat_obj_empty_initial) is_cat_obj_empty_terminal_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<ZZ> : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>1 0\<^sub>C\<^sub>F : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_empty_terminal_op)

lemmas [cat_op_intros] = is_cat_obj_empty_initial.is_cat_obj_empty_terminal_op'


text\<open>Elementary properties.\<close>

lemma (in is_cat_obj_empty_terminal) cat_oet_ntcf_0: "\<ZZ> = ntcf_0 \<CC>"
  by (rule is_ntcf_is_ntcf_0_if_cat_0)
    (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma (in is_cat_obj_empty_initial) cat_oei_ntcf_0: "\<ZZ> = ntcf_0 \<CC>"
  by (rule is_ntcf_is_ntcf_0_if_cat_0)
    (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)


subsubsection\<open>
Initial and terminal objects as limits/colimits of an empty diagram 
are initial and terminal objects
\<close>

lemma (in category) cat_obj_terminal_is_cat_obj_empty_terminal:
  assumes "obj_terminal \<CC> z"
  shows "ntcf_0 \<CC> : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>1 0\<^sub>C\<^sub>F : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  from assms have z: "z \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  from z have [cat_cs_simps]: "cf_const cat_0 \<CC> z = cf_0 \<CC>"
    by (intro is_functor_is_cf_0_if_cat_0) (cs_concl cs_intro: cat_cs_intros)
  note obj_terminalD = obj_terminalD[OF assms]

  show ?thesis
  proof
    (
      intro is_cat_obj_empty_terminalI is_cat_limitI is_cat_coneI, 
      unfold cat_cs_simps
    )
    show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> z \<and> u' = ntcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const cat_0 \<CC> f'"
      if "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e cf_0 \<CC> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" for u' r'
    proof-
      interpret u': is_cat_cone \<alpha> r' cat_0 \<CC> \<open>cf_0 \<CC>\<close> u' by (rule that)
      from z have [cat_cs_simps]: "cf_const cat_0 \<CC> r' = cf_0 \<CC>"
        by (intro is_functor_is_cf_0_if_cat_0) 
          (cs_concl cs_shallow cs_intro: cat_cs_intros)
      have u'_def: "u' = ntcf_0 \<CC>"
        by 
          (
            rule is_ntcf_is_ntcf_0_if_cat_0[
              OF u'.is_ntcf_axioms, unfolded cat_cs_simps
              ]
          )
      from obj_terminalD(2)[OF u'.cat_cone_obj] obtain f' 
        where f': "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> z"
          and f'_unique: "f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> z \<Longrightarrow> f'' = f'" 
        for f''
        by auto
      from f' have [cat_cs_simps]: "ntcf_const cat_0 \<CC> f' = ntcf_0 \<CC>"
        by (intro is_ntcf_is_ntcf_0_if_cat_0(1)) 
          (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show ?thesis
      proof(intro ex1I conjI; (elim conjE)?)
        show "u' = ntcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const cat_0 \<CC> f'"
          by
            (
              cs_concl cs_shallow
                cs_simp: u'_def cat_cs_simps cs_intro: cat_cs_intros
            )
        fix f'' assume prems: 
          "f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> z" "u' = ntcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const cat_0 \<CC> f''"
        show "f'' = f'" by (rule f'_unique[OF prems(1)])          
      qed (rule f')
    qed
  qed (cs_concl cs_simp: cat_cs_simps cs_intro: z cat_cs_intros)

qed

lemma (in category) cat_obj_initial_is_cat_obj_empty_initial:
  assumes "obj_initial \<CC> z"
  shows "ntcf_0 \<CC> : 0\<^sub>C\<^sub>F >\<^sub>C\<^sub>F\<^sub>.\<^sub>0 z : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  have z: "obj_terminal (op_cat \<CC>) z" unfolding cat_op_simps by (rule assms)
  show ?thesis
    by 
      (
        rule is_cat_obj_empty_terminal.is_cat_obj_empty_initial_op
          [
            OF category.cat_obj_terminal_is_cat_obj_empty_terminal[
              OF category_op z, folded op_ntcf_ntcf_0
              ], 
            unfolded cat_op_simps op_ntcf_ntcf_0
          ]
      )
qed

lemma (in is_cat_obj_empty_terminal) cat_oet_obj_terminal: "obj_terminal \<CC> z"
proof-
  show "obj_terminal \<CC> z"
  proof(rule obj_terminalI)
    fix a assume prems: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    have [cat_cs_simps]: "cf_const cat_0 \<CC> a = cf_0 \<CC>"
      by (rule is_functor_is_cf_0_if_cat_0)
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros prems)
    from prems have "ntcf_0 \<CC> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e cf_0 \<CC> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (intro is_cat_coneI)
        (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from cat_lim_ua_fo[OF this] obtain f' 
      where f': "f' : a \<mapsto>\<^bsub>\<CC>\<^esub> z"
        and "ntcf_0 \<CC> = \<ZZ> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const cat_0 \<CC> f'"
        and f'_unique: 
          "\<lbrakk> f'' : a \<mapsto>\<^bsub>\<CC>\<^esub> z; ntcf_0 \<CC> = \<ZZ> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const cat_0 \<CC> f'' \<rbrakk> \<Longrightarrow>
            f'' = f'"
      for f''
      by metis
    show "\<exists>!f'. f' : a \<mapsto>\<^bsub>\<CC>\<^esub> z"
    proof(intro ex1I)
      fix f'' assume prems': "f'' : a \<mapsto>\<^bsub>\<CC>\<^esub> z"
      from prems' have "ntcf_0 \<CC> = ntcf_0 \<CC> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const cat_0 \<CC> f''"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from f'_unique[OF prems', unfolded cat_oet_ntcf_0, OF this] 
      show "f'' = f'".
    qed (rule f')
  qed (rule cat_cone_obj)
qed

lemma (in is_cat_obj_empty_initial) cat_oei_obj_initial: "obj_initial \<CC> z"
  by 
    (
      rule is_cat_obj_empty_terminal.cat_oet_obj_terminal[
        OF is_cat_obj_empty_initial.is_cat_obj_empty_terminal_op[
          OF is_cat_obj_empty_initial_axioms
          ],
        unfolded cat_op_simps
        ]
    )

lemma (in category) cat_is_cat_obj_empty_terminal_obj_terminal_iff:
  "(ntcf_0 \<CC> : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>1 0\<^sub>C\<^sub>F : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>) \<longleftrightarrow> obj_terminal \<CC> z"
  using 
    cat_obj_terminal_is_cat_obj_empty_terminal
    is_cat_obj_empty_terminal.cat_oet_obj_terminal
  by auto

lemma (in category) cat_is_cat_obj_empty_initial_obj_initial_iff:
  "(ntcf_0 \<CC> : 0\<^sub>C\<^sub>F >\<^sub>C\<^sub>F\<^sub>.\<^sub>0 z : 0\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>) \<longleftrightarrow> obj_initial \<CC> z"
  using 
    cat_obj_initial_is_cat_obj_empty_initial
    is_cat_obj_empty_initial.cat_oei_obj_initial
  by auto



subsection\<open>Initial cone and terminal cocone\<close>


subsubsection\<open>Definitions and elementary properties\<close>

definition ntcf_initial :: "V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_initial \<CC> z =
    [
      (\<lambda>b\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. THE f. f : z \<mapsto>\<^bsub>\<CC>\<^esub> b),
      cf_const \<CC> \<CC> z,
      cf_id \<CC>,
      \<CC>,
      \<CC>
    ]\<^sub>\<circ>"

definition ntcf_terminal :: "V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_terminal \<CC> z =
    [
      (\<lambda>b\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. THE f. f : b \<mapsto>\<^bsub>\<CC>\<^esub> z),
      cf_id \<CC>,
      cf_const \<CC> \<CC> z,
      \<CC>,
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_initial_components:
  shows "ntcf_initial \<CC> z\<lparr>NTMap\<rparr> = (\<lambda>c\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. THE f. f : z \<mapsto>\<^bsub>\<CC>\<^esub> c)"
    and "ntcf_initial \<CC> z\<lparr>NTDom\<rparr> = cf_const \<CC> \<CC> z"
    and "ntcf_initial \<CC> z\<lparr>NTCod\<rparr> = cf_id \<CC>"
    and "ntcf_initial \<CC> z\<lparr>NTDGDom\<rparr> = \<CC>"
    and "ntcf_initial \<CC> z\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntcf_initial_def nt_field_simps 
  by (simp_all add: nat_omega_simps)

lemmas [cat_lim_cs_simps] = ntcf_initial_components(2-5)
    
lemma ntcf_terminal_components:
  shows "ntcf_terminal \<CC> z\<lparr>NTMap\<rparr> = (\<lambda>c\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. THE f. f : c \<mapsto>\<^bsub>\<CC>\<^esub> z)"
    and "ntcf_terminal \<CC> z\<lparr>NTDom\<rparr> = cf_id \<CC>"
    and "ntcf_terminal \<CC> z\<lparr>NTCod\<rparr> = cf_const \<CC> \<CC> z"
    and "ntcf_terminal \<CC> z\<lparr>NTDGDom\<rparr> = \<CC>"
    and "ntcf_terminal \<CC> z\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntcf_terminal_def nt_field_simps 
  by (simp_all add: nat_omega_simps)

lemmas [cat_lim_cs_simps] = ntcf_terminal_components(2-5)


text\<open>Duality.\<close>

lemma ntcf_initial_op[cat_op_simps]:
  "op_ntcf (ntcf_initial \<CC> z) = ntcf_terminal (op_cat \<CC>) z"
  unfolding 
    ntcf_initial_def ntcf_terminal_def op_ntcf_def 
    nt_field_simps cat_op_simps
  by (auto simp: nat_omega_simps cat_op_simps) 

lemma ntcf_cone_terminal_op[cat_op_simps]:
  "op_ntcf (ntcf_terminal \<CC> z) = ntcf_initial (op_cat \<CC>) z"
  unfolding 
    ntcf_initial_def ntcf_terminal_def op_ntcf_def 
    nt_field_simps cat_op_simps
  by (auto simp: nat_omega_simps cat_op_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_initial_components(1)
  |vsv ntcf_initial_vsv[cat_lim_cs_intros]|
  |vdomain ntcf_initial_vdomain[cat_lim_cs_simps]|
  |app ntcf_initial_app|

mk_VLambda ntcf_terminal_components(1)
  |vsv ntcf_terminal_vsv[cat_lim_cs_intros]|
  |vdomain ntcf_terminal_vdomain[cat_lim_cs_simps]|
  |app ntcf_terminal_app|

lemma (in category)
  assumes "obj_initial \<CC> z" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows ntcf_initial_NTMap_app_is_arr: 
    "ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and ntcf_initial_NTMap_app_unique: 
      "\<And>f'. f' : z \<mapsto>\<^bsub>\<CC>\<^esub> c \<Longrightarrow> f' = ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
proof-
  from obj_initialD(2)[OF assms(1,2)] obtain f
    where f: "f : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
      and f_unique: "f' : z \<mapsto>\<^bsub>\<CC>\<^esub> c \<Longrightarrow> f' = f" 
    for f'
    by auto
  show is_arr: "ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
  proof(cs_concl_step ntcf_initial_app, rule assms(2), rule theI)
    fix f' assume "f' : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
    from f_unique[OF this] show "f' = f".
  qed (rule f)
  fix f' assume "f' : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
  from f_unique[OF this, folded f_unique[OF is_arr]] 
  show "f' = ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr>".
qed

lemma (in category) ntcf_initial_NTMap_app_is_arr'[cat_lim_cs_intros]:
  assumes "obj_initial \<CC> z" 
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "\<CC>' = \<CC>" 
    and "z' = z"
    and "c' = c"
  shows "ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : z' \<mapsto>\<^bsub>\<CC>'\<^esub> c'"
  using assms(1,2) 
  unfolding assms(3-5) 
  by (rule ntcf_initial_NTMap_app_is_arr)

lemma (in category)
  assumes "obj_terminal \<CC> z" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows ntcf_terminal_NTMap_app_is_arr: 
    "ntcf_terminal \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> z"
    and ntcf_terminal_NTMap_app_unique: 
      "\<And>f'. f' : c \<mapsto>\<^bsub>\<CC>\<^esub> z \<Longrightarrow> f' = ntcf_terminal \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
proof-
  from obj_terminalD(2)[OF assms(1,2)] obtain f
    where f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> z"
      and f_unique: "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> z \<Longrightarrow> f' = f" 
    for f'
    by auto
  show is_arr: "ntcf_terminal \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> z"
  proof(cs_concl_step ntcf_terminal_app, rule assms(2), rule theI)
    fix f' assume "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> z"
    from f_unique[OF this] show "f' = f". 
  qed (rule f)
  fix f' assume "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> z"
  from f_unique[OF this, folded f_unique[OF is_arr]] 
  show "f' = ntcf_terminal \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr>".
qed

lemma (in category) ntcf_terminal_NTMap_app_is_arr'[cat_lim_cs_intros]:
  assumes "obj_terminal \<CC> z" 
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "\<CC>' = \<CC>" 
    and "z' = z"
    and "c' = c"
  shows "ntcf_terminal \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : c' \<mapsto>\<^bsub>\<CC>'\<^esub> z'"
  using assms(1,2) 
  unfolding assms(3-5) 
  by (rule ntcf_terminal_NTMap_app_is_arr)



subsection\<open>
Initial and terminal objects as limits/colimits of the identity functor
\<close>


subsubsection\<open>Definition and elementary properties\<close>

text\<open>
See 
\<^cite>\<open>"noauthor_nlab_nodate"\<close>\footnote{
\url{https://ncatlab.org/nlab/show/initial+object}
}, \<^cite>\<open>"noauthor_nlab_nodate"\<close>\footnote{
\url{https://ncatlab.org/nlab/show/terminal+object}
} and Chapter X-1 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.
\<close>

locale is_cat_obj_id_initial = is_cat_limit \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> z \<ZZ> for \<alpha> \<CC> z \<ZZ>

syntax "_is_cat_obj_id_initial" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>0 id\<^sub>C :/ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51] 51)
translations "\<ZZ> : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>0 id\<^sub>C : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_id_initial \<alpha> \<CC> z \<ZZ>"

locale is_cat_obj_id_terminal = is_cat_colimit \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> z \<ZZ> for \<alpha> \<CC> z \<ZZ>

syntax "_is_cat_obj_id_terminal" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ id\<^sub>C >\<^sub>C\<^sub>F\<^sub>.\<^sub>1 _ :/ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51] 51)
translations "\<ZZ> : id\<^sub>C >\<^sub>C\<^sub>F\<^sub>.\<^sub>1 z : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_id_terminal \<alpha> \<CC> z \<ZZ>"


text\<open>Rules.\<close>

lemma (in is_cat_obj_id_initial)
  is_cat_obj_id_initial_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "z' = z" and "\<CC>' = \<CC>" 
  shows "\<ZZ> : z' <\<^sub>C\<^sub>F\<^sub>.\<^sub>0 id\<^sub>C : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_id_initial_axioms)

mk_ide rf is_cat_obj_id_initial_def
  |intro is_cat_obj_id_initialI|
  |dest is_cat_obj_id_initialD[dest]|
  |elim is_cat_obj_id_initialE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_id_initialD

lemma (in is_cat_obj_id_terminal) 
  is_cat_obj_id_terminal_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "z' = z" and "\<CC>' = \<CC>" 
  shows "\<ZZ> : id\<^sub>C >\<^sub>C\<^sub>F\<^sub>.\<^sub>1 z' : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_id_terminal_axioms)

mk_ide rf is_cat_obj_id_terminal_def
  |intro is_cat_obj_id_terminalI|
  |dest is_cat_obj_id_terminalD[dest]|
  |elim is_cat_obj_id_terminalE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_id_terminalD


text\<open>Duality.\<close>

lemma (in is_cat_obj_id_initial) is_cat_obj_id_terminal_op:
  "op_ntcf \<ZZ> : id\<^sub>C >\<^sub>C\<^sub>F\<^sub>.\<^sub>1 z : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_obj_id_terminalI)
    (cs_concl cs_shallow cs_simp: cat_op_simps cs_intro: cat_op_intros)

lemma (in is_cat_obj_id_initial) is_cat_obj_id_terminal_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<ZZ> : id\<^sub>C >\<^sub>C\<^sub>F\<^sub>.\<^sub>1 z : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_id_terminal_op)

lemmas [cat_op_intros] = is_cat_obj_id_initial.is_cat_obj_id_terminal_op'

lemma (in is_cat_obj_id_terminal) is_cat_obj_id_initial_op:
  "op_ntcf \<ZZ> : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>0 id\<^sub>C : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_obj_id_initialI)
    (cs_concl cs_shallow cs_simp: cat_op_simps cs_intro: cat_op_intros)

lemma (in is_cat_obj_id_terminal) is_cat_obj_id_initial_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<ZZ> : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>0 id\<^sub>C : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_id_initial_op)

lemmas [cat_op_intros] = is_cat_obj_id_terminal.is_cat_obj_id_initial_op'


subsubsection\<open>
Initial and terminal objects as limits/colimits are initial and terminal objects
\<close>

lemma (in category) cat_obj_initial_is_cat_obj_id_initial:
  assumes "obj_initial \<CC> z"
  shows "ntcf_initial \<CC> z : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>0 id\<^sub>C : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_cat_obj_id_initialI is_cat_limitI)

  from assms have z: "z \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  note obj_initialD = obj_initialD[OF assms]

  show "ntcf_initial \<CC> z : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e cf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  proof(intro is_cat_coneI is_ntcfI', unfold cat_lim_cs_simps)
    show "vfsequence (ntcf_initial \<CC> z)"
      unfolding ntcf_initial_def by auto
    show "vcard (ntcf_initial \<CC> z) = 5\<^sub>\<nat>"
      unfolding ntcf_initial_def by (simp add: nat_omega_simps)
    show "ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
      cf_const \<CC> \<CC> z\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> cf_id \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for a
      using that assms(1)
      by
        (
          cs_concl 
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_lim_cs_intros
         )
    show 
      "ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> cf_const \<CC> \<CC> z\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        cf_id \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for a b f
    proof-
      from that assms(1) have 
        "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : z \<mapsto>\<^bsub>\<CC>\<^esub> b"
        by (cs_concl cs_intro: cat_cs_intros cat_lim_cs_intros)
      note [cat_cs_simps] = ntcf_initial_NTMap_app_unique[
          OF assms(1) cat_is_arrD(3)[OF that] this
          ]
      from that assms(1) show ?thesis
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_lim_cs_intros
          )
    qed
  qed (use z in \<open>cs_concl cs_intro: cat_cs_intros cat_lim_cs_intros\<close>)+
  then interpret i: is_cat_cone \<alpha> z \<CC> \<CC> \<open>cf_id \<CC>\<close> \<open>ntcf_initial \<CC> z\<close> .

  fix u r assume "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e cf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  then interpret u: is_cat_cone \<alpha> r \<CC> \<CC> \<open>cf_id \<CC>\<close> u .

  from obj_initialD(2)[OF u.cat_cone_obj] obtain f 
    where f: "f : z \<mapsto>\<^bsub>\<CC>\<^esub> r" and f_unique: "f' : z \<mapsto>\<^bsub>\<CC>\<^esub> r \<Longrightarrow> f' = f" for f' 
    by auto
  note u.cat_cone_Comp_commute[cat_cs_simps del]
  from u.ntcf_Comp_commute[OF f] f have "u\<lparr>NTMap\<rparr>\<lparr>r\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>z\<rparr>"
    by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

  show "\<exists>!f'.
    f' : r \<mapsto>\<^bsub>\<CC>\<^esub> z \<and>
    u = ntcf_initial \<CC> z \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<CC> \<CC> f'"
  proof(intro ex1I conjI; (elim conjE)?)
    from f show "u\<lparr>NTMap\<rparr>\<lparr>z\<rparr> : r \<mapsto>\<^bsub>\<CC>\<^esub> z"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "u = ntcf_initial \<CC> z \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<CC> \<CC> (u\<lparr>NTMap\<rparr>\<lparr>z\<rparr>)"
    proof(rule ntcf_eqI, rule u.is_ntcf_axioms)
      show "ntcf_initial \<CC> z \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<CC> \<CC> (u\<lparr>NTMap\<rparr>\<lparr>z\<rparr>) :
        cf_const \<CC> \<CC> r \<mapsto>\<^sub>C\<^sub>F cf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from z have dom_rhs: 
        "\<D>\<^sub>\<circ> ((ntcf_initial \<CC> z \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<CC> \<CC> (u\<lparr>NTMap\<rparr>\<lparr>z\<rparr>))\<lparr>NTMap\<rparr>) =
          \<CC>\<lparr>Obj\<rparr>" 
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "u\<lparr>NTMap\<rparr> =
        (ntcf_initial \<CC> z \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<CC> \<CC> (u\<lparr>NTMap\<rparr>\<lparr>z\<rparr>))\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold dom_rhs u.ntcf_NTMap_vdomain)
        fix c assume prems: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        then have ic: "ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        from u.ntcf_Comp_commute[OF ic] ic have [cat_cs_simps]: 
          "ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>z\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
          by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros) simp
        from prems z show "u\<lparr>NTMap\<rparr>\<lparr>c\<rparr> =
          (ntcf_initial \<CC> z \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<CC> \<CC> (u\<lparr>NTMap\<rparr>\<lparr>z\<rparr>))\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      qed (auto intro: cat_cs_intros)
    qed simp_all
    fix f' assume prems:
      "f' : r \<mapsto>\<^bsub>\<CC>\<^esub> z"
      "u = ntcf_initial \<CC> z \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<CC> \<CC> f'"
    from z have "ntcf_initial \<CC> z\<lparr>NTMap\<rparr>\<lparr>z\<rparr> : z \<mapsto>\<^bsub>\<CC>\<^esub> z"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros) 
    note [cat_cs_simps] = cat_obj_initial_CId[OF assms this, symmetric]
    from prems(2) have
      "u\<lparr>NTMap\<rparr>\<lparr>z\<rparr> = (ntcf_initial \<CC> z \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<CC> \<CC> f')\<lparr>NTMap\<rparr>\<lparr>z\<rparr>"
      by simp
    from this prems(1) show "f' = u\<lparr>NTMap\<rparr>\<lparr>z\<rparr>"
      by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros) simp
  qed
qed

lemma (in category) cat_obj_terminal_is_cat_obj_id_terminal:
  assumes "obj_terminal \<CC> z"
  shows "ntcf_terminal \<CC> z : id\<^sub>C >\<^sub>C\<^sub>F\<^sub>.\<^sub>1 z : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  by 
    (
      rule is_cat_obj_id_initial.is_cat_obj_id_terminal_op
        [
          OF category.cat_obj_initial_is_cat_obj_id_initial[
            OF category_op op_cat_obj_initial[THEN iffD2, OF assms(1)]
            ],
          unfolded cat_op_simps
        ]
    )

lemma cat_cone_CId_obj_initial:
  assumes "\<ZZ> : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e cf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>z\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>z\<rparr>"
  shows "obj_initial \<CC> z"
proof(intro obj_initialI)
  interpret \<ZZ>: is_cat_cone \<alpha> z \<CC> \<CC> \<open>cf_id \<CC>\<close> \<ZZ> by (rule assms(1))
  show "z \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (cs_concl cs_intro: cat_cs_intros)
  fix c assume prems: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  show "\<exists>!f. f : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
  proof(intro ex1I)
    from prems show \<ZZ>c: "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    fix f assume prems': "f : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
    from \<ZZ>.ntcf_Comp_commute[OF prems'] prems' \<ZZ>c show "f = \<ZZ>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
      by (cs_prems cs_simp: cat_cs_simps assms(2) cs_intro: cat_cs_intros) simp
  qed
qed

lemma cat_cocone_CId_obj_terminal:
  assumes "\<ZZ> : cf_id \<CC> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e z : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>z\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>z\<rparr>"
  shows "obj_terminal \<CC> z"
proof-
  interpret \<ZZ>: is_cat_cocone \<alpha> z \<CC> \<CC> \<open>cf_id \<CC>\<close> \<ZZ> by (rule assms(1))
  show ?thesis
    by 
      (
        rule cat_cone_CId_obj_initial
          [
            OF \<ZZ>.is_cat_cone_op[unfolded cat_op_simps], 
            unfolded cat_op_simps, 
            OF assms(2)
          ]
      )
qed
 
lemma (in is_cat_obj_id_initial) cat_oii_obj_initial: "obj_initial \<CC> z"
proof(rule cat_cone_CId_obj_initial, rule is_cat_cone_axioms)
  from cat_lim_unique_cone'[OF is_cat_cone_axioms] obtain f 
    where f: "f : z \<mapsto>\<^bsub>\<CC>\<^esub> z"
      and \<ZZ>'j: "\<And>j. j \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<ZZ>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<ZZ>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
      and f_unique:
        "\<lbrakk>
          f' : z \<mapsto>\<^bsub>\<CC>\<^esub> z;
          \<And>j. j \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<ZZ>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<ZZ>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'
         \<rbrakk> \<Longrightarrow> f' = f"
    for f'
    by metis
  have CId_z: "\<CC>\<lparr>CId\<rparr>\<lparr>z\<rparr> : z \<mapsto>\<^bsub>\<CC>\<^esub> z"
    by (cs_concl cs_intro: cat_cs_intros)
  have "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<ZZ>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>z\<rparr>" if "j \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for j
    using that by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from f_unique[OF CId_z this] have CId_f: "\<CC>\<lparr>CId\<rparr>\<lparr>z\<rparr> = f" .
  have \<ZZ>z: "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>z\<rparr> : z \<mapsto>\<^bsub>\<CC>\<^esub> z"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  have "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> = \<ZZ>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ZZ>\<lparr>NTMap\<rparr>\<lparr>z\<rparr>" if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c
  proof-
    from that have \<ZZ>c: "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    note cat_cone_Comp_commute[cat_cs_simps del]
    from ntcf_Comp_commute[OF \<ZZ>c] \<ZZ>c show
      "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> = \<ZZ>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ZZ>\<lparr>NTMap\<rparr>\<lparr>z\<rparr>"
      by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed
  from f_unique[OF \<ZZ>z this] have "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>z\<rparr> = f" .
  with CId_f show "\<ZZ>\<lparr>NTMap\<rparr>\<lparr>z\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>z\<rparr>" by simp
qed

lemma (in is_cat_obj_id_terminal) cat_oit_obj_terminal: "obj_terminal \<CC> z"
  by 
    (
      rule is_cat_obj_id_initial.cat_oii_obj_initial[
        OF is_cat_obj_id_initial_op, unfolded cat_op_simps
        ]
    )

lemma (in category) cat_is_cat_obj_id_initial_obj_initial_iff:
  "(ntcf_initial \<CC> z : z <\<^sub>C\<^sub>F\<^sub>.\<^sub>0 id\<^sub>C : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>) \<longleftrightarrow> obj_initial \<CC> z"
  using 
    cat_obj_initial_is_cat_obj_id_initial
    is_cat_obj_id_initial.cat_oii_obj_initial
  by auto

lemma (in category) cat_is_cat_obj_id_terminal_obj_terminal_iff:
  "(ntcf_terminal \<CC> z : id\<^sub>C >\<^sub>C\<^sub>F\<^sub>.\<^sub>1 z : \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>) \<longleftrightarrow> obj_terminal \<CC> z"
  using 
    cat_obj_terminal_is_cat_obj_id_terminal
    is_cat_obj_id_terminal.cat_oit_obj_terminal
  by auto

text\<open>\newpage\<close>

end