(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Equalizers and coequalizers as limits and colimits\<close>
theory CZH_UCAT_Limit_Equalizer
  imports 
    CZH_UCAT_Limit
    CZH_Elementary_Categories.CZH_ECAT_Parallel
begin



subsection\<open>Equalizer and coequalizer\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
See \<^cite>\<open>"noauthor_wikipedia_2001"\<close>\footnote{
\url{https://en.wikipedia.org/wiki/Equaliser_(mathematics)}
}.
\<close>

locale is_cat_equalizer =
  is_cat_limit \<alpha> \<open>\<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F\<close> \<CC> \<open>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F'\<close> E \<epsilon> +
  F': vsv F'
  for \<alpha> \<aa> \<bb> F F' \<CC> E \<epsilon> +
  assumes cat_eq_F_in_Vset[cat_lim_cs_intros]: "F \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_eq_F_ne[cat_lim_cs_intros]: "F \<noteq> 0"
    and cat_eq_F'_vdomain[cat_lim_cs_simps]: "\<D>\<^sub>\<circ> F' = F"
    and cat_eq_F'_app_is_arr[cat_lim_cs_intros]: "\<ff> \<in>\<^sub>\<circ> F \<Longrightarrow> F'\<lparr>\<ff>\<rparr> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"

syntax "_is_cat_equalizer" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q '(_,_,_,_') :/ \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51] 51)
translations "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_equalizer \<alpha> \<aa> \<bb> F F' \<CC> E \<epsilon>"

locale is_cat_coequalizer =
  is_cat_colimit \<alpha> \<open>\<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F\<close> \<CC> \<open>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<bb> \<aa> F'\<close> E \<epsilon> +
  F': vsv F'
  for \<alpha> \<aa> \<bb> F F' \<CC> E \<epsilon> +
  assumes cat_coeq_F_in_Vset[cat_lim_cs_intros]: "F \<in>\<^sub>\<circ> Vset \<alpha>" 
    and cat_coeq_F_ne[cat_lim_cs_intros]: "F \<noteq> 0"
    and cat_coeq_F'_vdomain[cat_lim_cs_simps]: "\<D>\<^sub>\<circ> F' = F"
    and cat_coeq_F'_app_is_arr[cat_lim_cs_intros]: "\<ff> \<in>\<^sub>\<circ> F \<Longrightarrow> F'\<lparr>\<ff>\<rparr> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"

syntax "_is_cat_coequalizer" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ '(_,_,_,_') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q _ :/ \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51] 51)
translations "\<epsilon> : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_coequalizer \<alpha> \<aa> \<bb> F F' \<CC> E \<epsilon>"


text\<open>Rules.\<close>

lemma (in is_cat_equalizer) is_cat_equalizer_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "E' = E"
    and "\<aa>' = \<aa>"
    and "\<bb>' = \<bb>"
    and "F'' = F"
    and "F''' = F'"
    and "\<CC>' = \<CC>"
  shows "\<epsilon> : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>',\<bb>',F'',F''') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_equalizer_axioms)

mk_ide rf is_cat_equalizer_def[unfolded is_cat_equalizer_axioms_def]
  |intro is_cat_equalizerI|
  |dest is_cat_equalizerD[dest]|
  |elim is_cat_equalizerE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_equalizerD(1)

lemma (in is_cat_coequalizer) is_cat_coequalizer_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "E' = E"
    and "\<aa>' = \<aa>"
    and "\<bb>' = \<bb>"
    and "F'' = F"
    and "F''' = F'"
    and "\<CC>' = \<CC>"
  shows "\<epsilon> : (\<aa>',\<bb>',F'',F''') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_coequalizer_axioms)

mk_ide rf is_cat_coequalizer_def[unfolded is_cat_coequalizer_axioms_def]
  |intro is_cat_coequalizerI|
  |dest is_cat_coequalizerD[dest]|
  |elim is_cat_coequalizerE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_coequalizerD(1)


text\<open>Elementary properties.\<close>

lemma (in is_cat_equalizer) 
  cat_eq_\<aa>[cat_lim_cs_intros]: "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  and cat_eq_\<bb>[cat_lim_cs_intros]: "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  from cat_eq_F_ne obtain \<ff> where \<ff>: "\<ff> \<in>\<^sub>\<circ> F" by force
  have "F'\<lparr>\<ff>\<rparr> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>" by (rule cat_eq_F'_app_is_arr[OF \<ff>])
  then show "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
qed

lemma (in is_cat_coequalizer) 
  cat_coeq_\<aa>[cat_lim_cs_intros]: "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  and cat_coeq_\<bb>[cat_lim_cs_intros]: "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  from cat_coeq_F_ne obtain \<ff> where \<ff>: "\<ff> \<in>\<^sub>\<circ> F" by force
  have "F'\<lparr>\<ff>\<rparr> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" by (rule cat_coeq_F'_app_is_arr[OF \<ff>])
  then show "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
qed

sublocale is_cat_equalizer \<subseteq> cf_parallel \<alpha> \<open>\<aa>\<^sub>P\<^sub>L F\<close> \<open>\<bb>\<^sub>P\<^sub>L F\<close> F \<aa> \<bb> F' \<CC>
  by (intro cf_parallelI cat_parallelI)
    (
      auto simp:
        cat_lim_cs_simps cat_parallel_cs_intros cat_lim_cs_intros cat_cs_intros
    )

sublocale is_cat_coequalizer \<subseteq> cf_parallel \<alpha> \<open>\<bb>\<^sub>P\<^sub>L F\<close> \<open>\<aa>\<^sub>P\<^sub>L F\<close> F \<bb> \<aa> F' \<CC>
  by (intro cf_parallelI cat_parallelI)
    (
      auto simp:
        cat_lim_cs_simps cat_parallel_cs_intros cat_lim_cs_intros cat_cs_intros
    )


text\<open>Duality.\<close>

lemma (in is_cat_equalizer) is_cat_coequalizer_op:
  "op_ntcf \<epsilon> : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_coequalizerI)
    (
      cs_concl 
        cs_simp: cat_lim_cs_simps cat_op_simps 
        cs_intro: V_cs_intros cat_op_intros cat_lim_cs_intros
    )+

lemma (in is_cat_equalizer) is_cat_coequalizer_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<epsilon> : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_coequalizer_op)

lemmas [cat_op_intros] = is_cat_equalizer.is_cat_coequalizer_op'

lemma (in is_cat_coequalizer) is_cat_equalizer_op:
  "op_ntcf \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_equalizerI)
    (
      cs_concl 
        cs_simp: cat_lim_cs_simps cat_op_simps
        cs_intro: V_cs_intros cat_op_intros cat_lim_cs_intros
    )+

lemma (in is_cat_coequalizer) is_cat_equalizer_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_equalizer_op)

lemmas [cat_op_intros] = is_cat_coequalizer.is_cat_equalizer_op'


text\<open>Further properties.\<close>

lemma (in category) cat_cf_parallel_\<aa>\<bb>:
  assumes "vsv F'"
    and "F \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<D>\<^sub>\<circ> F' = F"
    and "\<And>\<ff>. \<ff> \<in>\<^sub>\<circ> F \<Longrightarrow> F'\<lparr>\<ff>\<rparr> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "cf_parallel \<alpha> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F' \<CC>"
proof-
  have "\<aa>\<^sub>P\<^sub>L F \<in>\<^sub>\<circ> Vset \<alpha>" "\<bb>\<^sub>P\<^sub>L F \<in>\<^sub>\<circ> Vset \<alpha>"
    by (simp_all add: Axiom_of_Pairing \<bb>\<^sub>P\<^sub>L_def \<aa>\<^sub>P\<^sub>L_def assms(2))
  then show ?thesis
    by (intro cf_parallelI cat_parallelI)
      (simp_all add: assms cat_parallel_cs_intros cat_cs_intros)
qed

lemma (in category) cat_cf_parallel_\<bb>\<aa>:
  assumes "vsv F'"
    and "F \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<D>\<^sub>\<circ> F' = F"
    and "\<And>\<ff>. \<ff> \<in>\<^sub>\<circ> F \<Longrightarrow> F'\<lparr>\<ff>\<rparr> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "cf_parallel \<alpha> (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<bb> \<aa> F' \<CC>"
proof-
  have "\<aa>\<^sub>P\<^sub>L F \<in>\<^sub>\<circ> Vset \<alpha>" "\<bb>\<^sub>P\<^sub>L F \<in>\<^sub>\<circ> Vset \<alpha>"
    by (simp_all add: Axiom_of_Pairing \<bb>\<^sub>P\<^sub>L_def \<aa>\<^sub>P\<^sub>L_def assms(2))
  then show ?thesis
    by (intro cf_parallelI cat_parallelI)
      (simp_all add: assms cat_parallel_cs_intros cat_cs_intros)
qed

lemma cat_cone_cf_par_eps_NTMap_app:
  assumes "\<epsilon> :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F' :
    \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "vsv F'"
    and "F \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<D>\<^sub>\<circ> F' = F"
    and "\<And>\<ff>. \<ff> \<in>\<^sub>\<circ> F \<Longrightarrow> F'\<lparr>\<ff>\<rparr> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<ff> \<in>\<^sub>\<circ> F"
  shows "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> = F'\<lparr>\<ff>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>" 
proof-
  let ?II = \<open>\<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F\<close> 
    and ?II_II = \<open>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F'\<close>
  interpret \<epsilon>: is_cat_cone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  from assms(5,6) have \<aa>: "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and \<bb>: "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  interpret par: cf_parallel \<alpha> \<open>\<aa>\<^sub>P\<^sub>L F\<close> \<open>\<bb>\<^sub>P\<^sub>L F\<close> F \<aa> \<bb> F' \<CC> 
    by (intro \<epsilon>.NTDom.HomCod.cat_cf_parallel_\<aa>\<bb> assms \<aa> \<bb>)
  from assms(6) have \<ff>: "\<ff> : \<aa>\<^sub>P\<^sub>L F \<mapsto>\<^bsub>\<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F\<^esub> \<bb>\<^sub>P\<^sub>L F" 
    by (simp_all add: par.the_cat_parallel_is_arr_\<aa>\<bb>F)
  note \<epsilon>.cat_cone_Comp_commute[cat_cs_simps del]
  from \<epsilon>.ntcf_Comp_commute[OF \<ff>] assms(6) show ?thesis
    by
      (
        cs_prems 
          cs_simp: cat_parallel_cs_simps cat_cs_simps
          cs_intro: cat_cs_intros cat_parallel_cs_intros
      )
qed

lemma cat_cocone_cf_par_eps_NTMap_app:
  assumes "\<epsilon> :
    \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<bb> \<aa> F' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E :
    \<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "vsv F'"
    and "F \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<D>\<^sub>\<circ> F' = F"
    and "\<And>\<ff>. \<ff> \<in>\<^sub>\<circ> F \<Longrightarrow> F'\<lparr>\<ff>\<rparr> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "\<ff> \<in>\<^sub>\<circ> F"
  shows "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> F'\<lparr>\<ff>\<rparr>"
proof-
  let ?II = \<open>\<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F\<close> 
    and ?II_II = \<open>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<bb> \<aa> F'\<close>
  interpret \<epsilon>: is_cat_cocone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  from assms(5,6) 
  have \<aa>: "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and \<bb>: "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and F'\<ff>: "F'\<lparr>\<ff>\<rparr> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" 
    by auto
  interpret par: cf_parallel \<alpha> \<open>\<bb>\<^sub>P\<^sub>L F\<close> \<open>\<aa>\<^sub>P\<^sub>L F\<close> F \<bb> \<aa> F' \<CC>
    by (intro \<epsilon>.NTDom.HomCod.cat_cf_parallel_\<bb>\<aa> assms \<aa> \<bb>)
  note \<epsilon>_NTMap_app = 
    cat_cone_cf_par_eps_NTMap_app[
      OF \<epsilon>.is_cat_cone_op[unfolded cat_op_simps],
      unfolded cat_op_simps,  
      OF assms(2-6),
      simplified
      ]
  from \<epsilon>_NTMap_app F'\<ff> show ?thesis
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_parallel_cs_simps category.op_cat_Comp[symmetric] 
          cs_intro: cat_cs_intros cat_parallel_cs_intros
      )
qed

lemma (in is_cat_equalizer) cat_eq_eps_NTMap_app:
  assumes "\<ff> \<in>\<^sub>\<circ> F"
  shows "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> = F'\<lparr>\<ff>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>" 
  by 
    (
      intro cat_cone_cf_par_eps_NTMap_app[
        OF 
          is_cat_cone_axioms 
          F'.vsv_axioms 
          cat_eq_F_in_Vset 
          cat_eq_F'_vdomain
          cat_eq_F'_app_is_arr
          assms
        ]
    )+

lemma (in is_cat_coequalizer) cat_coeq_eps_NTMap_app:
  assumes "\<ff> \<in>\<^sub>\<circ> F"
  shows "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> F'\<lparr>\<ff>\<rparr>" 
  by 
    (
      intro cat_cocone_cf_par_eps_NTMap_app[
        OF is_cat_cocone_axioms
          F'.vsv_axioms 
          cat_coeq_F_in_Vset 
          cat_coeq_F'_vdomain
          cat_coeq_F'_app_is_arr
          assms
        ]
    )+

lemma (in is_cat_equalizer) cat_eq_Comp_eq: 
  assumes "\<gg> \<in>\<^sub>\<circ> F" and "\<ff> \<in>\<^sub>\<circ> F"
  shows "F'\<lparr>\<gg>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = F'\<lparr>\<ff>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>"
  using cat_eq_eps_NTMap_app[OF assms(1)] cat_eq_eps_NTMap_app[OF assms(2)]
  by auto

lemma (in is_cat_coequalizer) cat_coeq_Comp_eq: 
  assumes "\<gg> \<in>\<^sub>\<circ> F" and "\<ff> \<in>\<^sub>\<circ> F"
  shows "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> F'\<lparr>\<gg>\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> F'\<lparr>\<ff>\<rparr>"
  using cat_coeq_eps_NTMap_app[OF assms(1)] cat_coeq_eps_NTMap_app[OF assms(2)]
  by auto


subsubsection\<open>Universal property\<close>

lemma is_cat_equalizerI':
  assumes "\<epsilon> :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F' :
    \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "vsv F'"
    and "F \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<D>\<^sub>\<circ> F' = F"
    and "\<And>\<ff>. \<ff> \<in>\<^sub>\<circ> F \<Longrightarrow> F'\<lparr>\<ff>\<rparr> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<ff> \<in>\<^sub>\<circ> F" 
    and "\<And>\<epsilon>' E'. \<epsilon>' :
      E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F' :
      \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  shows "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  let ?II = \<open>\<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F\<close> 
    and ?II_II = \<open>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F'\<close>
  interpret \<epsilon>: is_cat_cone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  from assms(5,6) have \<aa>: "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and \<bb>: "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  interpret par: cf_parallel \<alpha> \<open>\<aa>\<^sub>P\<^sub>L F\<close> \<open>\<bb>\<^sub>P\<^sub>L F\<close> F \<aa> \<bb> F' \<CC>
    by (intro \<epsilon>.NTDom.HomCod.cat_cf_parallel_\<aa>\<bb> assms \<aa> \<bb>) simp
  
  show ?thesis
  proof(intro is_cat_equalizerI is_cat_limitI assms(1-3))
    fix u' r' assume prems: "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    interpret u': is_cat_cone \<alpha> r' ?II \<CC> ?II_II u' by (rule prems)
    from assms(7)[OF prems] obtain f'
      where f': "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E"
        and u'_NTMap_app_\<aa>: "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
        and unique_f': 
          "\<And>f''.
            \<lbrakk>
              f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E; 
              u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''
            \<rbrakk> \<Longrightarrow> f'' = f'"
      by metis
    show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'"
    proof(intro ex1I conjI; (elim conjE)?)
      show "u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'"
      proof(rule ntcf_eqI)
        show "u' : cf_const ?II \<CC> r' \<mapsto>\<^sub>C\<^sub>F ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
          by (rule u'.is_ntcf_axioms)
        from f' show "\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f' :
          cf_const ?II \<CC> r' \<mapsto>\<^sub>C\<^sub>F ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros )
        have dom_lhs: "\<D>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>) = ?II\<lparr>Obj\<rparr>"
          unfolding cat_cs_simps by simp
        from f' have dom_rhs:
          "\<D>\<^sub>\<circ> ((\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f')\<lparr>NTMap\<rparr>) = ?II\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        show "u'\<lparr>NTMap\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f')\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix a assume prems': "a \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>"
          note [cat_parallel_cs_simps] = 
            cat_cone_cf_par_eps_NTMap_app[
              OF u'.is_cat_cone_axioms assms(2-5), simplified
              ]
            cat_cone_cf_par_eps_NTMap_app[OF assms(1-5), simplified]
            u'_NTMap_app_\<aa>
          from prems' f' assms(6) show 
            "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by (elim the_cat_parallel_ObjE; simp only:)
              (
                cs_concl 
                  cs_simp: cat_parallel_cs_simps cat_cs_simps
                  cs_intro: cat_cs_intros cat_parallel_cs_intros
              )
        qed (cs_concl cs_intro: V_cs_intros cat_cs_intros)+
      qed simp_all
      fix f'' assume prems'': 
        "f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E" "u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f''"
      from prems''(2) have u'_NTMap_a:
        "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        for a 
        by simp
      have "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"  
        using u'_NTMap_a[of \<open>\<aa>\<^sub>P\<^sub>L F\<close>] prems''(1) 
        by 
          (
            cs_prems 
              cs_simp: cat_parallel_cs_simps cat_cs_simps 
              cs_intro: cat_parallel_cs_intros cat_cs_intros
          )
      from unique_f'[OF prems''(1) this] show "f'' = f'".
    qed (rule f')
  qed (use assms in fastforce)+

qed

lemma is_cat_coequalizerI':
  assumes "\<epsilon> :
    \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<bb> \<aa> F' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E : 
    \<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "vsv F'"
    and "F \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<D>\<^sub>\<circ> F' = F"
    and "\<And>\<ff>. \<ff> \<in>\<^sub>\<circ> F \<Longrightarrow> F'\<lparr>\<ff>\<rparr> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "\<ff> \<in>\<^sub>\<circ> F" 
    and "\<And>\<epsilon>' E'. \<epsilon>' :
      \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<bb> \<aa> F' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E' : 
      \<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>"
  shows "\<epsilon> : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  let ?op_II = \<open>\<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F\<close> 
    and ?op_II_II = \<open>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<bb> \<aa> F'\<close>
    and ?II = \<open>\<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F\<close>
    and ?II_II = \<open>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F (op_cat \<CC>) (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F'\<close>
  interpret \<epsilon>: is_cat_cocone \<alpha> E ?op_II \<CC> ?op_II_II \<epsilon> by (rule assms(1))
  from assms(5,6) have \<aa>: "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and \<bb>: "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  interpret par: cf_parallel \<alpha> \<open>\<bb>\<^sub>P\<^sub>L F\<close> \<open>\<aa>\<^sub>P\<^sub>L F\<close> F \<bb> \<aa> F' \<CC>
    by (intro \<epsilon>.NTDom.HomCod.cat_cf_parallel_\<bb>\<aa> assms \<aa> \<bb>) simp

  interpret op_par: cf_parallel \<alpha> \<open>\<aa>\<^sub>P\<^sub>L F\<close> \<open>\<bb>\<^sub>P\<^sub>L F\<close> F \<aa> \<bb> F' \<open>op_cat \<CC>\<close>
    by (rule par.cf_parallel_op)
  have assms_4':
    "\<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f'"
    if "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>" for \<epsilon>' E'
  proof-
    have [cat_op_simps]:
      "f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<longleftrightarrow>
        f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>"
      for f'
      by (intro iffI conjI; (elim conjE)?)
        (
          cs_concl cs_shallow
            cs_simp: category.op_cat_Comp[symmetric] cat_op_simps cat_cs_simps 
            cs_intro: cat_cs_intros cat_parallel_cs_intros
        )+
    interpret \<epsilon>': is_cat_cone \<alpha> E' ?II \<open>op_cat \<CC>\<close> ?II_II \<epsilon>' by (rule that)
    show ?thesis
      unfolding cat_op_simps
      by 
        (
          rule assms(7)[
            OF \<epsilon>'.is_cat_cocone_op[unfolded cat_op_simps], 
            unfolded cat_op_simps
            ]
        )
  qed
  interpret op_\<epsilon>: is_cat_equalizer \<alpha> \<aa> \<bb> F F' \<open>op_cat \<CC>\<close> E \<open>op_ntcf \<epsilon>\<close> 
    by 
      (
        rule 
          is_cat_equalizerI'
            [
              OF \<epsilon>.is_cat_cone_op[unfolded cat_op_simps], 
              unfolded cat_op_simps, 
              OF assms(2-6) assms_4',
              simplified
            ]
      )
  show ?thesis by (rule op_\<epsilon>.is_cat_coequalizer_op[unfolded cat_op_simps])

qed

lemma (in is_cat_equalizer) cat_eq_unique_cone:
  assumes "\<epsilon>' :
    E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F' : \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    (is \<open>\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>\<close>)
  shows "\<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-

  interpret \<epsilon>': is_cat_cone \<alpha> E' ?II \<CC> ?II_II \<epsilon>' by (rule assms(1))
  from cat_lim_ua_fo[OF assms(1)] obtain f' where f': "f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E"
    and \<epsilon>'_def: "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'"
    and unique: 
      "\<lbrakk> f'' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E; \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'' \<rbrakk> \<Longrightarrow> f'' = f'" 
    for f''
    by auto
  from cat_eq_F_ne obtain \<ff> where \<ff>: "\<ff> \<in>\<^sub>\<circ> F" by force

  show ?thesis
  proof(intro ex1I conjI; (elim conjE)?)
    show f': "f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E" by (rule f')
    from \<epsilon>'_def have "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f')\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>"
      by simp
    from this f' show \<epsilon>'_NTMap_app_I: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      by 
        (
          cs_prems 
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_parallel_cs_intros
        )
    fix f'' assume prems: 
      "f'' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E" "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
    have "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f''"
    proof(rule ntcf_eqI[OF ])
      show "\<epsilon>' : cf_const ?II \<CC> E' \<mapsto>\<^sub>C\<^sub>F ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (rule \<epsilon>'.is_ntcf_axioms)
      from f' prems(1) show "\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'' :
        cf_const ?II \<CC> E' \<mapsto>\<^sub>C\<^sub>F ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "\<epsilon>'\<lparr>NTMap\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold cat_cs_simps)
        show "vsv ((\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>)"
          by (cs_concl cs_intro: cat_cs_intros)
        from prems(1) show "?II\<lparr>Obj\<rparr> = \<D>\<^sub>\<circ> ((\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>)"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        fix a assume prems': "a \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>"
        note [cat_cs_simps] = 
          cat_eq_eps_NTMap_app[OF \<ff>]
          cat_cone_cf_par_eps_NTMap_app
            [
              OF 
                \<epsilon>'.is_cat_cone_axioms 
                F'.vsv_axioms 
                cat_eq_F_in_Vset 
                cat_eq_F'_vdomain 
                cat_eq_F'_app_is_arr \<ff>, 
              simplified
            ]
        from prems' prems(1) \<ff> have [cat_cs_simps]: 
          "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
          by (elim the_cat_parallel_ObjE; simp only:)
            (
                cs_concl 
                  cs_simp: cat_cs_simps cat_parallel_cs_simps prems(2)
                  cs_intro: cat_cs_intros cat_parallel_cs_intros
            )+
        from prems' prems show 
          "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      qed auto
    qed simp_all
    from unique[OF prems(1) this] show "f'' = f'" .
  qed

qed

lemma (in is_cat_equalizer) cat_eq_unique:
  assumes "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "\<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (\<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F) \<CC> f'"
  by (rule cat_lim_unique[OF is_cat_equalizerD(1)[OF assms]])

lemma (in is_cat_equalizer) cat_eq_unique':
  assumes "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  interpret \<epsilon>': is_cat_equalizer \<alpha> \<aa> \<bb> F F' \<CC> E' \<epsilon>' by (rule assms(1))
  show ?thesis by (rule cat_eq_unique_cone[OF \<epsilon>'.is_cat_cone_axioms])
qed

lemma (in is_cat_coequalizer) cat_coeq_unique_cocone:
  assumes "\<epsilon>' :
    \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<bb> \<aa> F' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E' : 
    \<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    (is \<open>\<epsilon>' : ?II_II >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E' : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>\<close>)
  shows "\<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>"
proof-
  interpret \<epsilon>': is_cat_cocone \<alpha> E' ?II \<CC> ?II_II \<epsilon>' by (rule assms(1))
  have [cat_op_simps]:
    "f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<longleftrightarrow>
      f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>" 
    for f'
    by (intro iffI conjI; (elim conjE)?)
      (
        cs_concl cs_shallow
          cs_simp: category.op_cat_Comp[symmetric] cat_op_simps cat_cs_simps 
          cs_intro: cat_cs_intros cat_parallel_cs_intros
      )+
  show ?thesis
    by 
      (
        rule is_cat_equalizer.cat_eq_unique_cone[
          OF is_cat_equalizer_op \<epsilon>'.is_cat_cone_op[unfolded cat_op_simps],
          unfolded cat_op_simps
          ]
     )
qed

lemma (in is_cat_coequalizer) cat_coeq_unique:
  assumes "\<epsilon>' : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>' = ntcf_const (\<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F) \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>"
  by (rule cat_colim_unique[OF is_cat_coequalizerD(1)[OF assms]])

lemma (in is_cat_coequalizer) cat_coeq_unique':
  assumes "\<epsilon>' : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>"
proof-
  interpret \<epsilon>': is_cat_coequalizer \<alpha> \<aa> \<bb> F F' \<CC> E' \<epsilon>' by (rule assms(1))
  show ?thesis by (rule cat_coeq_unique_cocone[OF \<epsilon>'.is_cat_cocone_axioms])
qed

lemma cat_equalizer_ex_is_iso_arr:
  assumes "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E"
    and "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (\<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F) \<CC> f"
proof-
  interpret \<epsilon>: is_cat_equalizer \<alpha> \<aa> \<bb> F F' \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_equalizer \<alpha> \<aa> \<bb> F F' \<CC> E' \<epsilon>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_lim_ex_is_iso_arr[
          OF \<epsilon>.is_cat_limit_axioms \<epsilon>'.is_cat_limit_axioms
          ]
      )
qed

lemma cat_equalizer_ex_is_iso_arr':
  assumes "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,F,F') : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E"
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  interpret \<epsilon>: is_cat_equalizer \<alpha> \<aa> \<bb> F F' \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_equalizer \<alpha> \<aa> \<bb> F F' \<CC> E' \<epsilon>' by (rule assms(2))
  obtain f where f: "f : E' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E"
    and "j \<in>\<^sub>\<circ> \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F\<lparr>Obj\<rparr> \<Longrightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" for j
    by 
      (
        elim cat_lim_ex_is_iso_arr'[
          OF \<epsilon>.is_cat_limit_axioms \<epsilon>'.is_cat_limit_axioms
          ]
      )
  then have 
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    unfolding the_cat_parallel_components by auto
  with f show ?thesis using that by simp
qed

lemma cat_coequalizer_ex_is_iso_arr:
  assumes "\<epsilon> : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon>' : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E'" 
    and "\<epsilon>' = ntcf_const (\<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F)  \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>"
proof-
  interpret \<epsilon>: is_cat_coequalizer \<alpha> \<aa> \<bb> F F' \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_coequalizer \<alpha> \<aa> \<bb> F F' \<CC> E' \<epsilon>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_colim_ex_is_iso_arr[
          OF \<epsilon>.is_cat_colimit_axioms \<epsilon>'.is_cat_colimit_axioms
          ]
      )
qed

lemma cat_coequalizer_ex_is_iso_arr':
  assumes "\<epsilon> : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon>' : (\<aa>,\<bb>,F,F') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E'" 
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>"
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr>"
proof-
  interpret \<epsilon>: is_cat_coequalizer \<alpha> \<aa> \<bb> F F' \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_coequalizer \<alpha> \<aa> \<bb> F F' \<CC> E' \<epsilon>' by (rule assms(2))
  obtain f where f: "f : E \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E'"
    and "j \<in>\<^sub>\<circ> \<Up>\<^sub>C (\<bb>\<^sub>P\<^sub>L F) (\<aa>\<^sub>P\<^sub>L F) F\<lparr>Obj\<rparr> \<Longrightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" for j
    by
      (
        elim cat_colim_ex_is_iso_arr'[
          OF \<epsilon>.is_cat_colimit_axioms \<epsilon>'.is_cat_colimit_axioms
          ]
      )
  then have 
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr>"
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L F\<rparr>"
    unfolding the_cat_parallel_components by auto
  with f show ?thesis using that by simp
qed


subsubsection\<open>Further properties\<close>

lemma (in is_cat_equalizer) cat_eq_is_monic_arr: 
  \<comment>\<open>See subsection 3.3 in \cite{awodey_category_2010}.\<close>
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> : E \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> \<aa>"
proof(intro is_monic_arrI)
  show "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> : E \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_parallel_cs_simps 
          cs_intro: cat_cs_intros cat_parallel_cs_intros
      )
  fix f g a
  assume prems:
    "f : a \<mapsto>\<^bsub>\<CC>\<^esub> E"
    "g : a \<mapsto>\<^bsub>\<CC>\<^esub> E"
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g"
  define \<epsilon>' where "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (\<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F) \<CC> f"
  from prems(1) have "\<epsilon>' :
    a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<aa> \<bb> F' :
    \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    unfolding \<epsilon>'_def 
    by (cs_concl cs_shallow cs_intro: is_cat_coneI cat_cs_intros)    
  from cat_eq_unique_cone[OF this] obtain f' 
    where f': "f' : a \<mapsto>\<^bsub>\<CC>\<^esub> E"
      and \<epsilon>'_\<aa>: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      and unique_f': "\<And>f''.
        \<lbrakk> f'' : a \<mapsto>\<^bsub>\<CC>\<^esub> E; \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'' \<rbrakk> \<Longrightarrow>
          f'' = f'"
    by meson
  from prems(1) have unique_f: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    unfolding \<epsilon>'_def
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_parallel_cs_intros
      )
  from prems(1) have unique_g: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g"
    unfolding \<epsilon>'_def
    by
      (
        cs_concl
          cs_simp: prems(3) cat_cs_simps
          cs_intro: cat_cs_intros cat_parallel_cs_intros
      )
  show "f = g"
    by 
      (
        rule unique_f'
          [
            OF prems(1) unique_f,
            unfolded unique_f'[OF prems(2) unique_g, symmetric]
          ]
      )
qed

lemma (in is_cat_coequalizer) cat_coeq_is_epic_arr: 
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L F\<rparr> : \<aa> \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> E"
  by
    (
      rule is_cat_equalizer.cat_eq_is_monic_arr[
        OF is_cat_equalizer_op, unfolded cat_op_simps
        ]
    )



subsection\<open>Equalizer and coequalizer for two arrows\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
See \<^cite>\<open>"noauthor_wikipedia_2001"\<close>\footnote{
\url{https://en.wikipedia.org/wiki/Equaliser_(mathematics)}
}.
\<close>

locale is_cat_equalizer_2 =
  is_cat_limit \<alpha> \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close> \<CC> \<open>\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<close> E \<epsilon> 
  for \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> +
  assumes cat_eq_\<gg>[cat_lim_cs_intros]: "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and cat_eq_\<ff>[cat_lim_cs_intros]: "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"

syntax "_is_cat_equalizer_2" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q '(_,_,_,_') :/ \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51] 51)
translations "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_equalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon>"

locale is_cat_coequalizer_2 =
  is_cat_colimit 
    \<alpha> \<open>\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L\<close> \<CC> \<open>\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg>\<close> E \<epsilon> 
  for \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> +
  assumes cat_coeq_\<gg>[cat_lim_cs_intros]: "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and cat_coeq_\<ff>[cat_lim_cs_intros]: "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"

syntax "_is_cat_coequalizer_2" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ '(_,_,_,_') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q _ :/ \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51] 51)
translations "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon>"


text\<open>Rules.\<close>

lemma (in is_cat_equalizer_2) is_cat_equalizer_2_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "E' = E"
    and "\<aa>' = \<aa>"
    and "\<bb>' = \<bb>"
    and "\<gg>' = \<gg>"
    and "\<ff>' = \<ff>"
    and "\<CC>' = \<CC>"
  shows "\<epsilon> : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>',\<bb>',\<gg>',\<ff>') : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_equalizer_2_axioms)

mk_ide rf is_cat_equalizer_2_def[unfolded is_cat_equalizer_2_axioms_def]
  |intro is_cat_equalizer_2I|
  |dest is_cat_equalizer_2D[dest]|
  |elim is_cat_equalizer_2E[elim]|

lemmas [cat_lim_cs_intros] = is_cat_equalizer_2D(1)

lemma (in is_cat_coequalizer_2) is_cat_coequalizer_2_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "E' = E"
    and "\<aa>' = \<aa>"
    and "\<bb>' = \<bb>"
    and "\<gg>' = \<gg>"
    and "\<ff>' = \<ff>"
    and "\<CC>' = \<CC>"
  shows "\<epsilon> : (\<aa>',\<bb>',\<gg>',\<ff>') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_coequalizer_2_axioms)

mk_ide rf is_cat_coequalizer_2_def[unfolded is_cat_coequalizer_2_axioms_def]
  |intro is_cat_coequalizer_2I|
  |dest is_cat_coequalizer_2D[dest]|
  |elim is_cat_coequalizer_2E[elim]|

lemmas [cat_lim_cs_intros] = is_cat_coequalizer_2D(1)


text\<open>Helper lemmas.\<close>

(*FIXME*)
lemma cat_eq_F'_helper:
  "(\<lambda>f\<in>\<^sub>\<circ>set {\<ff>\<^sub>P\<^sub>L, \<gg>\<^sub>P\<^sub>L}. (f = \<gg>\<^sub>P\<^sub>L ? \<gg> : \<ff>)) =
    (\<lambda>f\<in>\<^sub>\<circ>set {\<ff>\<^sub>P\<^sub>L, \<gg>\<^sub>P\<^sub>L}. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))"
  using cat_PL2_\<gg>\<ff> by (simp add: VLambda_vdoubleton)


text\<open>Elementary properties.\<close>

sublocale is_cat_equalizer_2 \<subseteq> cf_parallel_2 \<alpha> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<CC> 
  by (intro cf_parallel_2I cat_parallel_2I)
    (simp_all add: cat_parallel_cs_intros cat_lim_cs_intros cat_cs_intros)

sublocale is_cat_coequalizer_2 \<subseteq> cf_parallel_2 \<alpha> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> \<CC>
  by (intro cf_parallel_2I cat_parallel_2I)
    (
      auto simp: 
        cat_parallel_cs_intros cat_lim_cs_intros cat_cs_intros 
        cat_PL2_ineq[symmetric]
    )

lemma (in is_cat_equalizer_2) cat_equalizer_2_is_cat_equalizer:
  "\<epsilon> :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L},(\<lambda>f\<in>\<^sub>\<circ>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))) : 
    \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  by 
    (
      intro is_cat_equalizerI, 
      rule is_cat_limit_axioms[
        unfolded the_cf_parallel_2_def the_cat_parallel_2_def \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def
        ]
    ) 
    (auto simp: Limit_vdoubleton_in_VsetI cat_parallel_cs_intros)

lemma (in is_cat_coequalizer_2) cat_coequalizer_2_is_cat_coequalizer:
  "\<epsilon> :
    (\<aa>,\<bb>,set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L},(\<lambda>f\<in>\<^sub>\<circ>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E :
    \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof
  (
    intro is_cat_coequalizerI, 
    fold the_cf_parallel_2_def the_cat_parallel_2_def \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def
  )
  show "\<epsilon> :
    \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<bb> \<aa> \<gg> \<ff> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m E :
    \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by 
      (
        subst the_cat_parallel_2_commute, 
        subst cf_parallel_2_the_cf_parallel_2_commute[symmetric]
      )
      (intro is_cat_colimit_axioms)
qed (auto simp: Limit_vdoubleton_in_VsetI cat_parallel_cs_intros)

lemma cat_equalizer_is_cat_equalizer_2:
  assumes "\<epsilon> :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L},(\<lambda>f\<in>\<^sub>\<circ>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))) :
    \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<epsilon>: is_cat_equalizer 
    \<alpha> \<aa> \<bb> \<open>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}\<close> \<open>(\<lambda>f\<in>\<^sub>\<circ>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))\<close> \<CC> E \<epsilon>
    by (rule assms)
  have \<ff>\<^sub>P\<^sub>L: "\<ff>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}" and \<gg>\<^sub>P\<^sub>L: "\<gg>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}" by auto
  show ?thesis
    using \<epsilon>.cat_eq_F'_app_is_arr[OF \<gg>\<^sub>P\<^sub>L] \<epsilon>.cat_eq_F'_app_is_arr[OF \<ff>\<^sub>P\<^sub>L] 
    by 
      (
        intro 
          is_cat_equalizer_2I 
          \<epsilon>.is_cat_limit_axioms
            [
              folded 
                the_cf_parallel_2_def the_cat_parallel_2_def \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def
            ]
      )
      (auto simp: cat_PL2_\<gg>\<ff>)
qed

lemma cat_coequalizer_is_cat_coequalizer_2:
  assumes "\<epsilon> :
    (\<aa>,\<bb>,set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L},(\<lambda>f\<in>\<^sub>\<circ>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E :
    \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret is_cat_coequalizer 
    \<alpha> \<aa> \<bb> \<open>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}\<close> \<open>(\<lambda>f\<in>\<^sub>\<circ>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))\<close> \<CC> E \<epsilon>
    by (rule assms)
  interpret cf_parallel_2 \<alpha> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<bb> \<aa> \<gg> \<ff> \<CC>
    by 
      (
        rule cf_parallel_is_cf_parallel_2[
          OF cf_parallel_axioms cat_PL2_\<gg>\<ff>, folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def
          ]
      )
  show "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by
      (
        intro is_cat_coequalizer_2I, 
        subst the_cat_parallel_2_commute, 
        subst cf_parallel_2_the_cf_parallel_2_commute[symmetric], 
        rule is_cat_colimit_axioms[
          folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def the_cat_parallel_2_def the_cf_parallel_2_def
          ]
      )
      (simp_all add: cf_parallel_\<ff>' cf_parallel_\<gg>')
qed


text\<open>Duality.\<close>

lemma (in is_cat_equalizer_2) is_cat_coequalizer_2_op:
  "op_ntcf \<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  unfolding is_cat_equalizer_def
  by 
    (
      rule cat_coequalizer_is_cat_coequalizer_2
        [
          OF is_cat_equalizer.is_cat_coequalizer_op[
            OF cat_equalizer_2_is_cat_equalizer
          ]
        ]
    )

lemma (in is_cat_equalizer_2) is_cat_coequalizer_2_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_coequalizer_2_op)

lemmas [cat_op_intros] = is_cat_equalizer_2.is_cat_coequalizer_2_op'

lemma (in is_cat_coequalizer_2) is_cat_equalizer_2_op:
  "op_ntcf \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  unfolding is_cat_coequalizer_def
  by 
    (
      rule cat_equalizer_is_cat_equalizer_2
        [
          OF is_cat_coequalizer.is_cat_equalizer_op[
            OF cat_coequalizer_2_is_cat_coequalizer
          ]
        ]
    )

lemma (in is_cat_coequalizer_2) is_cat_equalizer_2_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_equalizer_2_op)

lemmas [cat_op_intros] = is_cat_coequalizer_2.is_cat_equalizer_2_op'


text\<open>Further properties.\<close>

lemma (in category) cat_cf_parallel_2_cat_equalizer: 
  assumes "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>" and "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
  shows "cf_parallel_2 \<alpha> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<CC>"
  using assms 
  by (intro cf_parallel_2I cat_parallel_2I)
    (auto simp: cat_parallel_cs_intros cat_cs_intros)

lemma (in category) cat_cf_parallel_2_cat_coequalizer: 
  assumes "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" and "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
  shows "cf_parallel_2 \<alpha> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> \<CC>"
  using assms 
  by (intro cf_parallel_2I cat_parallel_2I)
    (simp_all add: cat_parallel_cs_intros cat_cs_intros cat_PL2_ineq[symmetric])

lemma cat_cone_cf_par_2_eps_NTMap_app:
  assumes "\<epsilon> :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>" 
    and "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
  shows 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>" 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
proof-
  let ?II = \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close> 
    and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<close>
    and ?F = \<open>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}\<close>
  interpret \<epsilon>: is_cat_cone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  from \<epsilon>.cat_PL2_\<ff> \<epsilon>.cat_PL2_\<gg> have \<gg>\<ff>: "?F \<in>\<^sub>\<circ> Vset \<alpha>"
    by (intro Limit_vdoubleton_in_VsetI)  auto
  from assms(2,3) have
    "(\<And>\<ff>'. \<ff>' \<in>\<^sub>\<circ> ?F \<Longrightarrow> (\<lambda>f\<in>\<^sub>\<circ>?F. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))\<lparr>\<ff>'\<rparr> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>)"
    by auto
  note cat_cone_cf_par_eps_NTMap_app = cat_cone_cf_par_eps_NTMap_app
      [
        OF 
          assms(1)[
            unfolded 
              the_cat_parallel_2_def the_cf_parallel_2_def \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def
            ], 
        folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def, OF _ \<gg>\<ff> _ this,
        simplified
      ]
  from
    cat_cone_cf_par_eps_NTMap_app[of \<gg>\<^sub>P\<^sub>L, simplified]
    cat_cone_cf_par_eps_NTMap_app[of \<ff>\<^sub>P\<^sub>L, simplified]
    cat_PL2_\<gg>\<ff>
  show 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>" 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
    by fastforce+
qed

lemma cat_cocone_cf_par_2_eps_NTMap_app:
  assumes "\<epsilon> :
    \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E :
    \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" 
    and "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
  shows 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>" 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"    
proof-
  let ?II = \<open>\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L\<close> 
    and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg>\<close>
    and ?F = \<open>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}\<close>
  have \<ff>\<gg>_\<gg>\<ff>: "{\<ff>\<^sub>P\<^sub>L, \<gg>\<^sub>P\<^sub>L} = {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}" by auto
  interpret \<epsilon>: is_cat_cocone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  from \<epsilon>.cat_PL2_\<ff> \<epsilon>.cat_PL2_\<gg> have \<gg>\<ff>: "?F \<in>\<^sub>\<circ> Vset \<alpha>"
    by (intro Limit_vdoubleton_in_VsetI) auto
  from assms(2,3) have
    "(\<And>\<ff>'. \<ff>' \<in>\<^sub>\<circ> ?F \<Longrightarrow> (\<lambda>f\<in>\<^sub>\<circ>?F. (f = \<gg>\<^sub>P\<^sub>L ? \<gg> : \<ff>))\<lparr>\<ff>'\<rparr> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>)"
    by auto
  note cat_cocone_cf_par_eps_NTMap_app = cat_cocone_cf_par_eps_NTMap_app
    [
      OF assms(1)
        [
          unfolded 
            the_cat_parallel_2_def 
            the_cf_parallel_2_def 
            \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def 
            insert_commute,
          unfolded \<ff>\<gg>_\<gg>\<ff>
        ],
      folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def,
      OF _ \<gg>\<ff> _ this,
      simplified
    ]
  from
    cat_cocone_cf_par_eps_NTMap_app[of \<gg>\<^sub>P\<^sub>L, simplified]
    cat_cocone_cf_par_eps_NTMap_app[of \<ff>\<^sub>P\<^sub>L, simplified]
    cat_PL2_\<gg>\<ff>
  show
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>" 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
    by fastforce+
qed

lemma (in is_cat_equalizer_2) cat_eq_2_eps_NTMap_app:
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
proof-
  have \<gg>\<^sub>P\<^sub>L: "\<gg>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}" and \<ff>\<^sub>P\<^sub>L: "\<ff>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}" by auto
  note cat_eq_eps_NTMap_app = is_cat_equalizer.cat_eq_eps_NTMap_app
    [
      OF cat_equalizer_2_is_cat_equalizer,
      folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def
    ]
  from cat_eq_eps_NTMap_app[OF \<gg>\<^sub>P\<^sub>L] cat_eq_eps_NTMap_app[OF \<ff>\<^sub>P\<^sub>L] cat_PL2_\<gg>\<ff> show 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
    by auto
qed

lemma (in is_cat_coequalizer_2) cat_coeq_2_eps_NTMap_app:
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
proof-
  have \<gg>\<^sub>P\<^sub>L: "\<gg>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}" and \<ff>\<^sub>P\<^sub>L: "\<ff>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}" by auto
  note cat_eq_eps_NTMap_app = is_cat_coequalizer.cat_coeq_eps_NTMap_app
    [
      OF cat_coequalizer_2_is_cat_coequalizer,
      folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def
    ]
  from cat_eq_eps_NTMap_app[OF \<gg>\<^sub>P\<^sub>L] cat_eq_eps_NTMap_app[OF \<ff>\<^sub>P\<^sub>L] cat_PL2_\<gg>\<ff> show 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
    by auto
qed

lemma (in is_cat_equalizer_2) cat_eq_2_Comp_eq: 
  "\<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
  "\<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
  unfolding cat_eq_2_eps_NTMap_app[symmetric] by simp_all

lemma (in is_cat_coequalizer_2) cat_coeq_2_Comp_eq: 
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
  unfolding cat_coeq_2_eps_NTMap_app[symmetric] by simp_all


subsubsection\<open>Universal property\<close>

lemma is_cat_equalizer_2I':
  assumes "\<epsilon> :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<And>\<epsilon>' E'. \<epsilon>' :
      E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> :
      \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  shows "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  let ?II = \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close> 
    and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<close>
    and ?F = \<open>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}\<close>
  interpret \<epsilon>: is_cat_cone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  from \<epsilon>.cat_PL2_\<ff> \<epsilon>.cat_PL2_\<gg> have \<gg>\<ff>: "?F \<in>\<^sub>\<circ> Vset \<alpha>"
    by (intro Limit_vdoubleton_in_VsetI) auto
  from assms(2,3) have "(\<lambda>f\<in>\<^sub>\<circ>?F. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))\<lparr>\<ff>'\<rparr> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>" 
    if "\<ff>' \<in>\<^sub>\<circ> ?F" for \<ff>'
    using that by simp
  note is_cat_equalizerI' = is_cat_equalizerI'
      [
        OF 
          assms(1)[
            unfolded 
              the_cat_parallel_2_def the_cf_parallel_2_def \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def
            ], 
        folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def, 
        OF 
          _ 
          \<gg>\<ff> 
          _ 
          this 
          _ 
          assms(4)[unfolded the_cf_parallel_2_def the_cat_parallel_2_def], 
        of \<gg>\<^sub>P\<^sub>L,
        simplified
      ]
  show ?thesis by (rule cat_equalizer_is_cat_equalizer_2[OF is_cat_equalizerI'])
qed

lemma is_cat_coequalizer_2I':
  assumes "\<epsilon> :
    \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E :
    \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "\<And>\<epsilon>' E'. \<epsilon>' :
      \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E' :
      \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
  shows "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  let ?II = \<open>\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L\<close> 
    and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg>\<close>
    and ?F = \<open>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}\<close>
  have \<ff>\<gg>_\<gg>\<ff>: "{\<ff>\<^sub>P\<^sub>L, \<gg>\<^sub>P\<^sub>L} = {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}" by auto
  interpret \<epsilon>: is_cat_cocone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  from \<epsilon>.cat_PL2_\<ff> \<epsilon>.cat_PL2_\<gg> have \<gg>\<ff>: "?F \<in>\<^sub>\<circ> Vset \<alpha>"
    by (intro Limit_vdoubleton_in_VsetI) auto
  from assms(2,3) have "(\<lambda>f\<in>\<^sub>\<circ>set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}. (f = \<gg>\<^sub>P\<^sub>L ? \<gg> : \<ff>))\<lparr>\<ff>'\<rparr> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    if "\<ff>' \<in>\<^sub>\<circ> set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L}" for \<ff>'
    using that by simp
  note is_cat_coequalizerI'
    [
      OF assms(1)[
        unfolded 
          the_cat_parallel_2_def the_cf_parallel_2_def \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def \<ff>\<gg>_\<gg>\<ff>
          ],
      folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def,
      OF 
        _ 
        \<gg>\<ff>
        _ 
        this
        _
        assms(4)[unfolded the_cf_parallel_2_def the_cat_parallel_2_def \<ff>\<gg>_\<gg>\<ff>],
      of \<gg>\<^sub>P\<^sub>L,
      simplified
    ]
  with cat_PL2_\<gg>\<ff> have
    "\<epsilon> : (\<aa>,\<bb>,?F,(\<lambda>f\<in>\<^sub>\<circ>?F. (f = \<ff>\<^sub>P\<^sub>L ? \<ff> : \<gg>))) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<Up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (auto simp: VLambda_vdoubleton)
  from cat_coequalizer_is_cat_coequalizer_2[OF this] show ?thesis by simp
qed

lemma (in is_cat_equalizer_2) cat_eq_2_unique_cone:
  assumes "\<epsilon>' :
    E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : 
    \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  by 
    (
      rule is_cat_equalizer.cat_eq_unique_cone
        [
          OF cat_equalizer_2_is_cat_equalizer, 
          folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def,
          OF assms[unfolded the_cf_parallel_2_def the_cat_parallel_2_def]
        ]
    )

lemma (in is_cat_equalizer_2) cat_eq_2_unique:
  assumes "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> f'"
proof-  
  interpret \<epsilon>': is_cat_equalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms)
  show ?thesis
    by 
      (
        rule is_cat_equalizer.cat_eq_unique
          [
            OF cat_equalizer_2_is_cat_equalizer,
            folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def,
            OF \<epsilon>'.cat_equalizer_2_is_cat_equalizer,
            folded the_cat_parallel_2_def
          ]
      )
qed

lemma (in is_cat_equalizer_2) cat_eq_2_unique':
  assumes "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  interpret \<epsilon>': is_cat_equalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms)
  show ?thesis
    by 
      (
        rule is_cat_equalizer.cat_eq_unique'
          [
            OF cat_equalizer_2_is_cat_equalizer,
            folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def,
            OF \<epsilon>'.cat_equalizer_2_is_cat_equalizer,
            folded the_cat_parallel_2_def
          ]
      )
qed

lemma (in is_cat_coequalizer_2) cat_coeq_2_unique_cocone:
  assumes "\<epsilon>' :
    \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E' :
    \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
  by 
    (
      rule is_cat_coequalizer.cat_coeq_unique_cocone
        [
          OF cat_coequalizer_2_is_cat_coequalizer,
          folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def insert_commute,
          OF assms[
            unfolded 
              the_cf_parallel_2_def the_cat_parallel_2_def cat_eq_F'_helper
            ]
        ]
    )

lemma (in is_cat_coequalizer_2) cat_coeq_2_unique:
  assumes "\<epsilon>' : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and>
    \<epsilon>' = ntcf_const (\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L) \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>"
proof-
  interpret \<epsilon>': is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms)
  show ?thesis  
    by 
      (
        rule is_cat_coequalizer.cat_coeq_unique
          [
            OF cat_coequalizer_2_is_cat_coequalizer,
            folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def,
            OF \<epsilon>'.cat_coequalizer_2_is_cat_coequalizer,
            folded the_cat_parallel_2_def the_cat_parallel_2_commute
          ]
      )
qed

lemma (in is_cat_coequalizer_2) cat_coeq_2_unique':
  assumes "\<epsilon>' : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
proof-
  interpret \<epsilon>': is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms)
  show ?thesis
    by 
      (
        rule is_cat_coequalizer.cat_coeq_unique'
          [
            OF cat_coequalizer_2_is_cat_coequalizer,
            folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def,
            OF \<epsilon>'.cat_coequalizer_2_is_cat_coequalizer,
            folded the_cat_parallel_2_def
          ]
      )
qed

lemma cat_equalizer_2_ex_is_iso_arr:
  assumes "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E"
    and "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> f"
proof-
  interpret \<epsilon>: is_cat_equalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_equalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(2))
  show ?thesis
    using that 
    by 
      (
        rule cat_equalizer_ex_is_iso_arr
          [
            OF 
              \<epsilon>.cat_equalizer_2_is_cat_equalizer 
              \<epsilon>'.cat_equalizer_2_is_cat_equalizer,
            folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def the_cat_parallel_2_def
          ]
      )  
qed

lemma cat_equalizer_2_ex_is_iso_arr':
  assumes "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E"
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  interpret \<epsilon>: is_cat_equalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_equalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(2))
  show ?thesis
    using that 
    by 
      (
        rule cat_equalizer_ex_is_iso_arr'
          [
            OF 
              \<epsilon>.cat_equalizer_2_is_cat_equalizer 
              \<epsilon>'.cat_equalizer_2_is_cat_equalizer,
            folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def the_cat_parallel_2_def
          ]
      )
qed

lemma cat_coequalizer_2_ex_is_iso_arr:
  assumes "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon>' : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E'" 
    and "\<epsilon>' = ntcf_const (\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L\<^sub>2 \<aa>\<^sub>P\<^sub>L\<^sub>2 \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L) \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>"
proof-
  interpret \<epsilon>: is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(2))
  show ?thesis
    using that 
    by 
      (
        rule cat_coequalizer_ex_is_iso_arr
          [
            OF 
              \<epsilon>.cat_coequalizer_2_is_cat_coequalizer 
              \<epsilon>'.cat_coequalizer_2_is_cat_coequalizer,
            folded 
              \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def the_cat_parallel_2_def the_cat_parallel_2_commute
          ]
      )
qed

lemma cat_coequalizer_2_ex_is_iso_arr':
  assumes "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon>' : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E'" 
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
proof-
  interpret \<epsilon>: is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(2))
  show ?thesis
    using that 
    by 
      (
        rule cat_coequalizer_ex_is_iso_arr'
          [
            OF
              \<epsilon>.cat_coequalizer_2_is_cat_coequalizer
              \<epsilon>'.cat_coequalizer_2_is_cat_coequalizer,
            folded 
              \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def the_cat_parallel_2_def the_cat_parallel_2_commute
          ]
      )
qed


subsubsection\<open>Further properties\<close>

lemma (in is_cat_equalizer_2) cat_eq_2_is_monic_arr: 
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> : E \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> \<aa>"
  by
    (
      rule is_cat_equalizer.cat_eq_is_monic_arr[
        OF cat_equalizer_2_is_cat_equalizer, folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def
        ]
    )

lemma (in is_cat_coequalizer_2) cat_coeq_2_is_epic_arr:
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> : \<aa> \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> E"
  by
    (
      rule is_cat_coequalizer.cat_coeq_is_epic_arr[
        OF cat_coequalizer_2_is_cat_coequalizer, folded \<aa>\<^sub>P\<^sub>L\<^sub>2_def
        ]
    )



subsection\<open>Equalizer cone\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntcf_equalizer_base :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e =
    [
      (\<lambda>x\<in>\<^sub>\<circ>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<lparr>Obj\<rparr>. e x),
      cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E,
      \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>,
      \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L,
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_equalizer_base_components:
  shows "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTMap\<rparr> =
    (\<lambda>x\<in>\<^sub>\<circ>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<lparr>Obj\<rparr>. e x)"
    and [cat_lim_cs_simps]: "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTDom\<rparr> =
      cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E"
    and [cat_lim_cs_simps]: "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTCod\<rparr> =
      \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>"
    and [cat_lim_cs_simps]: 
      "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTDGDom\<rparr> = \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L"
    and [cat_lim_cs_simps]: 
      "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntcf_equalizer_base_def nt_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_equalizer_base_components(1)
  |vsv ntcf_equalizer_base_NTMap_vsv[cat_lim_cs_intros]|
  |vdomain ntcf_equalizer_base_NTMap_vdomain[cat_lim_cs_simps]|
  |app ntcf_equalizer_base_NTMap_app[cat_lim_cs_simps]|


subsubsection\<open>Equalizer cone is a cone\<close>

lemma (in category) cat_ntcf_equalizer_base_is_cat_cone:
  assumes "e \<aa>\<^sub>P\<^sub>L\<^sub>2 : E \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "e \<bb>\<^sub>P\<^sub>L\<^sub>2 : E \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "e \<bb>\<^sub>P\<^sub>L\<^sub>2 = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e \<aa>\<^sub>P\<^sub>L\<^sub>2"
    and "e \<bb>\<^sub>P\<^sub>L\<^sub>2 = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e \<aa>\<^sub>P\<^sub>L\<^sub>2"
    and "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
  shows "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> :
    \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret par: cf_parallel_2 \<alpha> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<CC> 
    by (intro cf_parallel_2I cat_parallel_2I assms(5,6))
      (simp_all add: cat_parallel_cs_intros cat_cs_intros)
  show ?thesis
  proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
    show "vfsequence (ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e)"
      unfolding ntcf_equalizer_base_def by auto
    show "vcard (ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e) = 5\<^sub>\<nat>"
      unfolding ntcf_equalizer_base_def by (simp add: nat_omega_simps)
    from assms(2) show 
      "cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_small_cs_intros cat_parallel_cs_intros cat_cs_intros
        )
    from assms show 
      "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: cat_parallel_cs_intros cat_small_cs_intros)
    show 
      "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTMap\<rparr>\<lparr>i\<rparr> :
        cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E\<lparr>ObjMap\<rparr>\<lparr>i\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub>
        \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>"
      if "i \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<lparr>Obj\<rparr>" for i 
    proof-
      from that assms(1,2,5,6) show ?thesis
        by (elim the_cat_parallel_2_ObjE; simp only:)
          ( 
            cs_concl 
              cs_simp: cat_lim_cs_simps cat_cs_simps cat_parallel_cs_simps 
              cs_intro: cat_cs_intros cat_parallel_cs_intros
          )
    qed
    show 
      "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
        cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> =
          \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
          ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTMap\<rparr>\<lparr>a'\<rparr>"
      if "f' : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<^esub> b'" for a' b' f'
      using that assms(1,2,5,6)
      by (elim par.the_cat_parallel_2_is_arrE; simp only:)
        (
          cs_concl 
            cs_simp: 
              cat_cs_simps 
              cat_lim_cs_simps 
              cat_parallel_cs_simps 
              assms(3,4)[symmetric]
            cs_intro: cat_parallel_cs_intros
        )+
  qed 
    (
      use assms(2) in 
        \<open>
          cs_concl 
            cs_intro: cat_lim_cs_intros cat_cs_intros 
            cs_simp: cat_lim_cs_simps
        \<close>
    )+
qed

text\<open>\newpage\<close>

end