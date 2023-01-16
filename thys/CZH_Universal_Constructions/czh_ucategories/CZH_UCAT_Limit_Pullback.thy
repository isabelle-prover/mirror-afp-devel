(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Pullbacks and pushouts as limits and colimits\<close>
theory CZH_UCAT_Limit_Pullback
  imports 
    CZH_UCAT_Limit
    CZH_Elementary_Categories.CZH_ECAT_SS
begin



subsection\<open>Pullback and pushout\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The definitions and the elementary properties of the pullbacks and the 
pushouts can be found, for example, in Chapter III-3 and Chapter III-4 in 
\<^cite>\<open>"mac_lane_categories_2010"\<close>. 
\<close>

locale is_cat_pullback =
  is_cat_limit \<alpha> \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> X x + 
  cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>
  for \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x 

syntax "_is_cat_pullback" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b _\<rightarrow>_\<rightarrow>_\<leftarrow>_\<leftarrow>_ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51, 51, 51] 51)
translations "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x"
                        
locale is_cat_pushout =
  is_cat_colimit \<alpha> \<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> X x +
  cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>
  for \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x

syntax "_is_cat_pushout" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _\<leftarrow>_\<leftarrow>_\<rightarrow>_\<rightarrow>_ >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51, 51, 51] 51)
translations "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x"


text\<open>Rules.\<close>

lemma (in is_cat_pullback) is_cat_pullback_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "\<aa>' = \<aa>"
    and "\<gg>' = \<gg>"
    and "\<oo>' = \<oo>"
    and "\<ff>' = \<ff>"
    and "\<bb>' = \<bb>"
    and "\<CC>' = \<CC>"
    and "X' = X"
  shows "x : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>'\<rightarrow>\<gg>'\<rightarrow>\<oo>'\<leftarrow>\<ff>'\<leftarrow>\<bb>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_pullback_axioms)

mk_ide rf is_cat_pullback_def
  |intro is_cat_pullbackI|
  |dest is_cat_pullbackD[dest]|
  |elim is_cat_pullbackE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_pullbackD

lemma (in is_cat_pushout) is_cat_pushout_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "\<aa>' = \<aa>"
    and "\<gg>' = \<gg>"
    and "\<oo>' = \<oo>"
    and "\<ff>' = \<ff>"
    and "\<bb>' = \<bb>"
    and "\<CC>' = \<CC>"
    and "X' = X"
  shows "x : \<aa>'\<leftarrow>\<gg>'\<leftarrow>\<oo>'\<rightarrow>\<ff>'\<rightarrow>\<bb>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_pushout_axioms)

mk_ide rf is_cat_pushout_def
  |intro is_cat_pushoutI|
  |dest is_cat_pushoutD[dest]|
  |elim is_cat_pushoutE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_pushoutD


text\<open>Duality.\<close>

lemma (in is_cat_pullback) is_cat_pushout_op:
  "op_ntcf x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_pushoutI) 
    (cs_concl cs_shallow cs_simp: cat_op_simps cs_intro: cat_op_intros)+

lemma (in is_cat_pullback) is_cat_pushout_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_pushout_op)

lemmas [cat_op_intros] = is_cat_pullback.is_cat_pushout_op'

lemma (in is_cat_pushout) is_cat_pullback_op:
  "op_ntcf x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_pullbackI) 
    (cs_concl cs_shallow cs_simp: cat_op_simps cs_intro: cat_op_intros)+

lemma (in is_cat_pushout) is_cat_pullback_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_pullback_op)

lemmas [cat_op_intros] = is_cat_pushout.is_cat_pullback_op'


text\<open>Elementary properties.\<close>

lemma cat_cone_cospan:
  assumes "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>"
  shows "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
    and "\<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
proof-
  interpret x: is_cat_cone \<alpha> X \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x 
    by (rule assms(1))
  interpret cospan: cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> by (rule assms(2))
  have \<gg>\<^sub>S\<^sub>S: "\<gg>\<^sub>S\<^sub>S : \<aa>\<^sub>S\<^sub>S \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> \<oo>\<^sub>S\<^sub>S" and \<ff>\<^sub>S\<^sub>S: "\<ff>\<^sub>S\<^sub>S : \<bb>\<^sub>S\<^sub>S \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> \<oo>\<^sub>S\<^sub>S" 
    by (cs_concl cs_intro: cat_ss_cs_intros)+
  note x.cat_cone_Comp_commute[cat_cs_simps del]
  from x.ntcf_Comp_commute[OF \<gg>\<^sub>S\<^sub>S] \<gg>\<^sub>S\<^sub>S \<ff>\<^sub>S\<^sub>S show
    "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    by 
      (
        cs_prems cs_shallow
          cs_simp: cat_ss_cs_simps cat_cs_simps cs_intro: cat_cs_intros
      )
  moreover from x.ntcf_Comp_commute[OF \<ff>\<^sub>S\<^sub>S] \<gg>\<^sub>S\<^sub>S \<ff>\<^sub>S\<^sub>S show 
    "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
    by 
      (
        cs_prems cs_shallow 
          cs_simp: cat_ss_cs_simps cat_cs_simps cs_intro: cat_cs_intros
      )
  ultimately show "\<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>" by simp
qed

lemma (in is_cat_pullback) cat_pb_cone_cospan:
  shows "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
    and "\<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
  by (all\<open>rule cat_cone_cospan[OF is_cat_cone_axioms cf_scospan_axioms]\<close>)

lemma cat_cocone_span:
  assumes "x : \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e X : \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>"
  shows "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
proof-
  interpret x: is_cat_cocone \<alpha> X \<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x
    by (rule assms(1))
  interpret span: cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> by (rule assms(2))
  note op = 
    cat_cone_cospan
      [
        OF 
          x.is_cat_cone_op[unfolded cat_op_simps] 
          span.cf_scospan_op, 
          unfolded cat_op_simps
      ]
  from op(1) show "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
    by 
      (
        cs_prems  
          cs_simp: cat_ss_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_ss_cs_intros
      )
  moreover from op(2) show "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
    by 
      (
        cs_prems 
          cs_simp: cat_ss_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_ss_cs_intros
      )
  ultimately show "x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>" by auto
qed

lemma (in is_cat_pushout) cat_po_cocone_span:
  shows "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
  by (all\<open>rule cat_cocone_span[OF is_cat_cocone_axioms cf_sspan_axioms]\<close>)


subsubsection\<open>Universal property\<close>

lemma is_cat_pullbackI':
  assumes "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>"
    and "\<And>x' X'. x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'.
        f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  shows "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_cat_pullbackI is_cat_limitI)

  show "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (rule assms(1))
  interpret x: is_cat_cone \<alpha> X \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x 
    by (rule assms(1))
  show "cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>" by (rule assms(2))
  interpret cospan: cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> by (rule assms(2))

  fix u' r' assume prems:
    "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"

  interpret u': is_cat_cone \<alpha> r' \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> u' 
    by (rule prems)

  from assms(3)[OF prems] obtain f' 
    where f': "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> X"
      and u'_\<aa>\<^sub>S\<^sub>S: "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      and u'_\<bb>\<^sub>S\<^sub>S: "u'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      and unique_f': "\<And>f''.
        \<lbrakk>
          f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> X;
          u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'';
          u'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''
        \<rbrakk> \<Longrightarrow> f'' = f'"
    by metis

  show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and> u' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'"
  proof(intro ex1I conjI; (elim conjE)?)

    show "u' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'"
    proof(rule ntcf_eqI)
      show "u' : cf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> r' \<mapsto>\<^sub>C\<^sub>F \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (rule u'.is_ntcf_axioms)
      from f' show 
        "x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f' :
          cf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> r' \<mapsto>\<^sub>C\<^sub>F \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> :
          \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from f' have dom_rhs: 
        "\<D>\<^sub>\<circ> ((x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f')\<lparr>NTMap\<rparr>) = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "u'\<lparr>NTMap\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f')\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold cat_cs_simps dom_rhs)
        fix a assume prems': "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
        from this f' x.is_ntcf_axioms show
          "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by (elim the_cat_scospan_ObjE; simp only:)
            (
              cs_concl 
                cs_simp:
                  cat_cs_simps cat_ss_cs_simps 
                  u'_\<bb>\<^sub>S\<^sub>S u'_\<aa>\<^sub>S\<^sub>S 
                  cat_cone_cospan(1)[OF assms(1,2)] 
                  cat_cone_cospan(1)[OF prems assms(2)] 
                cs_intro: cat_cs_intros cat_ss_cs_intros
            )+
      qed (cs_concl cs_intro: cat_cs_intros | auto)+
    qed simp_all

    fix f'' assume prems: 
      "f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> X" "u' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f''"
    have \<aa>\<^sub>S\<^sub>S: "\<aa>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" and \<bb>\<^sub>S\<^sub>S: "\<bb>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" 
      by (cs_concl cs_intro: cat_ss_cs_intros)+
    have "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''" if "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" for a
    proof-
      from prems(2) have 
        "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by simp
      from this that prems(1) show "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed
    from unique_f'[OF prems(1) this[OF \<aa>\<^sub>S\<^sub>S] this[OF \<bb>\<^sub>S\<^sub>S]] show "f'' = f'".

  qed (intro f')

qed

lemma is_cat_pushoutI':
  assumes "x : \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e X : \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>"
    and "\<And>x' X'. x' : \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e X' : \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'.
        f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
  shows "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret x: is_cat_cocone \<alpha> X \<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x 
    by (rule assms(1))
  interpret span: cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> by (rule assms(2))
  have assms_3': 
    "\<exists>!f'.
      f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f'"
    if "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    for x' X'
  proof-
    from that(1) have [cat_op_simps]:
      "f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and> 
      x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<longleftrightarrow>
        f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>" 
      for f'
      by (intro iffI conjI; (elim conjE)?)
        (
          cs_concl 
            cs_simp: category.op_cat_Comp[symmetric] cat_op_simps cat_cs_simps 
            cs_intro: cat_cs_intros cat_ss_cs_intros
        )+
    interpret x': 
      is_cat_cone \<alpha> X' \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<open>op_cat \<CC>\<close> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub>\<close> x'
      by (rule that)
    show ?thesis
      unfolding cat_op_simps
      by 
        (
          rule assms(3)[
            OF x'.is_cat_cocone_op[unfolded cat_op_simps], 
            unfolded cat_op_simps
            ]
        )
  qed
  interpret op_x: is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<open>op_cat \<CC>\<close> X \<open>op_ntcf x\<close> 
    using 
      is_cat_pullbackI'
        [
          OF x.is_cat_cone_op[unfolded cat_op_simps] 
          span.cf_scospan_op, 
          unfolded cat_op_simps, 
          OF assms_3'
        ]
    by simp
  show "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (rule op_x.is_cat_pushout_op[unfolded cat_op_simps])
qed
                   
lemma (in is_cat_pullback) cat_pb_unique_cone:
  assumes "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  interpret x': is_cat_cone \<alpha> X' \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x' 
    by (rule assms)
  from cat_lim_ua_fo[OF assms] obtain f'
    where f': "f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X" 
      and x'_def: "x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'"
      and unique_f': "\<And>f''.
        \<lbrakk> f'' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X; x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'' \<rbrakk> \<Longrightarrow>
        f'' = f'"
    by auto
  have \<aa>\<^sub>S\<^sub>S: "\<aa>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" and \<bb>\<^sub>S\<^sub>S: "\<bb>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
    by (cs_concl cs_intro: cat_ss_cs_intros)+
  show ?thesis
  proof(intro ex1I conjI; (elim conjE)?)
    show "f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X" by (rule f')
    have "x'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'" if "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" for a
    proof-
      from x'_def have 
        "x'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by simp
      from this that f' show "x'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed
    from this[OF \<aa>\<^sub>S\<^sub>S] this[OF \<bb>\<^sub>S\<^sub>S] show 
      "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      by auto
    fix f'' assume prems': 
      "f'' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X"
      "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
      "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
    have "x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f''"
    proof(rule ntcf_eqI)
      show "x' : cf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> X' \<mapsto>\<^sub>C\<^sub>F \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (rule x'.is_ntcf_axioms)
      from prems'(1) show
        "x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'' :
          cf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> X' \<mapsto>\<^sub>C\<^sub>F \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> :
          \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      have dom_lhs: "\<D>\<^sub>\<circ> (x'\<lparr>NTMap\<rparr>) = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" 
        by (cs_concl cs_shallow cs_simp: cat_cs_simps)
      from prems'(1) have dom_rhs:
        "\<D>\<^sub>\<circ> ((x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'')\<lparr>NTMap\<rparr>) = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "x'\<lparr>NTMap\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'')\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
        fix a assume prems'': "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
        from this prems'(1) show 
          "x'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by (elim the_cat_scospan_ObjE; simp only:)
            (
              cs_concl 
                cs_simp: 
                  prems'(2,3)
                  cat_cone_cospan(1,2)[OF assms cf_scospan_axioms] 
                  cat_pb_cone_cospan 
                  cat_ss_cs_simps cat_cs_simps 
                cs_intro: cat_ss_cs_intros cat_cs_intros
            )+
      qed (auto simp: cat_cs_intros)
    qed simp_all
    from unique_f'[OF prems'(1) this] show "f'' = f'".
  qed
qed

lemma (in is_cat_pullback) cat_pb_unique:
  assumes "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and> x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'"
  by (rule cat_lim_unique[OF is_cat_pullbackD(1)[OF assms]])

lemma (in is_cat_pullback) cat_pb_unique':
  assumes "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  interpret x': is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(1))
  show ?thesis by (rule cat_pb_unique_cone[OF x'.is_cat_cone_axioms])
qed

lemma (in is_cat_pushout) cat_po_unique_cocone:
  assumes "x' : \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e X' : \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
proof-
  interpret x': is_cat_cocone \<alpha> X' \<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x'
    by (rule assms(1))
  have [cat_op_simps]:
    "f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<longleftrightarrow>
      f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>" 
    for f'
    by (intro iffI conjI; (elim conjE)?)
      (
        cs_concl 
          cs_simp: category.op_cat_Comp[symmetric] cat_op_simps cat_cs_simps  
          cs_intro: cat_cs_intros cat_ss_cs_intros
      )+
  show ?thesis
    by 
      (
        rule is_cat_pullback.cat_pb_unique_cone[
          OF is_cat_pullback_op x'.is_cat_cone_op[unfolded cat_op_simps], 
          unfolded cat_op_simps
          ]
     )
qed

lemma (in is_cat_pushout) cat_po_unique:
  assumes "x' : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and> x' = ntcf_const \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F x"
  by (rule cat_colim_unique[OF is_cat_pushoutD(1)[OF assms]])

lemma (in is_cat_pushout) cat_po_unique':
  assumes "x' : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
proof-
  interpret x': is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(1))
  show ?thesis by (rule cat_po_unique_cocone[OF x'.is_cat_cocone_axioms])
qed

lemma cat_pullback_ex_is_iso_arr:
  assumes "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : X' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X" 
    and "x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C  \<CC> f"
proof-
  interpret x: is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x by (rule assms(1))
  interpret x': is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_lim_ex_is_iso_arr[
          OF x.is_cat_limit_axioms x'.is_cat_limit_axioms
          ]
      )
qed

lemma cat_pullback_ex_is_iso_arr':
  assumes "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : X' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X" 
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  interpret x: is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x by (rule assms(1))
  interpret x': is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(2))
  obtain f where f: "f : X' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X"
    and "j \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr> \<Longrightarrow> x'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" for j
    by 
      (
        elim cat_lim_ex_is_iso_arr'[
          OF x.is_cat_limit_axioms x'.is_cat_limit_axioms
          ]
      )
  then have 
    "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" 
    "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    by (auto simp: cat_ss_cs_intros)
  with f show ?thesis using that by simp
qed

lemma cat_pushout_ex_is_iso_arr:
  assumes "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "x' : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : X \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X'" 
    and "x' = ntcf_const \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F x"
proof-
  interpret x: is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x by (rule assms(1))
  interpret x': is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_colim_ex_is_iso_arr[
          OF x.is_cat_colimit_axioms x'.is_cat_colimit_axioms
          ]
      )
qed

lemma cat_pushout_ex_is_iso_arr':
  assumes "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "x' : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : X \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X'" 
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
proof-
  interpret x: is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x by (rule assms(1))
  interpret x': is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(2))
  obtain f where f: "f : X \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X'"
    and "j \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr> \<Longrightarrow> x'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" for j
    by 
      (
        elim cat_colim_ex_is_iso_arr'[
          OF x.is_cat_colimit_axioms x'.is_cat_colimit_axioms
          ]
      )
  then have "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
    by (auto simp: cat_ss_cs_intros)
  with f show ?thesis using that by simp
qed

text\<open>\newpage\<close>

end