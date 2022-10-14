(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for cones and cocones\<close>
theory CZH_ECAT_Small_Cone
  imports 
    CZH_ECAT_Cone
    CZH_ECAT_Small_NTCF
begin



subsection\<open>Cone with tiny maps and cocone with tiny maps\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tm_cat_cone =
  is_ntcf \<alpha> \<JJ> \<CC> \<open>cf_const \<JJ> \<CC> c\<close> \<FF> \<NN> + NTCod: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> 
  for \<alpha> c \<JJ> \<CC> \<FF> \<NN> +
  assumes tm_cat_cone_obj[cat_cs_intros, cat_small_cs_intros]: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"

syntax "_is_tm_cat_cone" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_tm_cat_cone \<alpha> c \<JJ> \<CC> \<FF> \<NN>"

locale is_tm_cat_cocone = 
  is_ntcf \<alpha> \<JJ> \<CC> \<FF> \<open>cf_const \<JJ> \<CC> c\<close> \<NN> + NTDom: is_tm_functor \<alpha> \<JJ> \<CC> \<FF>
  for \<alpha> c \<JJ> \<CC> \<FF> \<NN> +
  assumes tm_cat_cocone_obj[cat_cs_intros, cat_small_cs_intros]: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"

syntax "_is_tm_cat_cocone" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_tm_cat_cocone \<alpha> c \<JJ> \<CC> \<FF> \<NN>"


text\<open>Rules.\<close>

lemma (in is_tm_cat_cone) is_tm_cat_cone_axioms'[
    cat_cs_intros, cat_small_cs_intros
    ]:
  assumes "\<alpha>' = \<alpha>" and "c' = c" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "\<NN> : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_cone_axioms)

mk_ide rf is_tm_cat_cone_def[unfolded is_tm_cat_cone_axioms_def]
  |intro is_tm_cat_coneI|
  |dest is_tm_cat_coneD[dest!]|
  |elim is_tm_cat_coneE[elim!]|

lemma (in is_tm_cat_cocone) is_tm_cat_cocone_axioms'[
    cat_cs_intros, cat_small_cs_intros
    ]:
  assumes "\<alpha>' = \<alpha>" and "c' = c" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "\<NN> : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_cocone_axioms)

mk_ide rf is_tm_cat_cocone_def[unfolded is_tm_cat_cocone_axioms_def]
  |intro is_tm_cat_coconeI|
  |dest is_tm_cat_coconeD[dest!]|
  |elim is_tm_cat_coconeE[elim!]|


text\<open>Duality.\<close>

lemma (in is_tm_cat_cone) is_tm_cat_cocone_op:
  "op_ntcf \<NN> : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_tm_cat_coconeI)
    (
      cs_concl cs_shallow
        cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros
    )+

lemma (in is_tm_cat_cone) is_tm_cat_cocone_op'[cat_op_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>" and "\<FF>' = op_cf \<FF>"
  shows "op_ntcf \<NN> : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_cocone_op)

lemmas [cat_op_intros] = is_tm_cat_cone.is_tm_cat_cocone_op'

lemma (in is_tm_cat_cocone) is_tm_cat_cone_op:
  "op_ntcf \<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_tm_cat_coneI)
    (
      cs_concl cs_shallow 
        cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros
    )

lemma (in is_tm_cat_cocone) is_tm_cat_cone_op'[cat_op_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>" and "\<FF>' = op_cf \<FF>"
  shows "op_ntcf \<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_cone_op)

lemmas [cat_op_intros] = is_cat_cocone.is_cat_cone_op'


text\<open>Elementary properties.\<close>

lemma (in is_tm_cat_cone) tm_cat_cone_is_tm_ntcf'[
    cat_cs_intros, cat_small_cs_intros
    ]:
  assumes "c' = cf_const \<JJ> \<CC> c"
  shows "\<NN> : c' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  unfolding assms
proof(intro is_tm_ntcfI')
  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> by (rule NTCod.is_tm_functor_axioms)
  show "cf_const \<JJ> \<CC> c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)
qed (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros assms)+

lemmas [cat_small_cs_intros] = is_tm_cat_cone.tm_cat_cone_is_tm_ntcf'

sublocale is_tm_cat_cone \<subseteq> is_tm_ntcf \<alpha> \<JJ> \<CC> \<open>cf_const \<JJ> \<CC> c\<close> \<FF> \<NN> 
  by (intro tm_cat_cone_is_tm_ntcf') simp

lemma (in is_tm_cat_cocone) tm_cat_cocone_is_tm_ntcf'[
    cat_cs_intros, cat_small_cs_intros
    ]:
  assumes "c' = cf_const \<JJ> \<CC> c"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  unfolding assms
proof(intro is_tm_ntcfI')
  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> by (rule NTDom.is_tm_functor_axioms)
  show "cf_const \<JJ> \<CC> c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)
qed (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros assms)+

lemmas [cat_small_cs_intros, cat_cs_intros] = 
  is_tm_cat_cocone.tm_cat_cocone_is_tm_ntcf'

sublocale is_tm_cat_cocone \<subseteq> is_tm_ntcf \<alpha> \<JJ> \<CC> \<FF> \<open>cf_const \<JJ> \<CC> c\<close> \<NN> 
  by (intro tm_cat_cocone_is_tm_ntcf') simp

sublocale is_tm_cat_cone \<subseteq> is_cat_cone
  by (intro is_cat_coneI, rule is_ntcf_axioms, rule tm_cat_cone_obj)

lemmas (in is_tm_cat_cone) tm_cat_cone_is_cat_cone = is_cat_cone_axioms
lemmas [cat_small_cs_intros] = is_tm_cat_cone.tm_cat_cone_is_cat_cone

sublocale is_tm_cat_cocone \<subseteq> is_cat_cocone
  by (intro is_cat_coconeI, rule is_ntcf_axioms, rule tm_cat_cocone_obj)

lemmas (in is_tm_cat_cocone) tm_cat_cocone_is_cat_cocone = is_cat_cocone_axioms
lemmas [cat_small_cs_intros] = is_tm_cat_cocone.tm_cat_cocone_is_cat_cocone


subsubsection\<open>
Vertical composition of a natural transformation with tiny maps 
and a cone with tiny maps
\<close>

lemma ntcf_vcomp_is_tm_cat_cone[cat_cs_intros]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  by 
    (
      intro is_tm_cat_coneI ntcf_vcomp_is_ntcf; 
      (rule is_tm_ntcfD'[OF assms(1)])?; 
      (intro is_tm_cat_coneD[OF assms(2)])?
    )


subsubsection\<open>
Composition of a functor and a cone with tiny maps,
composition of a functor and a cocone with tiny maps
\<close>

lemma cf_ntcf_comp_tm_cf_tm_cat_cone: 
  assumes "\<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_tm_cat_cone \<alpha> c \<AA> \<BB> \<FF> \<NN> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  interpret \<GG>\<FF>: is_tm_functor \<alpha> \<AA> \<CC> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> by (rule assms(3))
  show ?thesis
    by (intro is_tm_cat_coneI)
      (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros is_cat_coneD)+
qed

lemma cf_ntcf_comp_tm_cf_tm_cat_cone'[cat_small_cs_intros]: 
  assumes "\<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "c' = \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    and "\<GG>\<FF> = \<GG> \<circ>\<^sub>C\<^sub>F \<FF>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG>\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2,3) 
  unfolding assms(4,5) 
  by (rule cf_ntcf_comp_tm_cf_tm_cat_cone)

lemma cf_ntcf_comp_tm_cf_tm_cat_cocone:
  assumes "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<GG> \<circ>\<^sub>C\<^sub>F \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_tm_cat_cocone \<alpha> c \<AA> \<BB> \<FF> \<NN> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  interpret \<GG>\<FF>: is_tm_functor \<alpha> \<AA> \<CC> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> by (rule assms(3))
  show ?thesis
    by
      (
        rule is_tm_cat_cone.is_tm_cat_cocone_op
          [
            OF cf_ntcf_comp_tm_cf_tm_cat_cone[
              OF \<NN>.is_tm_cat_cone_op \<GG>.is_functor_op, unfolded cat_op_simps
              ],
            OF \<GG>\<FF>.is_tm_functor_op[unfolded cat_op_simps],
            unfolded cat_op_simps
          ]
      )
qed

lemma cf_ntcf_comp_tm_cf_tm_cat_cocone'[cat_small_cs_intros]: 
  assumes "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "c' = \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    and "\<GG>\<FF> = \<GG> \<circ>\<^sub>C\<^sub>F \<FF>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<GG>\<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1-3) 
  unfolding assms(4,5) 
  by (rule cf_ntcf_comp_tm_cf_tm_cat_cocone)


subsubsection\<open>
Cones and cocones with tiny maps and constant natural transformations
\<close>

lemma ntcf_vcomp_ntcf_const_is_tm_cat_cone:
  assumes "\<NN> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<AA> \<BB> f : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_tm_cat_cone \<alpha> b \<AA> \<BB> \<FF> \<NN> by (rule assms(1))
  from assms(2) show ?thesis
    by (intro is_tm_cat_coneI)
      (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)
qed

lemma ntcf_vcomp_ntcf_const_is_tm_cat_cone'[cat_small_cs_intros]:
  assumes "\<NN> : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM> = ntcf_const \<AA> \<BB> f"
    and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1,3)
  unfolding assms(2)
  by (rule ntcf_vcomp_ntcf_const_is_tm_cat_cone)

lemma ntcf_vcomp_ntcf_const_is_tm_cat_cocone:
  assumes "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e a : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "ntcf_const \<AA> \<BB> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e b : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_tm_cat_cocone \<alpha> a \<AA> \<BB> \<FF> \<NN> by (rule assms(1))
  from is_tm_cat_cone.is_tm_cat_cocone_op
    [
      OF ntcf_vcomp_ntcf_const_is_tm_cat_cone[
        OF \<NN>.is_tm_cat_cone_op, unfolded cat_op_simps, OF assms(2)
        ],
      unfolded cat_op_simps, 
      folded op_ntcf_ntcf_const
    ]
    assms(2)
  show ?thesis
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros)
qed

lemma ntcf_vcomp_ntcf_const_is_tm_cat_cocone'[cat_cs_intros]:
  assumes "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e a : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<MM> = ntcf_const \<AA> \<BB> f"
    and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e b : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1,3)
  unfolding assms(2)
  by (rule ntcf_vcomp_ntcf_const_is_tm_cat_cocone)



subsection\<open>Small cone and small cocone functors\<close>(*TODO: duality automation*)


subsubsection\<open>Definition and elementary properties\<close>

definition tm_cf_Cone :: "V \<Rightarrow> V \<Rightarrow> V"
  where "tm_cf_Cone \<alpha> \<FF> =
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Funct \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>)(-,cf_map \<FF>) \<circ>\<^sub>C\<^sub>F
    op_cf (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>))"

definition tm_cf_Cocone :: "V \<Rightarrow> V \<Rightarrow> V"
  where "tm_cf_Cocone \<alpha> \<FF> =
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Funct \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>)(cf_map \<FF>,-) \<circ>\<^sub>C\<^sub>F
    (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>))"


text\<open>Alternative definitions.\<close>

context is_tm_functor
begin

lemma tm_cf_Cone_def': 
  "tm_cf_Cone \<alpha> \<FF> =
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Funct \<alpha> \<AA> \<BB>(-,cf_map \<FF>) \<circ>\<^sub>C\<^sub>F op_cf (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>)"
  unfolding tm_cf_Cone_def cat_cs_simps by simp

lemma tm_cf_Cocone_def': 
  "tm_cf_Cocone \<alpha> \<FF> =
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Funct \<alpha> \<AA> \<BB>(cf_map \<FF>,-) \<circ>\<^sub>C\<^sub>F (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>)"
  unfolding tm_cf_Cocone_def cat_cs_simps by simp

end


subsubsection\<open>Object map\<close>

lemma (in is_tm_functor) tm_cf_Cone_ObjMap_vsv[cat_small_cs_intros]:
  "vsv (tm_cf_Cone \<alpha> \<FF>\<lparr>ObjMap\<rparr>)"
proof-
  interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  show ?thesis
    unfolding tm_cf_Cone_def
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro: 
            cat_small_cs_intros 
            cat_cs_intros 
            cat_FUNCT_cs_intros 
            cat_op_intros
      )
qed

lemmas [cat_small_cs_intros] = is_tm_functor.tm_cf_Cone_ObjMap_vsv

lemma (in is_tm_functor) tm_cf_Cocone_ObjMap_vsv[cat_small_cs_intros]:
  "vsv (tm_cf_Cocone \<alpha> \<FF>\<lparr>ObjMap\<rparr>)"
proof-
  interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  show ?thesis
    unfolding tm_cf_Cocone_def
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros 
       )
qed

lemmas [cat_small_cs_intros] = is_tm_functor.tm_cf_Cocone_ObjMap_vsv

lemma (in is_tm_functor) tm_cf_Cone_ObjMap_vdomain[cat_small_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (tm_cf_Cone \<alpha> \<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
proof-
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  from assms show ?thesis
    unfolding tm_cf_Cone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro: 
            cat_small_cs_intros 
            cat_cs_intros 
            cat_FUNCT_cs_intros 
            cat_op_intros
      )
qed

lemmas [cat_small_cs_simps] = is_tm_functor.tm_cf_Cone_ObjMap_vdomain

lemma (in is_tm_functor) tm_cf_Cocone_ObjMap_vdomain[cat_small_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (tm_cf_Cocone \<alpha> \<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
proof-
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  from assms show ?thesis
    unfolding tm_cf_Cocone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro: 
            cat_small_cs_intros 
            cat_cs_intros 
            cat_FUNCT_cs_intros 
            cat_op_intros
      )
qed

lemmas [cat_small_cs_simps] = is_tm_functor.tm_cf_Cocone_ObjMap_vdomain

lemma (in is_tm_functor) tm_cf_Cone_ObjMap_app[cat_small_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "tm_cf_Cone \<alpha> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> =
    Hom (cat_Funct \<alpha> \<AA> \<BB>) (cf_map (cf_const \<AA> \<BB> b)) (cf_map \<FF>)"
proof-
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  from assms show ?thesis
    unfolding tm_cf_Cone_def
    by
      (
        cs_concl
          cs_simp: 
            cat_small_cs_simps
            cat_cs_simps
            cat_FUNCT_cs_simps
            cat_op_simps
          cs_intro: 
            cat_small_cs_intros
            cat_cs_intros 
            cat_FUNCT_cs_intros
            cat_op_intros
      )
qed

lemmas [cat_small_cs_simps] = is_tm_functor.tm_cf_Cone_ObjMap_app

lemma (in is_tm_functor) tm_cf_Cocone_ObjMap_app[cat_small_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "tm_cf_Cocone \<alpha> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> =
    Hom (cat_Funct \<alpha> \<AA> \<BB>) (cf_map \<FF>) (cf_map (cf_const \<AA> \<BB> b))"
proof-
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  from assms show ?thesis
    unfolding tm_cf_Cocone_def
    by
      (
        cs_concl cs_shallow
          cs_simp:
            cat_small_cs_simps cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
qed

lemmas [cat_small_cs_simps] = is_tm_functor.tm_cf_Cocone_ObjMap_app


subsubsection\<open>Arrow map\<close>

lemma (in is_tm_functor) tm_cf_Cone_ArrMap_vsv[cat_small_cs_intros]:
  "vsv (tm_cf_Cone \<alpha> \<FF>\<lparr>ArrMap\<rparr>)"
proof-
  interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  show ?thesis
    unfolding tm_cf_Cone_def
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps 
          cs_intro: 
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_small_cs_intros] = is_tm_functor.tm_cf_Cone_ArrMap_vsv

lemma (in is_tm_functor) tm_cf_Cocone_ArrMap_vsv[cat_small_cs_intros]:
  "vsv (tm_cf_Cocone \<alpha> \<FF>\<lparr>ArrMap\<rparr>)"
proof-
  interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  show ?thesis
    unfolding tm_cf_Cocone_def
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_small_cs_intros] = is_tm_functor.tm_cf_Cocone_ArrMap_vsv

lemma (in is_tm_functor) tm_cf_Cone_ArrMap_vdomain[cat_small_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (tm_cf_Cone \<alpha> \<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
proof-
  interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  from assms show ?thesis
    unfolding tm_cf_Cone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_small_cs_simps] = is_tm_functor.tm_cf_Cone_ArrMap_vdomain

lemma (in is_tm_functor) tm_cf_Cocone_ArrMap_vdomain[cat_small_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (tm_cf_Cocone \<alpha> \<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
proof-
  interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  from assms show ?thesis
    unfolding tm_cf_Cocone_def'
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
qed

lemmas [cat_small_cs_simps] = is_tm_functor.tm_cf_Cocone_ArrMap_vdomain

lemma (in is_tm_functor) tm_cf_Cone_ArrMap_app[cat_small_cs_simps]:
  assumes "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "tm_cf_Cone \<alpha> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = cf_hom
    (cat_Funct \<alpha> \<AA> \<BB>)
    [ntcf_arrow (ntcf_const \<AA> \<BB> f), cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>cf_map \<FF>\<rparr>]\<^sub>\<circ>"
proof-
  interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  from assms show ?thesis
    unfolding tm_cf_Cone_def
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps 
          cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_small_cs_simps] = is_tm_functor.tm_cf_Cone_ArrMap_app

lemma (in is_tm_functor) tm_cf_Cocone_ArrMap_app[cat_small_cs_simps]:
  assumes "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "tm_cf_Cocone \<alpha> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = cf_hom
    (cat_Funct \<alpha> \<AA> \<BB>)
    [cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>cf_map \<FF>\<rparr>, ntcf_arrow (ntcf_const \<AA> \<BB> f)]\<^sub>\<circ>"
proof-
  interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  from assms show ?thesis
    unfolding tm_cf_Cocone_def
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps cat_op_simps
          cs_intro:
            cat_small_cs_intros
            cat_cs_intros
            cat_FUNCT_cs_intros
            cat_op_intros
      )
qed

lemmas [cat_small_cs_simps] = is_tm_functor.tm_cf_Cocone_ArrMap_app


subsubsection\<open>Small cone functor and small cocone functor are functors\<close>

lemma (in is_tm_functor) tm_cf_cf_Cone_is_functor:
  "tm_cf_Cone \<alpha> \<FF> : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  interpret \<AA>\<BB>: category \<alpha> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_shallow cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  interpret op_\<Delta>: 
    is_functor \<alpha> \<open>op_cat \<BB>\<close> \<open>op_cat (cat_Funct \<alpha> \<AA> \<BB>)\<close> \<open>op_cf (\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>)\<close>
    by 
      (
        cs_concl cs_shallow cs_intro:
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )
  have "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Funct \<alpha> \<AA> \<BB>(-,cf_map \<FF>) :
    op_cat (cat_Funct \<alpha> \<AA> \<BB>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_FUNCT_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  then show "tm_cf_Cone \<alpha> \<FF> : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    unfolding tm_cf_Cone_def' by (cs_concl cs_intro: cat_cs_intros)
qed

lemma (in is_tm_functor) tm_cf_cf_Cone_is_functor'[cat_small_cs_intros]:
  assumes "\<AA>' = op_cat \<BB>" and "\<BB>' = cat_Set \<alpha>" and "\<alpha>' = \<alpha>"
  shows "tm_cf_Cone \<alpha> \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule tm_cf_cf_Cone_is_functor)

lemmas [cat_small_cs_intros] = is_tm_functor.tm_cf_cf_Cone_is_functor'

lemma (in is_tm_functor) tm_cf_cf_Cocone_is_functor:
  "tm_cf_Cocone \<alpha> \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  interpret Funct: category \<alpha> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_shallow cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_cs_intros)
  have "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>cat_Funct \<alpha> \<AA> \<BB>(cf_map \<FF>,-) :
    cat_Funct \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by
      (
        cs_concl cs_shallow
          cs_simp: cat_FUNCT_cs_simps
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  then show "tm_cf_Cocone \<alpha> \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    unfolding tm_cf_Cocone_def' by (cs_concl cs_intro: cat_cs_intros)
qed

lemma (in is_tm_functor) tm_cf_cf_Cocone_is_functor'[cat_small_cs_intros]:
  assumes "\<BB>' = cat_Set \<alpha>" and "\<alpha>' = \<alpha>"
  shows "tm_cf_Cocone \<alpha> \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule tm_cf_cf_Cocone_is_functor)

lemmas [cat_small_cs_intros] = is_tm_functor.tm_cf_cf_Cocone_is_functor'

text\<open>\newpage\<close>

end