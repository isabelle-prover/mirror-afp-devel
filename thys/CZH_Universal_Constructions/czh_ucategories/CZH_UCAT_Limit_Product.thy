(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Products and coproducts as limits and colimits\<close>
theory CZH_UCAT_Limit_Product
  imports 
    CZH_UCAT_Limit
    CZH_Elementary_Categories.CZH_ECAT_Discrete 
begin



subsection\<open>Product and coproduct\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The definition of the product object is a specialization of the 
definition presented in Chapter III-4 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.
In the definition presented below, the discrete category that is used in the 
definition presented in \<^cite>\<open>"mac_lane_categories_2010"\<close> is parameterized by
an index set and the functor from the discrete category is 
parameterized by a function from the index set to the set of 
the objects of the category.
\<close>

locale is_cat_obj_prod = 
  is_cat_limit \<alpha> \<open>:\<^sub>C I\<close> \<CC> \<open>:\<rightarrow>: I A \<CC>\<close> P \<pi> + cf_discrete \<alpha> I A \<CC>
  for \<alpha> I A \<CC> P \<pi>

syntax "_is_cat_obj_prod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_prod \<alpha> I A \<CC> P \<pi>"

locale is_cat_obj_coprod = 
  is_cat_colimit \<alpha> \<open>:\<^sub>C I\<close> \<CC> \<open>:\<rightarrow>: I A \<CC>\<close> U \<pi> + cf_discrete \<alpha> I A \<CC>
  for \<alpha> I A \<CC> U \<pi>

syntax "_is_cat_obj_coprod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_coprod \<alpha> I A \<CC> U \<pi>"


text\<open>Rules.\<close>

lemma (in is_cat_obj_prod) is_cat_obj_prod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "P' = P" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A' : I' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_prod_axioms)

mk_ide rf is_cat_obj_prod_def
  |intro is_cat_obj_prodI|
  |dest is_cat_obj_prodD[dest]|
  |elim is_cat_obj_prodE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_prodD

lemma (in is_cat_obj_coprod) is_cat_obj_coprod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "U' = U" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : A' >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_coprod_axioms)

mk_ide rf is_cat_obj_coprod_def
  |intro is_cat_obj_coprodI|
  |dest is_cat_obj_coprodD[dest]|
  |elim is_cat_obj_coprodE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_coprodD


text\<open>Duality.\<close>

lemma (in is_cat_obj_prod) is_cat_obj_coprod_op:
  "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  using cf_discrete_vdomain_vsubset_Vset
  by (intro is_cat_obj_coprodI)
    (
      cs_concl cs_shallow 
        cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros
    )

lemma (in is_cat_obj_prod) is_cat_obj_coprod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_coprod_op)

lemmas [cat_op_intros] = is_cat_obj_prod.is_cat_obj_coprod_op'

lemma (in is_cat_obj_coprod) is_cat_obj_prod_op:
  "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  using cf_discrete_vdomain_vsubset_Vset
  by (intro is_cat_obj_prodI)
    (
      cs_concl cs_shallow 
        cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros
    )

lemma (in is_cat_obj_coprod) is_cat_obj_prod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_prod_op)

lemmas [cat_op_intros] = is_cat_obj_coprod.is_cat_obj_prod_op'


subsubsection\<open>Universal property\<close>

lemma (in is_cat_obj_prod) cat_obj_prod_unique_cone':
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: I A \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and> (\<forall>j\<in>\<^sub>\<circ>I. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
  by 
    (
      rule cat_lim_unique_cone'[
        OF assms, unfolded the_cat_discrete_components(1)
        ]
    )

lemma (in is_cat_obj_prod) cat_obj_prod_unique:
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and> \<pi>' = \<pi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) \<CC> f'"
  by (intro cat_lim_unique[OF is_cat_obj_prodD(1)[OF assms]])

lemma (in is_cat_obj_prod) cat_obj_prod_unique':
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and> (\<forall>i\<in>\<^sub>\<circ>I. \<pi>'\<lparr>NTMap\<rparr>\<lparr>i\<rparr> = \<pi>\<lparr>NTMap\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
proof-
  interpret \<pi>': is_cat_obj_prod \<alpha> I A \<CC> P' \<pi>' by (rule assms(1))
  show ?thesis
    by 
      (
        rule cat_lim_unique'[
          OF \<pi>'.is_cat_limit_axioms, unfolded the_cat_discrete_components(1)
          ]
      )
qed

lemma (in is_cat_obj_coprod) cat_obj_coprod_unique_cocone':
  assumes "\<pi>' : :\<rightarrow>: I A \<CC> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e U' : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : U \<mapsto>\<^bsub>\<CC>\<^esub> U' \<and> (\<forall>j\<in>\<^sub>\<circ>I. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
  by 
    (
      rule cat_colim_unique_cocone'[
        OF assms, unfolded the_cat_discrete_components(1)
        ]
    )

lemma (in is_cat_obj_coprod) cat_obj_coprod_unique:
  assumes "\<pi>' : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : U \<mapsto>\<^bsub>\<CC>\<^esub> U' \<and> \<pi>' = ntcf_const (:\<^sub>C I) \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<pi>"
  by (intro cat_colim_unique[OF is_cat_obj_coprodD(1)[OF assms]])

lemma (in is_cat_obj_coprod) cat_obj_coprod_unique':
  assumes "\<pi>' : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : U \<mapsto>\<^bsub>\<CC>\<^esub> U' \<and> (\<forall>j\<in>\<^sub>\<circ>I. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
  by 
    (
      rule cat_colim_unique'[
        OF is_cat_obj_coprodD(1)[OF assms], unfolded the_cat_discrete_components
        ]
    )

lemma cat_obj_prod_ex_is_iso_arr:
  assumes "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : P' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> P" and "\<pi>' = \<pi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) \<CC> f"
proof-
  interpret \<pi>: is_cat_obj_prod \<alpha> I A \<CC> P \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_prod \<alpha> I A \<CC> P' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_lim_ex_is_iso_arr[
          OF \<pi>.is_cat_limit_axioms \<pi>'.is_cat_limit_axioms
          ]
      )
qed

lemma cat_obj_prod_ex_is_iso_arr':
  assumes "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : P' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> P" 
    and "\<And>j. j \<in>\<^sub>\<circ> I \<Longrightarrow> \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  interpret \<pi>: is_cat_obj_prod \<alpha> I A \<CC> P \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_prod \<alpha> I A \<CC> P' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_lim_ex_is_iso_arr'[
          OF \<pi>.is_cat_limit_axioms \<pi>'.is_cat_limit_axioms,
          unfolded the_cat_discrete_components(1)
          ]
      )
qed

lemma cat_obj_coprod_ex_is_iso_arr:
  assumes "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<pi>' : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : U \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> U'" and "\<pi>' = ntcf_const (:\<^sub>C I) \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<pi>"
proof-
  interpret \<pi>: is_cat_obj_coprod \<alpha> I A \<CC> U \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_coprod \<alpha> I A \<CC> U' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_colim_ex_is_iso_arr[
          OF \<pi>.is_cat_colimit_axioms \<pi>'.is_cat_colimit_axioms
          ]
      )
qed

lemma cat_obj_coprod_ex_is_iso_arr':
  assumes "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<pi>' : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : U \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> U'" 
    and "\<And>j. j \<in>\<^sub>\<circ> I \<Longrightarrow> \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
proof-
  interpret \<pi>: is_cat_obj_coprod \<alpha> I A \<CC> U \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_coprod \<alpha> I A \<CC> U' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_colim_ex_is_iso_arr'[
          OF \<pi>.is_cat_colimit_axioms \<pi>'.is_cat_colimit_axioms,
          unfolded the_cat_discrete_components(1)
          ]
      )
qed



subsection\<open>Small product and small coproduct\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tm_cat_obj_prod = 
  is_cat_limit \<alpha> \<open>:\<^sub>C I\<close> \<CC> \<open>:\<rightarrow>: I A \<CC>\<close> P \<pi> + tm_cf_discrete \<alpha> I A \<CC>
  for \<alpha> I A \<CC> P \<pi>

syntax "_is_tm_cat_obj_prod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Prod> _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_tm_cat_obj_prod \<alpha> I A \<CC> P \<pi>"

locale is_tm_cat_obj_coprod = 
  is_cat_colimit \<alpha> \<open>:\<^sub>C I\<close> \<CC> \<open>:\<rightarrow>: I A \<CC>\<close> U \<pi> + tm_cf_discrete \<alpha> I A \<CC>
  for \<alpha> I A \<CC> U \<pi>

syntax "_is_tm_cat_obj_coprod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Coprod> _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Coprod> U : I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_tm_cat_obj_coprod \<alpha> I A \<CC> U \<pi>"


text\<open>Rules.\<close>

lemma (in is_tm_cat_obj_prod) is_tm_cat_obj_prod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "P' = P" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Prod> A' : I' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_obj_prod_axioms)

mk_ide rf is_tm_cat_obj_prod_def
  |intro is_tm_cat_obj_prodI|
  |dest is_tm_cat_obj_prodD[dest]|
  |elim is_tm_cat_obj_prodE[elim]|

lemmas [cat_lim_cs_intros] = is_tm_cat_obj_prodD

lemma (in is_tm_cat_obj_coprod) 
  is_tm_cat_obj_coprod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "U' = U" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : A' >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Coprod> U' : I' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_obj_coprod_axioms)

mk_ide rf is_tm_cat_obj_coprod_def
  |intro is_tm_cat_obj_coprodI|
  |dest is_tm_cat_obj_coprodD[dest]|
  |elim is_tm_cat_obj_coprodE[elim]|

lemmas [cat_lim_cs_intros] = is_tm_cat_obj_coprodD


text\<open>Elementary properties.\<close>

sublocale is_tm_cat_obj_prod \<subseteq> is_cat_obj_prod
  by
    (
      intro is_cat_obj_prodI,
      rule is_cat_limit_axioms,
      rule cf_discrete_axioms
    )

lemmas (in is_tm_cat_obj_prod) tm_cat_obj_prod_is_cat_obj_prod = 
  is_cat_obj_prod_axioms

sublocale is_tm_cat_obj_coprod \<subseteq> is_cat_obj_coprod
  by 
    ( 
      intro is_cat_obj_coprodI, 
      rule is_cat_colimit_axioms, 
      rule cf_discrete_axioms
    )

lemmas (in is_tm_cat_obj_coprod) tm_cat_obj_coprod_is_cat_obj_coprod = 
  is_cat_obj_coprod_axioms

sublocale is_tm_cat_obj_prod \<subseteq> is_tm_cat_limit \<alpha> \<open>:\<^sub>C I\<close> \<CC> \<open>:\<rightarrow>: I A \<CC>\<close> P \<pi>
  by
    (
      intro
        is_tm_cat_limitI 
        is_tm_cat_coneI 
        is_ntcf_axioms 
        tm_cf_discrete_the_cf_discrete_is_tm_functor 
        cat_cone_obj 
        cat_lim_ua_fo
    )

lemmas (in is_tm_cat_obj_prod) tm_cat_obj_prod_is_tm_cat_limit =
  is_tm_cat_limit_axioms

sublocale is_tm_cat_obj_coprod \<subseteq> is_tm_cat_colimit \<alpha> \<open>:\<^sub>C I\<close> \<CC> \<open>:\<rightarrow>: I A \<CC>\<close> U \<pi>
  by
    (
      intro
        is_tm_cat_colimitI 
        is_tm_cat_coconeI 
        is_ntcf_axioms 
        tm_cf_discrete_the_cf_discrete_is_tm_functor 
        cat_cocone_obj 
        cat_colim_ua_of
    )

lemmas (in is_tm_cat_obj_coprod) tm_cat_obj_coprod_is_tm_cat_colimit =
  is_tm_cat_colimit_axioms


text\<open>Duality.\<close>

lemma (in is_tm_cat_obj_prod) is_tm_cat_obj_coprod_op:
  "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  using cf_discrete_vdomain_vsubset_Vset
  by (intro is_tm_cat_obj_coprodI) 
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)

lemma (in is_tm_cat_obj_prod) is_tm_cat_obj_coprod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_obj_coprod_op)

lemmas [cat_op_intros] = is_tm_cat_obj_prod.is_tm_cat_obj_coprod_op'

lemma (in is_tm_cat_obj_coprod) is_tm_cat_obj_coprod_op:
  "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  using cf_discrete_vdomain_vsubset_Vset
  by (intro is_tm_cat_obj_prodI)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)

lemma (in is_tm_cat_obj_coprod) is_tm_cat_obj_prod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_tm_cat_obj_coprod_op)

lemmas [cat_op_intros] = is_tm_cat_obj_coprod.is_tm_cat_obj_prod_op'



subsection\<open>Finite product and finite coproduct\<close>

locale is_cat_finite_obj_prod = is_cat_obj_prod \<alpha> I A \<CC> P \<pi> 
  for \<alpha> I A \<CC> P \<pi> +
  assumes cat_fin_obj_prod_index_in_\<omega>: "I \<in>\<^sub>\<circ> \<omega>" 

syntax "_is_cat_finite_obj_prod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_finite_obj_prod \<alpha> I A \<CC> P \<pi>"

locale is_cat_finite_obj_coprod = is_cat_obj_coprod \<alpha> I A \<CC> U \<pi> 
  for \<alpha> I A \<CC> U \<pi> +
  assumes cat_fin_obj_coprod_index_in_\<omega>: "I \<in>\<^sub>\<circ> \<omega>" 

syntax "_is_cat_finite_obj_coprod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n U : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_finite_obj_coprod \<alpha> I A \<CC> U \<pi>"

lemma (in is_cat_finite_obj_prod) cat_fin_obj_prod_index_vfinite: "vfinite I"
  using cat_fin_obj_prod_index_in_\<omega> by auto

sublocale is_cat_finite_obj_prod \<subseteq> I: finite_category \<alpha> \<open>:\<^sub>C I\<close>
  by (intro finite_categoryI')
    (
      auto
        simp: NTDom.HomDom.category_axioms the_cat_discrete_components
        intro!: cat_fin_obj_prod_index_vfinite
    )

lemma (in is_cat_finite_obj_coprod) cat_fin_obj_coprod_index_vfinite:
  "vfinite I"
  using cat_fin_obj_coprod_index_in_\<omega> by auto

sublocale is_cat_finite_obj_coprod \<subseteq> I: finite_category \<alpha> \<open>:\<^sub>C I\<close>
  by (intro finite_categoryI')
    (
      auto 
        simp: NTDom.HomDom.category_axioms the_cat_discrete_components 
        intro!: cat_fin_obj_coprod_index_vfinite
    )


text\<open>Rules.\<close>

lemma (in is_cat_finite_obj_prod) 
  is_cat_finite_obj_prod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "P' = P" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n A' : I' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_obj_prod_axioms)

mk_ide rf 
  is_cat_finite_obj_prod_def[unfolded is_cat_finite_obj_prod_axioms_def]
  |intro is_cat_finite_obj_prodI|
  |dest is_cat_finite_obj_prodD[dest]|
  |elim is_cat_finite_obj_prodE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_finite_obj_prodD

lemma (in is_cat_finite_obj_coprod) 
  is_cat_finite_obj_coprod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "U' = U" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : A' >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n U' : I' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_obj_coprod_axioms)

mk_ide rf 
  is_cat_finite_obj_coprod_def[unfolded is_cat_finite_obj_coprod_axioms_def]
  |intro is_cat_finite_obj_coprodI|
  |dest is_cat_finite_obj_coprodD[dest]|
  |elim is_cat_finite_obj_coprodE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_finite_obj_coprodD


text\<open>Duality.\<close>

lemma (in is_cat_finite_obj_prod) is_cat_finite_obj_coprod_op:
  "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_finite_obj_coprodI)
    (
      cs_concl cs_shallow
        cs_simp: cat_op_simps 
        cs_intro: cat_fin_obj_prod_index_in_\<omega> cat_cs_intros cat_op_intros
    )

lemma (in is_cat_finite_obj_prod) is_cat_finite_obj_coprod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_obj_coprod_op)

lemmas [cat_op_intros] = is_cat_finite_obj_prod.is_cat_finite_obj_coprod_op'

lemma (in is_cat_finite_obj_coprod) is_cat_finite_obj_prod_op:
  "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_finite_obj_prodI)
    (
      cs_concl cs_shallow
        cs_simp: cat_op_simps 
        cs_intro: cat_fin_obj_coprod_index_in_\<omega> cat_cs_intros cat_op_intros
    )

lemma (in is_cat_finite_obj_coprod) is_cat_finite_obj_prod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_obj_prod_op)

lemmas [cat_op_intros] = is_cat_finite_obj_coprod.is_cat_finite_obj_prod_op'



subsection\<open>Product and coproduct of two objects\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_cat_obj_prod_2 = is_cat_obj_prod \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 a b\<close> \<CC> P \<pi>
  for \<alpha> a b \<CC> P \<pi>

syntax "_is_cat_obj_prod_2" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {_,_} :/ 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_prod_2 \<alpha> a b \<CC> P \<pi>"

locale is_cat_obj_coprod_2 = is_cat_obj_coprod \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 a b\<close> \<CC> P \<pi>
  for \<alpha> a b \<CC> P \<pi>

syntax "_is_cat_obj_coprod_2" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ {_,_} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> _ :/ 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> U : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_coprod_2 \<alpha> a b \<CC> U \<pi>"

abbreviation proj_fst where "proj_fst \<pi> \<equiv> vpfst (\<pi>\<lparr>NTMap\<rparr>)"
abbreviation proj_snd where "proj_snd \<pi> \<equiv> vpsnd (\<pi>\<lparr>NTMap\<rparr>)"


text\<open>Rules.\<close>

lemma (in is_cat_obj_prod_2) is_cat_obj_prod_2_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "P' = P" and "a' = a" and "b' = b" and "\<CC>' = \<CC>" 
  shows "\<pi> : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a',b'} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_prod_2_axioms)

mk_ide rf is_cat_obj_prod_2_def
  |intro is_cat_obj_prod_2I|
  |dest is_cat_obj_prod_2D[dest]|
  |elim is_cat_obj_prod_2E[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_prod_2D

lemma (in is_cat_obj_coprod_2) is_cat_obj_coprod_2_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "P' = P" and "a' = a" and "b' = b" and "\<CC>' = \<CC>" 
  shows "\<pi> : {a',b'} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P' : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_coprod_2_axioms)

mk_ide rf is_cat_obj_coprod_2_def
  |intro is_cat_obj_coprod_2I|
  |dest is_cat_obj_coprod_2D[dest]|
  |elim is_cat_obj_coprod_2E[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_coprod_2D


text\<open>Duality.\<close>

lemma (in is_cat_obj_prod_2) is_cat_obj_coprod_2_op:
  "op_ntcf \<pi> : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (rule is_cat_obj_coprod_2I[OF is_cat_obj_coprod_op])

lemma (in is_cat_obj_prod_2) is_cat_obj_coprod_2_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_coprod_2_op)

lemmas [cat_op_intros] = is_cat_obj_prod_2.is_cat_obj_coprod_2_op'

lemma (in is_cat_obj_coprod_2) is_cat_obj_prod_2_op:
  "op_ntcf \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (rule is_cat_obj_prod_2I[OF is_cat_obj_prod_op])

lemma (in is_cat_obj_coprod_2) is_cat_obj_prod_2_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_prod_2_op)

lemmas [cat_op_intros] = is_cat_obj_coprod_2.is_cat_obj_prod_2_op'


text\<open>Product/coproduct of two objects is a finite product/coproduct.\<close>

sublocale is_cat_obj_prod_2 \<subseteq> is_cat_finite_obj_prod \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 a b\<close> \<CC> P \<pi>
proof(intro is_cat_finite_obj_prodI)
  show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
qed (cs_concl cs_shallow cs_simp: two[symmetric] cs_intro: cat_lim_cs_intros)

sublocale is_cat_obj_coprod_2 \<subseteq> is_cat_finite_obj_coprod \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 a b\<close> \<CC> P \<pi>
proof(intro is_cat_finite_obj_coprodI)
  show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
qed (cs_concl cs_shallow cs_simp: two[symmetric] cs_intro: cat_lim_cs_intros)


text\<open>Elementary properties.\<close>

lemma (in is_cat_obj_prod_2) cat_obj_prod_2_lr_in_Obj:
  shows cat_obj_prod_2_left_in_Obj[cat_lim_cs_intros]: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and cat_obj_prod_2_right_in_Obj[cat_lim_cs_intros]: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  have 0: "0 \<in>\<^sub>\<circ> 2\<^sub>\<nat>" and 1: "1\<^sub>\<nat> \<in>\<^sub>\<circ> 2\<^sub>\<nat>" by simp_all
  show "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by 
      (
        intro 
          cf_discrete_selector_vrange[OF 0, simplified]
          cf_discrete_selector_vrange[OF 1, simplified]
      )+
qed

lemmas [cat_lim_cs_intros] = is_cat_obj_prod_2.cat_obj_prod_2_lr_in_Obj

lemma (in is_cat_obj_coprod_2) cat_obj_coprod_2_lr_in_Obj:
  shows cat_obj_coprod_2_left_in_Obj[cat_lim_cs_intros]: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and cat_obj_coprod_2_right_in_Obj[cat_lim_cs_intros]: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  by 
    (
      intro is_cat_obj_prod_2.cat_obj_prod_2_lr_in_Obj[
        OF is_cat_obj_prod_2_op, unfolded cat_op_simps
        ]
    )+

lemmas [cat_lim_cs_intros] = is_cat_obj_coprod_2.cat_obj_coprod_2_lr_in_Obj


text\<open>Utilities/help lemmas.\<close>

lemma helper_I2_proj_fst_proj_snd_iff: 
  "(\<forall>j\<in>\<^sub>\<circ>2\<^sub>\<nat>. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f') \<longleftrightarrow>
    (proj_fst \<pi>' = proj_fst \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and> proj_snd \<pi>' = proj_snd \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')" 
  unfolding two by auto

lemma helper_I2_proj_fst_proj_snd_iff': 
  "(\<forall>j\<in>\<^sub>\<circ>2\<^sub>\<nat>. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>) \<longleftrightarrow>
    (proj_fst \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_fst \<pi> \<and> proj_snd \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_snd \<pi>)" 
  unfolding two by auto


subsubsection\<open>Universal property\<close>

lemma (in is_cat_obj_prod_2) cat_obj_prod_2_unique_cone':
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (2\<^sub>\<nat>) (if2 a b) \<CC> : :\<^sub>C (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and>
      proj_fst \<pi>' = proj_fst \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
      proj_snd \<pi>' = proj_snd \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  by 
    (
      rule cat_obj_prod_unique_cone'[
        OF assms, unfolded helper_I2_proj_fst_proj_snd_iff
        ]
    )

lemma (in is_cat_obj_prod_2) cat_obj_prod_2_unique:
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and> \<pi>' = \<pi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C (2\<^sub>\<nat>)) \<CC> f'"
  by (rule cat_obj_prod_unique[OF is_cat_obj_prod_2D[OF assms]])

lemma (in is_cat_obj_prod_2) cat_obj_prod_2_unique':
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and>
      proj_fst \<pi>' = proj_fst \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
      proj_snd \<pi>' = proj_snd \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  by 
    (
      rule cat_obj_prod_unique'[
        OF is_cat_obj_prod_2D[OF assms], 
        unfolded helper_I2_proj_fst_proj_snd_iff
        ]
    )

lemma (in is_cat_obj_coprod_2) cat_obj_coprod_2_unique_cocone':
  assumes "\<pi>' : :\<rightarrow>: (2\<^sub>\<nat>) (if2 a b) \<CC> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e P' : :\<^sub>C (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : P \<mapsto>\<^bsub>\<CC>\<^esub> P' \<and>
      proj_fst \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_fst \<pi> \<and>
      proj_snd \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_snd \<pi>"
  by 
    (
      rule cat_obj_coprod_unique_cocone'[
        OF assms, unfolded helper_I2_proj_fst_proj_snd_iff'
        ]
    )

lemma (in is_cat_obj_coprod_2) cat_obj_coprod_2_unique:
  assumes "\<pi>' : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P' : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P \<mapsto>\<^bsub>\<CC>\<^esub> P' \<and> \<pi>' = ntcf_const (:\<^sub>C (2\<^sub>\<nat>)) \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<pi>"
  by (rule cat_obj_coprod_unique[OF is_cat_obj_coprod_2D[OF assms]])

lemma (in is_cat_obj_coprod_2) cat_obj_coprod_2_unique':
  assumes "\<pi>' : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P' : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : P \<mapsto>\<^bsub>\<CC>\<^esub> P' \<and>
      proj_fst \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_fst \<pi> \<and>
      proj_snd \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_snd \<pi>"
  by 
    (
      rule cat_obj_coprod_unique'[
        OF is_cat_obj_coprod_2D[OF assms], 
        unfolded helper_I2_proj_fst_proj_snd_iff'
        ]
    )

lemma cat_obj_prod_2_ex_is_iso_arr:
  assumes "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : P' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> P" and "\<pi>' = \<pi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C (2\<^sub>\<nat>)) \<CC> f"
proof-
  interpret \<pi>: is_cat_obj_prod_2 \<alpha> a b \<CC> P \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_prod_2 \<alpha> a b \<CC> P' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_obj_prod_ex_is_iso_arr[
          OF \<pi>.is_cat_obj_prod_axioms \<pi>'.is_cat_obj_prod_axioms
          ]
      )
qed

lemma cat_obj_coprod_2_ex_is_iso_arr:
  assumes "\<pi> : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> U : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<pi>' : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> U' : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : U \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> U'" and "\<pi>' = ntcf_const (:\<^sub>C (2\<^sub>\<nat>)) \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<pi>"
proof-
  interpret \<pi>: is_cat_obj_coprod_2 \<alpha> a b \<CC> U \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_coprod_2 \<alpha> a b \<CC> U' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_obj_coprod_ex_is_iso_arr[
          OF \<pi>.is_cat_obj_coprod_axioms \<pi>'.is_cat_obj_coprod_axioms
          ]
      )
qed



subsection\<open>Projection cone\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntcf_obj_prod_base :: "V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "ntcf_obj_prod_base \<CC> I F P f =
    [(\<lambda>j\<in>\<^sub>\<circ>:\<^sub>C I\<lparr>Obj\<rparr>. f j), cf_const (:\<^sub>C I) \<CC> P, :\<rightarrow>: I F \<CC>, :\<^sub>C I, \<CC>]\<^sub>\<circ>"

definition ntcf_obj_coprod_base :: "V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "ntcf_obj_coprod_base \<CC> I F P f =
    [(\<lambda>j\<in>\<^sub>\<circ>:\<^sub>C I\<lparr>Obj\<rparr>. f j), :\<rightarrow>: I F \<CC>, cf_const (:\<^sub>C I) \<CC> P, :\<^sub>C I, \<CC>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_obj_prod_base_components:
  shows "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTMap\<rparr> = (\<lambda>j\<in>\<^sub>\<circ>:\<^sub>C I\<lparr>Obj\<rparr>. f j)"
    and "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTDom\<rparr> = cf_const (:\<^sub>C I) \<CC> P"
    and "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTCod\<rparr> = :\<rightarrow>: I F \<CC>"
    and "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTDGDom\<rparr> = :\<^sub>C I"
    and "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntcf_obj_prod_base_def nt_field_simps 
  by (simp_all add: nat_omega_simps)

lemma ntcf_obj_coprod_base_components:
  shows "ntcf_obj_coprod_base \<CC> I F P f\<lparr>NTMap\<rparr> = (\<lambda>j\<in>\<^sub>\<circ>:\<^sub>C I\<lparr>Obj\<rparr>. f j)"
    and "ntcf_obj_coprod_base \<CC> I F P f\<lparr>NTDom\<rparr> = :\<rightarrow>: I F \<CC>"
    and "ntcf_obj_coprod_base \<CC> I F P f\<lparr>NTCod\<rparr> = cf_const (:\<^sub>C I) \<CC> P"
    and "ntcf_obj_coprod_base \<CC> I F P f\<lparr>NTDGDom\<rparr> = :\<^sub>C I"
    and "ntcf_obj_coprod_base \<CC> I F P f\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntcf_obj_coprod_base_def nt_field_simps 
  by (simp_all add: nat_omega_simps)


text\<open>Duality.\<close>

lemma (in cf_discrete) op_ntcf_ntcf_obj_coprod_base[cat_op_simps]:
  "op_ntcf (ntcf_obj_coprod_base \<CC> I F P f) =
    ntcf_obj_prod_base (op_cat \<CC>) I F P f"
proof-
  note [cat_op_simps] = the_cat_discrete_op[OF cf_discrete_vdomain_vsubset_Vset]
  show ?thesis
    unfolding 
      ntcf_obj_prod_base_def ntcf_obj_coprod_base_def op_ntcf_def nt_field_simps
    by (simp add: nat_omega_simps cat_op_simps) 
qed

lemma (in cf_discrete) op_ntcf_ntcf_obj_prod_base[cat_op_simps]:
  "op_ntcf (ntcf_obj_prod_base \<CC> I F P f) =
    ntcf_obj_coprod_base (op_cat \<CC>) I F P f"
proof-
  note [cat_op_simps] = the_cat_discrete_op[OF cf_discrete_vdomain_vsubset_Vset]
  show ?thesis
    unfolding 
      ntcf_obj_prod_base_def ntcf_obj_coprod_base_def op_ntcf_def nt_field_simps
    by (simp add: nat_omega_simps cat_op_simps) 
qed


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_obj_prod_base_components(1)
  |vsv ntcf_obj_prod_base_NTMap_vsv[cat_cs_intros]|
  |vdomain ntcf_obj_prod_base_NTMap_vdomain[cat_cs_simps]|
  |app ntcf_obj_prod_base_NTMap_app[cat_cs_simps]|

mk_VLambda ntcf_obj_coprod_base_components(1)
  |vsv ntcf_obj_coprod_base_NTMap_vsv[cat_cs_intros]|
  |vdomain ntcf_obj_coprod_base_NTMap_vdomain[cat_cs_simps]|
  |app ntcf_obj_coprod_base_NTMap_app[cat_cs_simps]|


subsubsection\<open>Projection natural transformation is a cone\<close>

lemma (in tm_cf_discrete) tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone:
  assumes "P \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<And>a. a \<in>\<^sub>\<circ> I \<Longrightarrow> f a : P \<mapsto>\<^bsub>\<CC>\<^esub> F a"
  shows "ntcf_obj_prod_base \<CC> I F P f : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: I F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
  from assms(2) have [cat_cs_intros]: 
    "\<lbrakk> a \<in>\<^sub>\<circ> I; P' = P; Fa = F a \<rbrakk> \<Longrightarrow> f a : P' \<mapsto>\<^bsub>\<CC>\<^esub> Fa" for a P' Fa 
    by simp
  show "vfsequence (ntcf_obj_prod_base \<CC> I F P f)"
    unfolding ntcf_obj_prod_base_def by auto
  show "vcard (ntcf_obj_prod_base \<CC> I F P f) = 5\<^sub>\<nat>"
    unfolding ntcf_obj_prod_base_def by (auto simp: nat_omega_simps)
  from assms show "cf_const (:\<^sub>C I) \<CC> P : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by 
      (
        cs_concl 
          cs_intro: 
            cf_discrete_vdomain_vsubset_Vset 
            cat_discrete_cs_intros 
            cat_cs_intros
      )
  show ":\<rightarrow>: I F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_shallow cs_intro: cat_discrete_cs_intros)
  show "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
    cf_const (:\<^sub>C I) \<CC> P\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> :\<rightarrow>: I F \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> :\<^sub>C I\<lparr>Obj\<rparr>" for a
  proof-
    from that have "a \<in>\<^sub>\<circ> I" unfolding the_cat_discrete_components by simp
    from that this show ?thesis
      by 
        (
          cs_concl cs_shallow
            cs_simp: cat_cs_simps cat_discrete_cs_simps cs_intro: cat_cs_intros
        )
  qed
  show 
    "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
      cf_const (:\<^sub>C I) \<CC> P\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> =
      :\<rightarrow>: I F \<CC>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ntcf_obj_prod_base \<CC> I F P f\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    if "g : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b" for a b g
  proof-
    note g = the_cat_discrete_is_arrD[OF that]
    from that g(4)[unfolded g(7-9)] g(1)[unfolded g(7-9)] show ?thesis
      unfolding g(7-9)
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_discrete_cs_simps 
            cs_intro: 
              cf_discrete_vdomain_vsubset_Vset 
              cat_cs_intros cat_discrete_cs_intros
        )
  qed
qed 
  (
    auto simp: 
      assms 
      ntcf_obj_prod_base_components 
      tm_cf_discrete_the_cf_discrete_is_tm_functor
  )

lemma (in tm_cf_discrete) tm_cf_discrete_ntcf_obj_coprod_base_is_cat_cocone:
  assumes "P \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<And>a. a \<in>\<^sub>\<circ> I \<Longrightarrow> f a : F a \<mapsto>\<^bsub>\<CC>\<^esub> P"
  shows "ntcf_obj_coprod_base \<CC> I F P f :
    :\<rightarrow>: I F \<CC> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e P : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  note [cat_op_simps] =
    the_cat_discrete_op[OF cf_discrete_vdomain_vsubset_Vset]
    cf_discrete.op_ntcf_ntcf_obj_prod_base[OF cf_discrete_op]
    cf_discrete.cf_discrete_the_cf_discrete_op[OF cf_discrete_op]
  have "op_ntcf (ntcf_obj_coprod_base \<CC> I F P f) :
    P <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e op_cf (:\<rightarrow>: I F \<CC>) : op_cat (:\<^sub>C I) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    unfolding cat_op_simps
    by
      (
        rule tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone[
          OF tm_cf_discrete_op, unfolded cat_op_simps, OF assms
          ]
      )
  from is_cat_cone.is_cat_cocone_op[OF this, unfolded cat_op_simps] 
  show ?thesis .
qed

lemma (in tm_cf_discrete) tm_cf_discrete_ntcf_obj_prod_base_is_cat_obj_prod:
  assumes "P \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "\<And>a. a \<in>\<^sub>\<circ> I \<Longrightarrow> f a : P \<mapsto>\<^bsub>\<CC>\<^esub> F a"
    and "\<And>u' r'.
      \<lbrakk> u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: I F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<rbrakk> \<Longrightarrow> 
        \<exists>!f'.
          f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and>
          u' = ntcf_obj_prod_base \<CC> I F P f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) \<CC> f'"
  shows "ntcf_obj_prod_base \<CC> I F P f : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> F : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof
  (
    intro 
      is_cat_obj_prodI 
      is_cat_limitI 
      tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone[OF assms(1,2), simplified] 
      assms(1,3)
  )
  show "cf_discrete \<alpha> I F \<CC>"
    by (cs_concl cs_shallow cs_intro: cat_small_discrete_cs_intros)
qed

lemma (in tm_cf_discrete) tm_cf_discrete_ntcf_obj_coprod_base_is_cat_obj_coprod:
  assumes "P \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "\<And>a. a \<in>\<^sub>\<circ> I \<Longrightarrow> f a : F a \<mapsto>\<^bsub>\<CC>\<^esub> P"
    and "\<And>u' r'. \<lbrakk> u' : :\<rightarrow>: I F \<CC> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<rbrakk> \<Longrightarrow>
      \<exists>!f'.
        f' : P \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and>
        u' = ntcf_const (:\<^sub>C I) \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_obj_coprod_base \<CC> I F P f"
  shows "ntcf_obj_coprod_base \<CC> I F P f : F >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    (is \<open>?nc : F >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>\<close>)
proof-
  let ?np = \<open>ntcf_obj_prod_base (op_cat \<CC>) I F P f\<close>
  interpret is_cat_cocone \<alpha> P \<open>:\<^sub>C I\<close> \<CC> \<open>:\<rightarrow>: I F \<CC>\<close> ?nc
    by (intro tm_cf_discrete_ntcf_obj_coprod_base_is_cat_cocone[OF assms(1,2)])
  note [cat_op_simps] =
    the_cat_discrete_op[OF cf_discrete_vdomain_vsubset_Vset]
    cf_discrete.op_ntcf_ntcf_obj_prod_base[OF cf_discrete_op]
    cf_discrete.cf_discrete_the_cf_discrete_op[OF cf_discrete_op]
  have "\<exists>!f'.
    f' : P \<mapsto>\<^bsub>\<CC>\<^esub> r \<and>
    u = ?np \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (op_cat \<CC>) f'"
    if "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: I F (op_cat \<CC>) : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>" for u r
  proof-
    interpret u: is_cat_cone \<alpha> r \<open>:\<^sub>C I\<close> \<open>op_cat \<CC>\<close> \<open>:\<rightarrow>: I F (op_cat \<CC>)\<close> u
      by (rule that)
    from assms(3)[OF u.is_cat_cocone_op[unfolded cat_op_simps]] obtain g 
      where g: "g : P \<mapsto>\<^bsub>\<CC>\<^esub> r"
        and op_u: "op_ntcf u = ntcf_const (:\<^sub>C I) \<CC> g \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?nc"
        and g_unique: 
          "\<lbrakk> g' : P \<mapsto>\<^bsub>\<CC>\<^esub> r; op_ntcf u = ntcf_const (:\<^sub>C I) \<CC> g' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?nc \<rbrakk> \<Longrightarrow>
            g' = g"
      for g'
      by metis
    show ?thesis
    proof(intro ex1I conjI; (elim conjE)?)
      from op_u have 
        "op_ntcf (op_ntcf u) = op_ntcf (ntcf_const (:\<^sub>C I) \<CC> g \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?nc)"
        by simp
      from this g show "u = ?np \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (op_cat \<CC>) g"
        by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros)
      fix g' assume prems:
        "g' : P \<mapsto>\<^bsub>\<CC>\<^esub> r"
        "u = ?np \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (op_cat \<CC>) g'"
      from prems(2) have 
        "op_ntcf u = op_ntcf (?np \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (op_cat \<CC>) g')"
        by simp
      from this prems(1) g have "op_ntcf u = ntcf_const (:\<^sub>C I) \<CC> g' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?nc"
        by 
          (
            subst (asm) 
              the_cat_discrete_op[OF cf_discrete_vdomain_vsubset_Vset, symmetric]
          )
          (
            cs_prems 
              cs_simp: 
                cat_op_simps 
                op_ntcf_ntcf_vcomp[symmetric] 
                is_ntcf.ntcf_op_ntcf_op_ntcf 
                op_ntcf_ntcf_obj_coprod_base[symmetric] 
                op_ntcf_ntcf_const[symmetric]
              cs_intro: cat_cs_intros cat_op_intros
          )
      from g_unique[OF prems(1) this] show "g' = g" .
    qed (rule g)
  qed
  from is_cat_obj_prod.is_cat_obj_coprod_op
    [
      OF tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_obj_prod
        [
          OF tm_cf_discrete_op, 
          unfolded cat_op_simps,
          OF assms(1,2) this, 
          folded op_ntcf_ntcf_obj_coprod_base
        ],
      unfolded cat_op_simps
    ]
  show "?nc : F >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>".
qed

text\<open>\newpage\<close>

end