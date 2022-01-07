(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Completeness for categories\<close>
theory CZH_UCAT_Complete
  imports CZH_UCAT_Limit
begin



subsection\<open>Small-complete category\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale cat_small_complete = category \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_small_complete: 
    "\<And>\<FF> \<JJ>. \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow> \<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"

locale cat_small_cocomplete = category \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_small_cocomplete: 
    "\<And>\<FF> \<JJ>. \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow> \<exists>u r. u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"


text\<open>Rules.\<close>

mk_ide rf cat_small_complete_def[unfolded cat_small_complete_axioms_def]
  |intro cat_small_completeI|
  |dest cat_small_completeD[dest]|
  |elim cat_small_completeE[elim]|

lemma cat_small_completeE'[elim]:
  assumes "cat_small_complete \<alpha> \<CC>" and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains u r where "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by auto

mk_ide rf cat_small_cocomplete_def[unfolded cat_small_cocomplete_axioms_def]
  |intro cat_small_cocompleteI|
  |dest cat_small_cocompleteD[dest]|
  |elim cat_small_cocompleteE[elim]|

lemma cat_small_cocompleteE'[elim]:
  assumes "cat_small_cocomplete \<alpha> \<CC>" and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains u r where "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by auto


subsubsection\<open>Duality\<close>

lemma (in cat_small_complete) cat_small_cocomplete_op[cat_op_intros]:
  "cat_small_cocomplete \<alpha> (op_cat \<CC>)"
proof(intro cat_small_cocompleteI)
  fix \<FF> \<JJ> assume "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  then interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<open>op_cat \<CC>\<close> \<FF> .
  from cat_small_complete[OF \<FF>.is_tm_functor_op[unfolded cat_op_simps]]
  obtain u r where u: "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by auto
  then interpret u: is_cat_limit \<alpha> \<open>op_cat \<JJ>\<close> \<CC> \<open>op_cf \<FF>\<close> r u .
  from u.is_cat_colimit_op[unfolded cat_op_simps] show 
    "\<exists>u r. u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by auto
qed (auto intro: cat_cs_intros)

lemmas [cat_op_intros] = cat_small_complete.cat_small_cocomplete_op

lemma (in cat_small_cocomplete) cat_small_complete_op[cat_op_intros]:
  "cat_small_complete \<alpha> (op_cat \<CC>)"
proof(intro cat_small_completeI)
  fix \<FF> \<JJ> assume prems: "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  then interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<open>op_cat \<CC>\<close> \<FF> .
  from cat_small_cocomplete[OF \<FF>.is_tm_functor_op[unfolded cat_op_simps]]
  obtain u r where u: "u : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by auto
  interpret u: is_cat_colimit \<alpha> \<open>op_cat \<JJ>\<close> \<CC> \<open>op_cf \<FF>\<close> r u by (rule u)
  from u.is_cat_limit_op[unfolded cat_op_simps] show 
    "\<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by auto
qed (auto intro: cat_cs_intros)

lemmas [cat_op_intros] = cat_small_cocomplete.cat_small_complete_op


subsubsection\<open>A category with equalizers and small products is small-complete\<close>

lemma (in category) cat_small_complete_if_eq_and_obj_prod:
  \<comment>\<open>See Corollary 2 in Chapter V-2 in \cite{mac_lane_categories_2010}\<close>
  assumes "\<And>\<aa> \<bb> \<gg> \<ff>. \<lbrakk> \<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>; \<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb> \<rbrakk> \<Longrightarrow>
      \<exists>E \<epsilon>. \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A I. tm_cf_discrete \<alpha> I A \<CC> \<Longrightarrow> \<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cat_small_complete \<alpha> \<CC>"
proof(intro cat_small_completeI)
  fix \<FF> \<JJ> assume prems: "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  then interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> .
  show "\<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (rule cat_limit_of_cat_prod_obj_and_cat_equalizer[OF prems assms(1)])
      (auto intro: assms(2))
qed (auto simp: cat_cs_intros)

lemma (in category) cat_small_cocomplete_if_eq_and_obj_prod:
  assumes "\<And>\<aa> \<bb> \<gg> \<ff>. \<lbrakk> \<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>; \<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa> \<rbrakk> \<Longrightarrow>
    \<exists>E \<epsilon>. \<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A I. tm_cf_discrete \<alpha> I A \<CC> \<Longrightarrow> \<exists>P \<pi>. \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cat_small_cocomplete \<alpha> \<CC>"
proof-
  have "\<exists>E \<epsilon>. \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" and "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" for \<aa> \<bb> \<gg> \<ff>
  proof-
    from assms(1)[OF that] obtain \<epsilon> E where 
      \<epsilon>: "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by clarsimp
    interpret \<epsilon>: is_cat_coequalizer_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule \<epsilon>)
    from \<epsilon>.is_cat_equalizer_2_op show ?thesis by auto
  qed
  moreover have "\<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "tm_cf_discrete \<alpha> I A (op_cat \<CC>)" for A I
  proof-
    interpret tm_cf_discrete \<alpha> I A \<open>op_cat \<CC>\<close> by (rule that)
    from assms(2)[OF tm_cf_discrete_op[unfolded cat_op_simps]] obtain P \<pi> 
      where \<pi>: "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by auto
    interpret \<pi>: is_cat_obj_coprod \<alpha> I A \<CC> P \<pi> by (rule \<pi>)
    from \<pi>.is_cat_obj_prod_op show ?thesis by auto
  qed
  ultimately interpret cat_small_complete \<alpha> \<open>op_cat \<CC>\<close>
    by 
      (
        rule category.cat_small_complete_if_eq_and_obj_prod[
          OF category_op, unfolded cat_op_simps
          ]
      )
  show ?thesis by (rule cat_small_cocomplete_op[unfolded cat_op_simps])
qed


subsubsection\<open>
Existence of the initial and terminal objects in small-complete categories
\<close>

lemma (in cat_small_complete) cat_sc_ex_obj_initial:
  \<comment>\<open>See Theorem 1 in Chapter V-6 in \cite{mac_lane_categories_2010}.\<close>
  assumes "A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "A \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<exists>f a. a \<in>\<^sub>\<circ> A \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
  obtains z where "obj_initial \<CC> z"
proof-
  
  interpret tcd: tm_cf_discrete \<alpha> A id \<CC>
  proof(intro tm_cf_discreteI)
    show "(\<lambda>i\<in>\<^sub>\<circ>A. \<CC>\<lparr>CId\<rparr>\<lparr>id i\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      unfolding id_def
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      from assms(1) have "A \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>)" by (simp add: cat_CId_vdomain)
      then have "\<R>\<^sub>\<circ> (VLambda A (app (\<CC>\<lparr>CId\<rparr>))) = \<CC>\<lparr>CId\<rparr> `\<^sub>\<circ> A" by auto
      moreover have "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>A. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
        by (rule cat_Hom_vifunion_in_Vset[OF assms(1,1,2,2)])
      moreover have "\<CC>\<lparr>CId\<rparr> `\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>A. Hom \<CC> a b)"
      proof(intro vsubsetI)
        fix f assume "f \<in>\<^sub>\<circ> \<CC>\<lparr>CId\<rparr> `\<^sub>\<circ> A"
        then obtain a where a: "a \<in>\<^sub>\<circ> A" and f_def: "f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>" by auto
        from assms(1) a show "f \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>A. Hom \<CC> a b)"
          unfolding f_def by (intro vifunionI) (auto simp: cat_CId_is_arr)
      qed
      ultimately show "\<R>\<^sub>\<circ> (VLambda A (app (\<CC>\<lparr>CId\<rparr>))) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
    qed (simp_all add: assms(2))
  qed 
    (
      use assms in 
        \<open>auto simp: assms(2) Limit_vid_on_in_Vset intro: cat_cs_intros\<close>
    )

  have tcd: ":\<rightarrow>: A id \<CC> : :\<^sub>C A \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by 
      (
        cs_concl cs_shallow cs_intro: 
          cat_small_cs_intros 
          cat_cs_intros 
          cat_small_discrete_cs_intros
          cat_discrete_cs_intros
      )
  from cat_small_complete[OF this] obtain \<pi> w 
    where "\<pi> : w <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m :\<rightarrow>: A id \<CC> : :\<^sub>C A \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by auto
  then interpret \<pi>: is_cat_obj_prod \<alpha> A id \<CC> w \<pi>
    by (intro is_cat_obj_prodI tcd.cf_discrete_axioms)

  let ?ww = \<open>Hom \<CC> w w\<close>

  have CId_w: "\<CC>\<lparr>CId\<rparr>\<lparr>w\<rparr> \<in>\<^sub>\<circ> Hom \<CC> w w"
    by (cs_concl cs_shallow cs_intro: cat_cs_intros cat_lim_cs_intros)
  then have ww_neq_vempty: "Hom \<CC> w w \<noteq> 0" by force

  have wd: "\<exists>h. h : w \<mapsto>\<^bsub>\<CC>\<^esub> d" if "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for d
  proof-
    from assms(3)[OF that] obtain g a where a: "a \<in>\<^sub>\<circ> A" and g: "g : a \<mapsto>\<^bsub>\<CC>\<^esub> d"
      by clarsimp
    from \<pi>.ntcf_NTMap_is_arr[unfolded the_cat_discrete_components, OF a] a g 
    have "\<pi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : w \<mapsto>\<^bsub>\<CC>\<^esub> a"
      by
        (
          cs_prems cs_shallow cs_simp:
            id_apply the_cat_discrete_components(1) 
            cat_discrete_cs_simps cat_cs_simps
        )
    with g have "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : w \<mapsto>\<^bsub>\<CC>\<^esub> d"
      by (cs_concl cs_shallow cs_intro: cat_cs_intros)
    then show ?thesis by (intro exI)
  qed

  have "cf_parallel \<alpha> (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww w w (vid_on ?ww) \<CC>"
    by (intro cat_cf_parallel_\<aa>\<bb> \<pi>.cat_cone_obj cat_Hom_in_Vset) simp_all
  then have "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww w w (vid_on ?ww) :
    \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by (intro cf_parallel.cf_parallel_the_cf_parallel_is_tm_functor)
  from cat_small_complete[OF this] obtain \<epsilon> v where \<epsilon>: "\<epsilon> :
    v <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww w w (vid_on ?ww) :
    \<Up>\<^sub>C (\<aa>\<^sub>P\<^sub>L ?ww) (\<bb>\<^sub>P\<^sub>L ?ww) ?ww \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by clarsimp
  from is_cat_equalizerI[
      OF
        this
        _ 
        cat_Hom_in_Vset[OF \<pi>.cat_cone_obj \<pi>.cat_cone_obj]
        ww_neq_vempty
      ]
  interpret \<epsilon>: is_cat_equalizer \<alpha> w w ?ww \<open>vid_on ?ww\<close> \<CC> v \<epsilon> by auto
  note \<epsilon>_is_monic_arr = 
    is_cat_equalizer.cat_eq_is_monic_arr[OF \<epsilon>.is_cat_equalizer_axioms]
  note \<epsilon>_is_monic_arrD = is_monic_arrD[OF \<epsilon>_is_monic_arr]

  show ?thesis
  proof(rule, intro obj_initialI)

    show "v \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (rule \<epsilon>.cat_cone_obj)
    then have CId_v: "\<CC>\<lparr>CId\<rparr>\<lparr>v\<rparr> : v \<mapsto>\<^bsub>\<CC>\<^esub> v" 
      by (cs_concl cs_shallow cs_intro: cat_cs_intros)

    fix d assume prems: "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    from wd[OF prems] obtain h where h: "h : w \<mapsto>\<^bsub>\<CC>\<^esub> d" by auto

    show "\<exists>!f. f : v \<mapsto>\<^bsub>\<CC>\<^esub> d"
    proof(rule ex1I)
      define f where "f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>"
      from \<epsilon>_is_monic_arrD(1) h show f: "f : v \<mapsto>\<^bsub>\<CC>\<^esub> d"
        unfolding f_def by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      fix g assume prems': "g : v \<mapsto>\<^bsub>\<CC>\<^esub> d"
      have "cf_parallel_2 \<alpha> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L v d g f \<CC>"
        by (intro cat_cf_parallel_2_cat_equalizer prems' f)
      then have "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L v d g f :
        \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
        by (intro cf_parallel_2.cf_parallel_2_the_cf_parallel_2_is_tm_functor)
      from cat_small_complete[OF this] obtain \<epsilon>' u 
        where "\<epsilon>' :
          u <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L v d g f :
          \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by clarsimp
      from is_cat_equalizer_2I[OF this prems' f] interpret \<epsilon>': 
        is_cat_equalizer_2 \<alpha> v d g f \<CC> u \<epsilon>'.
      note \<epsilon>'_is_monic_arr = is_cat_equalizer_2.cat_eq_2_is_monic_arr[
        OF \<epsilon>'.is_cat_equalizer_2_axioms
        ]
      note \<epsilon>'_is_monic_arrD = is_monic_arrD[OF \<epsilon>'_is_monic_arr]
      then have "u \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
      from wd[OF this] obtain s where s: "s : w \<mapsto>\<^bsub>\<CC>\<^esub> u" by clarsimp
      from s \<epsilon>'_is_monic_arrD(1) \<epsilon>_is_monic_arrD(1) have \<epsilon>\<epsilon>'s:
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s : w \<mapsto>\<^bsub>\<CC>\<^esub> w"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)
      from s \<epsilon>'_is_monic_arrD(1) \<epsilon>_is_monic_arrD(1) have \<epsilon>'s\<epsilon>:
        "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L (Hom \<CC> w w)\<rparr> : v \<mapsto>\<^bsub>\<CC>\<^esub> v"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from \<epsilon>_is_monic_arrD(1) \<epsilon>'_is_monic_arrD(1) s have 
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>) =
          \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      also from
        \<epsilon>.cat_eq_Comp_eq
          [
            unfolded in_Hom_iff, OF cat_CId_is_arr[OF \<pi>.cat_cone_obj] \<epsilon>\<epsilon>'s,
            symmetric
          ]
        \<epsilon>\<epsilon>'s \<pi>.cat_cone_obj \<epsilon>_is_monic_arr(1)
      have "\<dots> = \<CC>\<lparr>CId\<rparr>\<lparr>w\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>"
        by (cs_prems cs_shallow cs_simp: vid_on_atI cs_intro:  cat_cs_intros)
      also from \<epsilon>.cf_parallel_\<aa>' \<epsilon>_is_monic_arrD(1) have 
        "\<dots> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>v\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro:  cat_cs_intros)
      finally have
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>) =
          \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>v\<rparr>".      
      from 
        is_monic_arrD(2)[OF \<epsilon>_is_monic_arr \<epsilon>'s\<epsilon> CId_v this] 
        \<epsilon>'_is_monic_arrD(1) s \<epsilon>_is_monic_arrD(1) 
      have \<epsilon>'s\<epsilon>_is_CId: 
        "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (s \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L ?ww\<rparr>) = \<CC>\<lparr>CId\<rparr>\<lparr>v\<rparr>"
        by (cs_prems cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      have \<epsilon>'_is_arr_isomorphism: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> : u \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> v"
        by 
        (
          intro 
            cat_is_arr_isomorphism_if_is_monic_arr_is_right_inverse 
            \<epsilon>'_is_monic_arr,
          rule is_right_inverseI[OF _ \<epsilon>'_is_monic_arrD(1) \<epsilon>'s\<epsilon>_is_CId]
        )
        (
          use s \<epsilon>_is_monic_arrD(1) in 
            \<open>cs_concl cs_shallow cs_intro: cat_cs_intros\<close>
        )
      from \<epsilon>'.cat_eq_2_Comp_eq(1) have 
        "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> =
          f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>"
        by simp      
      from this f \<epsilon>'_is_monic_arrD(1) \<epsilon>'_is_arr_isomorphism prems' show "g = f"
        by
          (
            cs_prems cs_shallow
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_arrow_cs_intros
          )
    qed

  qed

qed

lemma (in cat_small_cocomplete) cat_sc_ex_obj_terminal:
  \<comment>\<open>See Theorem 1 in Chapter V-6 in \cite{mac_lane_categories_2010}.\<close>
  assumes "A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "A \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<exists>f a. a \<in>\<^sub>\<circ> A \<and> f : c \<mapsto>\<^bsub>\<CC>\<^esub> a"
  obtains z where "obj_terminal \<CC> z"
  using that 
  by 
    (
      rule cat_small_complete.cat_sc_ex_obj_initial[
        OF cat_small_complete_op, unfolded cat_op_simps, OF assms, simplified
        ]
    )



subsection\<open>Finite-complete category\<close>

locale cat_finite_complete = category \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_finite_complete: 
    "\<And>\<FF> \<JJ>. \<lbrakk> finite_category \<alpha> \<JJ>; \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<rbrakk> \<Longrightarrow> 
      \<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"

locale cat_finite_cocomplete = category \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_finite_cocomplete: 
    "\<And>\<FF> \<JJ>. \<lbrakk> finite_category \<alpha> \<JJ>; \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<rbrakk> \<Longrightarrow> 
      \<exists>u r. u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"


text\<open>Rules.\<close>

mk_ide rf cat_finite_complete_def[unfolded cat_finite_complete_axioms_def]
  |intro cat_finite_completeI|
  |dest cat_finite_completeD[dest]|
  |elim cat_finite_completeE[elim]|

lemma cat_finite_completeE'[elim]:
  assumes "cat_finite_complete \<alpha> \<CC>" 
    and "finite_category \<alpha> \<JJ>" 
    and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains u r where "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by auto

mk_ide rf cat_finite_cocomplete_def[unfolded cat_finite_cocomplete_axioms_def]
  |intro cat_finite_cocompleteI|
  |dest cat_finite_cocompleteD[dest]|
  |elim cat_finite_cocompleteE[elim]|

lemma cat_finite_cocompleteE'[elim]:
  assumes "cat_finite_cocomplete \<alpha> \<CC>" 
    and "finite_category \<alpha> \<JJ>" 
    and "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains u r where "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by auto


text\<open>Elementary properties.\<close>

sublocale cat_small_complete \<subseteq> cat_finite_complete
proof(intro cat_finite_completeI)
  fix \<FF> \<JJ> assume prems: "finite_category \<alpha> \<JJ>" "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  interpret \<FF>: is_functor \<alpha> \<JJ> \<CC> \<FF> by (rule prems(2))
  from cat_small_complete_axioms show "\<exists>u r. u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (auto intro: \<FF>.cf_is_tm_functor_if_HomDom_finite_category[OF prems(1)])
qed (auto intro: cat_cs_intros)

sublocale cat_small_cocomplete \<subseteq> cat_finite_cocomplete
proof(intro cat_finite_cocompleteI)
  fix \<FF> \<JJ> assume prems: "finite_category \<alpha> \<JJ>" "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  interpret \<FF>: is_functor \<alpha> \<JJ> \<CC> \<FF> by (rule prems(2))
  from cat_small_cocomplete_axioms show "\<exists>u r. u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (auto intro: \<FF>.cf_is_tm_functor_if_HomDom_finite_category[OF prems(1)])
qed (auto intro: cat_cs_intros)



subsection\<open>Discrete functor with tiny maps to the category \<open>Set\<close>\<close>

lemma (in \<Z>) tm_cf_discrete_cat_Set_if_VLambda_in_Vset:
  assumes "VLambda I F \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "tm_cf_discrete \<alpha> I F (cat_Set \<alpha>)"
proof(intro tm_cf_discreteI)
  from assms have vrange_F_in_Vset: "\<R>\<^sub>\<circ> (VLambda I F) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (auto intro: vrange_in_VsetI)
  show "(\<lambda>i\<in>\<^sub>\<circ>I. cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>F i\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
  proof(rule vbrelation.vbrelation_Limit_in_VsetI)
    from assms show "\<D>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>F i\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (metis vdomain_VLambda vdomain_in_VsetI)
    define Q where
      "Q i =
        (
          if i = 0
          then VPow ((\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i) \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)) 
          else set (F ` elts I)
        )" 
      for i :: V
    have "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>F i\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
    proof(intro vsubsetI, unfold cat_Set_components)
      fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. VLambda (Vset \<alpha>) id_Set\<lparr>F i\<rparr>)"
      then obtain i where i: "i \<in>\<^sub>\<circ> I" 
        and y_def: "y = VLambda (Vset \<alpha>) id_Set\<lparr>F i\<rparr>" 
        by auto
      from i have "F i \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (VLambda I F)" by auto
      with vrange_F_in_Vset have "F i \<in>\<^sub>\<circ> Vset \<alpha>" by auto
      then have y_def: "y = id_Set (F i)" unfolding y_def by auto
      show "y \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
        unfolding y_def
      proof(intro vproductI, unfold Ball_def; (intro allI impI)?)
        show "\<D>\<^sub>\<circ> (id_Rel (F i)) = set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"  
          by (simp add: id_Rel_def incl_Rel_def three nat_omega_simps)
        fix j assume "j \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
        then consider \<open>j = 0\<close> | \<open>j = 1\<^sub>\<nat>\<close> | \<open>j = 2\<^sub>\<nat>\<close> by auto
        then show "id_Rel (F i)\<lparr>j\<rparr> \<in>\<^sub>\<circ> Q j"
        proof cases
          case 1
          from i show ?thesis
            unfolding 1
            by 
              (
                subst arr_field_simps(1)[symmetric], 
                unfold id_Rel_components Q_def
              )
              force
        next
          case 2
          from i show ?thesis
            unfolding 2
            by 
              (
                subst arr_field_simps(2)[symmetric], 
                unfold id_Rel_components Q_def
              ) 
              auto
        next
          case 3
          from i show ?thesis
            unfolding 3
            by 
              (
                subst arr_field_simps(3)[symmetric], 
                unfold id_Rel_components Q_def
              ) 
              auto
        qed
      qed (auto simp: id_Rel_def cat_Set_cs_intros)
    qed
    moreover have "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule Limit_vproduct_in_VsetI)
      show "set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>} \<in>\<^sub>\<circ> Vset \<alpha>" unfolding three[symmetric] by simp
      from assms have "VPow ((\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i) \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)) \<in>\<^sub>\<circ> Vset \<alpha>"
        by 
          (
            intro 
              Limit_VPow_in_VsetI 
              Limit_vtimes_in_VsetI 
              Limit_vifunion_in_Vset_if_VLambda_in_VsetI
          )
          auto
      then show "Q i \<in>\<^sub>\<circ> Vset \<alpha>" if "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}" for i
        using that vrange_VLambda
        by (auto intro!: vrange_F_in_Vset simp: Q_def nat_omega_simps)
    qed auto
    ultimately show "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>F i\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (meson vsubset_in_VsetI) 
  qed auto
  fix i assume prems: "i \<in>\<^sub>\<circ> I"
  from assms have "\<R>\<^sub>\<circ> (VLambda I F) \<in>\<^sub>\<circ> Vset \<alpha>" by (auto simp: vrange_in_VsetI)
  moreover from prems have "F i \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (VLambda I F)" by auto
  ultimately show "F i \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" unfolding cat_Set_components by auto    
qed (cs_concl cs_shallow cs_intro: cat_cs_intros assms)+



subsection\<open>Product cone for the category \<open>Set\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntcf_Set_obj_prod :: "V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "ntcf_Set_obj_prod \<alpha> I F = ntcf_obj_prod_base 
    (cat_Set \<alpha>) I F (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i) (\<lambda>i. vprojection_arrow I F i)"


text\<open>Components.\<close>

lemma ntcf_Set_obj_prod_components:
  shows "ntcf_Set_obj_prod \<alpha> I F\<lparr>NTMap\<rparr> =
    (\<lambda>i\<in>\<^sub>\<circ>:\<^sub>C I\<lparr>Obj\<rparr>. vprojection_arrow I F i)"
    and "ntcf_Set_obj_prod \<alpha> I F\<lparr>NTDom\<rparr> =
    cf_const (:\<^sub>C I) (cat_Set \<alpha>) (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)"
    and "ntcf_Set_obj_prod \<alpha> I F\<lparr>NTCod\<rparr> = :\<rightarrow>: I F (cat_Set \<alpha>)"
    and "ntcf_Set_obj_prod \<alpha> I F\<lparr>NTDGDom\<rparr> = :\<^sub>C I"
    and "ntcf_Set_obj_prod \<alpha> I F\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding ntcf_Set_obj_prod_def ntcf_obj_prod_base_components by simp_all


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_Set_obj_prod_components(1)
  |vsv ntcf_Set_obj_prod_NTMap_vsv[cat_cs_intros]|
  |vdomain ntcf_Set_obj_prod_NTMap_vdomain[cat_cs_simps]|
  |app ntcf_Set_obj_prod_NTMap_app[cat_cs_simps]|


subsubsection\<open>Product cone for the category \<open>Set\<close> is a universal cone\<close>

lemma (in \<Z>) tm_cf_discrete_ntcf_obj_prod_base_is_cat_obj_prod:
  \<comment>\<open>See Theorem 5.2 in Chapter Introduction in \cite{hungerford_algebra_2003}.\<close>
  assumes "VLambda I F \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "ntcf_Set_obj_prod \<alpha> I F : (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i) <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> F : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof(intro is_cat_obj_prodI is_cat_limitI)

  interpret Set: tm_cf_discrete \<alpha> I F \<open>cat_Set \<alpha>\<close> 
    by (rule tm_cf_discrete_cat_Set_if_VLambda_in_Vset[OF assms])

  let ?F = \<open>ntcf_Set_obj_prod \<alpha> I F\<close>

  show "cf_discrete \<alpha> I F (cat_Set \<alpha>)"
    by (auto simp: cat_small_discrete_cs_intros)
  show F_is_cat_cone: "?F :
    (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i) <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: I F (cat_Set \<alpha>) : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      unfolding ntcf_Set_obj_prod_def
  proof(rule Set.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone)
    show "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i) \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
      unfolding cat_Set_components
      by 
        (
          intro 
            Limit_vproduct_in_Vset_if_VLambda_in_VsetI 
            Set.tm_cf_discrete_ObjMap_in_Vset
        ) 
        auto
  qed (intro vprojection_arrow_is_arr Set.tm_cf_discrete_ObjMap_in_Vset)

  interpret F: is_cat_cone 
    \<alpha> \<open>\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i\<close> \<open>:\<^sub>C I\<close> \<open>cat_Set \<alpha>\<close> \<open>:\<rightarrow>: I F (cat_Set \<alpha>)\<close> \<open>?F\<close>
    by (rule F_is_cat_cone)

  fix \<pi>' P' assume prems:
    "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: I F (cat_Set \<alpha>) : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"

  let ?\<pi>'i = \<open>\<lambda>i. \<pi>'\<lparr>NTMap\<rparr>\<lparr>i\<rparr>\<close>
  let ?up' = \<open>cat_Set_obj_prod_up I F P' ?\<pi>'i\<close>

  interpret \<pi>': is_cat_cone \<alpha> P' \<open>:\<^sub>C I\<close> \<open>cat_Set \<alpha>\<close> \<open>:\<rightarrow>: I F (cat_Set \<alpha>)\<close> \<pi>'
    by (rule prems(1))

  show "\<exists>!f'.
    f' : P' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i) \<and>
    \<pi>' = ?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (cat_Set \<alpha>) f'"
  proof(intro ex1I conjI; (elim conjE)?)
    show up': "?up' : P' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)" 
    proof(rule cat_Set_obj_prod_up_cat_Set_is_arr)
      show "P' \<in>\<^sub>\<circ> Vset \<alpha>" by (auto intro: cat_cs_intros cat_lim_cs_intros)
      fix i assume "i \<in>\<^sub>\<circ> I"
      then show "\<pi>'\<lparr>NTMap\<rparr>\<lparr>i\<rparr> : P' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> F i"
        by 
          (
            cs_concl cs_shallow
              cs_simp: 
                the_cat_discrete_components(1) 
                cat_cs_simps cat_discrete_cs_simps 
              cs_intro: cat_cs_intros
          )
    qed (rule assms)

    then have P': "P' \<in>\<^sub>\<circ> Vset \<alpha>" 
      by (auto intro: cat_cs_intros cat_lim_cs_intros)

    have \<pi>'i_i: "?\<pi>'i i : P' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> F i" if "i \<in>\<^sub>\<circ> I" for i
      using 
        \<pi>'.ntcf_NTMap_is_arr[unfolded the_cat_discrete_components(1), OF that]
        that
      by 
        (
          cs_prems cs_shallow cs_simp:
            cat_cs_simps cat_discrete_cs_simps the_cat_discrete_components(1)
        )
    from cat_Set_obj_prod_up_cat_Set_is_arr[OF P' assms(1) \<pi>'i_i] have \<pi>'i: 
      "cat_Set_obj_prod_up I F P' ?\<pi>'i : P' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)". 

    show "\<pi>' = ?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (cat_Set \<alpha>) ?up'"
    proof(rule ntcf_eqI, rule \<pi>'.is_ntcf_axioms)

      from F_is_cat_cone \<pi>'i show 
        "?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (cat_Set \<alpha>) ?up' :
          cf_const (:\<^sub>C I) (cat_Set \<alpha>) P' \<mapsto>\<^sub>C\<^sub>F :\<rightarrow>: I F (cat_Set \<alpha>) : 
          :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by (cs_concl cs_shallow cs_intro: cat_cs_intros)

      have dom_lhs: "\<D>\<^sub>\<circ> (\<pi>'\<lparr>NTMap\<rparr>) = :\<^sub>C I\<lparr>Obj\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps)
      from F_is_cat_cone \<pi>'i have dom_rhs: 
        "\<D>\<^sub>\<circ> ((?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (cat_Set \<alpha>) ?up')\<lparr>NTMap\<rparr>) = :\<^sub>C I\<lparr>Obj\<rparr>"
        by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

      show "\<pi>'\<lparr>NTMap\<rparr> = (?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (cat_Set \<alpha>) ?up')\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
        fix i assume prems': "i \<in>\<^sub>\<circ> :\<^sub>C I\<lparr>Obj\<rparr>"
        then have i: "i \<in>\<^sub>\<circ> I" unfolding the_cat_discrete_components by simp
        have [cat_cs_simps]: 
          "vprojection_arrow I F i \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?up' = \<pi>'\<lparr>NTMap\<rparr>\<lparr>i\<rparr>"
          by 
            (
              rule cat_Set_cf_comp_proj_obj_prod_up[
                OF P' assms \<pi>'i_i i, symmetric
                ]
            ) 
            auto
        from \<pi>'i prems' show "\<pi>'\<lparr>NTMap\<rparr>\<lparr>i\<rparr> =
          (?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (cat_Set \<alpha>) ?up')\<lparr>NTMap\<rparr>\<lparr>i\<rparr>"
          by 
            (
              cs_concl cs_shallow
                cs_simp: cat_cs_simps cat_Rel_cs_simps cs_intro: cat_cs_intros
            )
      qed (auto simp: cat_cs_intros)

    qed simp_all

    fix f' assume prems:
      "f' : P' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)"
      "\<pi>' = ?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (cat_Set \<alpha>) f'"
    from prems(2) have \<pi>'_eq_F_f': "\<pi>'\<lparr>NTMap\<rparr>\<lparr>i\<rparr>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = 
      (?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) (cat_Set \<alpha>) f')\<lparr>NTMap\<rparr>\<lparr>i\<rparr>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
      if "i \<in>\<^sub>\<circ> I" and "a \<in>\<^sub>\<circ> P'" for i a
      by simp
    have [cat_Set_cs_simps]: "\<pi>'\<lparr>NTMap\<rparr>\<lparr>i\<rparr>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = f'\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr>"
      if "i \<in>\<^sub>\<circ> I" and "a \<in>\<^sub>\<circ> P'" for i a
      using 
        \<pi>'_eq_F_f'[OF that] 
        assms prems that 
        vprojection_arrow_is_arr[OF that(1) assms]
      by 
        (
          cs_prems cs_shallow
            cs_simp: 
              cat_Set_cs_simps 
              cat_cs_simps 
              vprojection_arrow_app 
              the_cat_discrete_components(1) 
            cs_intro: cat_Set_cs_intros cat_cs_intros
        )

    note f' = cat_Set_is_arrD[OF prems(1)]
    note up' = cat_Set_is_arrD[OF up']

    interpret f': arr_Set \<alpha> f' by (rule f'(1))
    interpret u': arr_Set \<alpha> \<open>(cat_Set_obj_prod_up I F P' (app (\<pi>'\<lparr>NTMap\<rparr>)))\<close> 
      by (rule up'(1))

    show "f' = ?up'"
    proof(rule arr_Set_eqI[of \<alpha>])
      have dom_lhs: "\<D>\<^sub>\<circ> (f'\<lparr>ArrVal\<rparr>) = P'" 
        by (simp add: cat_Set_cs_simps cat_cs_simps f')
      have dom_rhs: 
        "\<D>\<^sub>\<circ> (cat_Set_obj_prod_up I F P' (app (\<pi>'\<lparr>NTMap\<rparr>))\<lparr>ArrVal\<rparr>) = P'"
        by (simp add: cat_Set_cs_simps cat_cs_simps up')
      show "f'\<lparr>ArrVal\<rparr> = cat_Set_obj_prod_up I F P' (app (\<pi>'\<lparr>NTMap\<rparr>))\<lparr>ArrVal\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
        fix a assume prems': "a \<in>\<^sub>\<circ> P'"
        from prems(1) prems' have "f'\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)"
          by (cs_concl cs_shallow cs_intro: cat_Set_cs_intros)
        note f'a = vproductD[OF this]
        from prems' have dom_rhs: 
          "\<D>\<^sub>\<circ> (cat_Set_obj_prod_up I F P' (app (\<pi>'\<lparr>NTMap\<rparr>))\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>) = I"
          by (cs_concl cs_shallow cs_simp: cat_Set_cs_simps)
        show "f'\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> =
          cat_Set_obj_prod_up I F P' (app (\<pi>'\<lparr>NTMap\<rparr>))\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
        proof(rule vsv_eqI, unfold f'a dom_rhs)
          fix i assume "i \<in>\<^sub>\<circ> I"
          with prems' show "f'\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr> =
            cat_Set_obj_prod_up I F P' (app (\<pi>'\<lparr>NTMap\<rparr>))\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr>"
            by (cs_concl cs_shallow cs_simp: cat_Set_cs_simps)
        qed (simp_all add: prems' f'a(1) cat_Set_obj_prod_up_ArrVal_app)
      qed auto
    qed (simp_all add: cat_Set_obj_prod_up_components f' up'(1))

  qed

qed



subsection\<open>Equalizer for the category \<open>Set\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

abbreviation ntcf_Set_equalizer_map :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_Set_equalizer_map \<alpha> a g f i \<equiv>
    (
      i = \<aa>\<^sub>P\<^sub>L\<^sub>2 ?
        incl_Set (vequalizer a g f) a :
        g \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> incl_Set (vequalizer a g f) a
    )"

definition ntcf_Set_equalizer :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_Set_equalizer \<alpha> a b g f = ntcf_equalizer_base
    (cat_Set \<alpha>) a b g f (vequalizer a g f) (ntcf_Set_equalizer_map \<alpha> a g f)"


text\<open>Components.\<close>

context
  fixes a g f \<alpha> :: V
begin

lemmas ntcf_Set_equalizer_components = 
  ntcf_equalizer_base_components[
    where \<CC>=\<open>cat_Set \<alpha>\<close> 
      and e=\<open>ntcf_Set_equalizer_map \<alpha> a g f\<close>
      and E=\<open>vequalizer a g f\<close>
      and \<aa>=a and \<gg>=g and \<ff>=f,
      folded ntcf_Set_equalizer_def
      ]

end


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_Set_equalizer_components(1)
  |vsv ntcf_Set_equalizer_NTMap_vsv[cat_Set_cs_intros]|
  |vdomain ntcf_Set_equalizer_NTMap_vdomain[cat_Set_cs_simps]|
  |app ntcf_Set_equalizer_NTMap_app|

lemma ntcf_Set_equalizer_2_NTMap_app_\<aa>[cat_Set_cs_simps]:
  assumes "x = \<aa>\<^sub>P\<^sub>L\<^sub>2"
  shows 
    "ntcf_Set_equalizer \<alpha> a b g f\<lparr>NTMap\<rparr>\<lparr>x\<rparr> =
      incl_Set (vequalizer a g f) a"
  unfolding assms the_cat_parallel_2_components(1) ntcf_Set_equalizer_components 
  by simp

lemma ntcf_Set_equalizer_2_NTMap_app_\<bb>[cat_Set_cs_simps]:
  assumes "x = \<bb>\<^sub>P\<^sub>L\<^sub>2"
  shows 
    "ntcf_Set_equalizer \<alpha> a b g f\<lparr>NTMap\<rparr>\<lparr>x\<rparr> =
      g \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> incl_Set (vequalizer a g f) a"
  unfolding assms the_cat_parallel_2_components(1) ntcf_Set_equalizer_components
  using cat_PL2_ineq
  by auto


subsubsection\<open>Equalizer for the category \<open>Set\<close> is an equalizer\<close>

lemma (in \<Z>) ntcf_Set_equalizer_2_is_cat_equalizer_2:
  assumes "\<gg> : \<aa> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>" and "\<ff> : \<aa> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>" 
  shows "ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> :
    vequalizer \<aa> \<gg> \<ff> <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof(intro is_cat_equalizer_2I is_cat_equalizerI is_cat_limitI)
  
  let ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F (cat_Set \<alpha>) \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<close>
    and ?II = \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close>

  note \<gg> = cat_Set_is_arrD[OF assms(1)]
  interpret \<gg>: arr_Set \<alpha> \<gg> 
    rewrites "\<gg>\<lparr>ArrDom\<rparr> = \<aa>" and "\<gg>\<lparr>ArrCod\<rparr> = \<bb>"
    by (rule \<gg>(1)) (simp_all add: \<gg>)
  note \<ff> = cat_Set_is_arrD[OF assms(2)]
  interpret \<ff>: arr_Set \<alpha> \<ff> 
    rewrites "\<ff>\<lparr>ArrDom\<rparr> = \<aa>" and "\<ff>\<lparr>ArrCod\<rparr> = \<bb>"
    by (rule \<ff>(1)) (simp_all add: \<ff>)

  note [cat_Set_cs_intros] = \<gg>.arr_Set_ArrDom_in_Vset \<ff>.arr_Set_ArrCod_in_Vset
  
  let ?incl = \<open>incl_Set (vequalizer \<aa> \<gg> \<ff>) \<aa>\<close>

  show \<aa>\<bb>\<gg>\<ff>_is_cat_cone: "ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> :
    vequalizer \<aa> \<gg> \<ff> <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    unfolding ntcf_Set_equalizer_def
  proof
    (
      intro 
        category.cat_ntcf_equalizer_base_is_cat_cone 
        category.cat_cf_parallel_2_cat_equalizer
    )
    from assms show 
      "(\<bb>\<^sub>P\<^sub>L\<^sub>2 = \<aa>\<^sub>P\<^sub>L\<^sub>2 ? ?incl : \<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl) :
        vequalizer \<aa> \<gg> \<ff> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>"
      by 
        (
          cs_concl cs_shallow
            cs_simp: V_cs_simps 
            cs_intro: 
              V_cs_intros cat_Set_cs_intros cat_cs_intros 
              cat_PL2_ineq[symmetric] 
        )
    show 
      "(\<bb>\<^sub>P\<^sub>L\<^sub>2 = \<aa>\<^sub>P\<^sub>L\<^sub>2 ? ?incl : \<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl) =
        \<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (\<aa>\<^sub>P\<^sub>L\<^sub>2 = \<aa>\<^sub>P\<^sub>L\<^sub>2 ? ?incl : \<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)"
      by 
        (
          cs_concl 
            cs_simp: V_cs_simps 
            cs_intro: 
              V_cs_intros cat_Set_cs_intros cat_cs_intros 
              cat_PL2_ineq[symmetric] 
        )
    from assms show 
      "(\<bb>\<^sub>P\<^sub>L\<^sub>2 = \<aa>\<^sub>P\<^sub>L\<^sub>2 ? ?incl : \<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl) =
        \<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (\<aa>\<^sub>P\<^sub>L\<^sub>2 = \<aa>\<^sub>P\<^sub>L\<^sub>2 ? ?incl : \<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)"
      by 
        (
          cs_concl 
            cs_simp: V_cs_simps cat_Set_incl_Set_commute 
            cs_intro: V_cs_intros cat_PL2_ineq[symmetric]
        )
  qed 
    (
      cs_concl 
        cs_intro: cat_cs_intros V_cs_intros cat_Set_cs_intros assms 
        cs_simp: V_cs_simps cat_cs_simps
    )+

  interpret \<aa>\<bb>\<gg>\<ff>: is_cat_cone 
    \<alpha> \<open>vequalizer \<aa> \<gg> \<ff>\<close> ?II \<open>cat_Set \<alpha>\<close> ?II_II \<open>ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff>\<close>
    by (rule \<aa>\<bb>\<gg>\<ff>_is_cat_cone)

  show "\<exists>!f'.
    f' : r' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> vequalizer \<aa> \<gg> \<ff> \<and> 
    u' = ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II (cat_Set \<alpha>) f'"
    if "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" for u' r'
  proof-
    
    interpret u': is_cat_cone \<alpha> r' ?II \<open>cat_Set \<alpha>\<close> ?II_II u' by (rule that(1))

    have "\<aa>\<^sub>P\<^sub>L\<^sub>2 \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L\<^sub>2 \<bb>\<^sub>P\<^sub>L\<^sub>2 \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<lparr>Obj\<rparr>" 
      unfolding the_cat_parallel_2_components(1) by simp
    from 
      u'.ntcf_NTMap_is_arr[OF this] 
      \<aa>\<bb>\<gg>\<ff>.NTDom.HomCod.cat_cf_parallel_2_cat_equalizer[OF assms] 
    have u'_\<aa>\<^sub>P\<^sub>L_is_arr: "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> : r' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<aa>"
      by (cs_prems_atom_step cat_cs_simps) 
        (
          cs_prems  
            cs_simp: cat_parallel_cs_simps 
            cs_intro: 
              cat_parallel_cs_intros 
              cat_cs_intros
              category.cat_cf_parallel_2_cat_equalizer
        )
    note u'_\<aa>\<^sub>P\<^sub>L = cat_Set_is_arrD[OF u'_\<aa>\<^sub>P\<^sub>L_is_arr]
    interpret u'_\<aa>\<^sub>P\<^sub>L: arr_Set \<alpha> \<open>u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<close> by (rule u'_\<aa>\<^sub>P\<^sub>L(1))

    have "\<bb>\<^sub>P\<^sub>L\<^sub>2 \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>" 
      by (cs_concl cs_shallow cs_intro: cat_parallel_cs_intros)

    from 
      u'.ntcf_NTMap_is_arr[OF this] 
      \<aa>\<bb>\<gg>\<ff>.NTDom.HomCod.cat_cf_parallel_2_cat_equalizer[OF assms]
    have "u'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> : r' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>"
      by 
        (
          cs_prems cs_shallow
            cs_simp: cat_cs_simps cat_parallel_cs_simps 
            cs_intro: cat_parallel_cs_intros
        )

    note u'_\<gg>u' = cat_cone_cf_par_2_eps_NTMap_app(1)[OF that(1) assms]
    
    define q where "q = [u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>, r', vequalizer \<aa> \<gg> \<ff>]\<^sub>\<circ>"

    have q_components[cat_Set_cs_simps]:  
      "q\<lparr>ArrVal\<rparr> = u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>" 
      "q\<lparr>ArrDom\<rparr> = r'" 
      "q\<lparr>ArrCod\<rparr> = vequalizer \<aa> \<gg> \<ff>"
      unfolding q_def arr_field_simps by (simp_all add: nat_omega_simps)

    from cat_cone_cf_par_2_eps_NTMap_app[OF that(1) assms] have \<gg>u'_eq_\<ff>u':
      "(\<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> =
        (\<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>"
      for x 
      by simp

    show ?thesis
    proof(intro ex1I conjI; (elim conjE)?)

      have u'_NTMap_vrange: "\<R>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> vequalizer \<aa> \<gg> \<ff>"
      proof(rule vsubsetI)
        fix y assume prems: "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>)"
        then obtain x where x: "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>)" 
          and y_def: "y = u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>"
          by (blast dest: u'_\<aa>\<^sub>P\<^sub>L.ArrVal.vrange_atD)
        have x: "x \<in>\<^sub>\<circ> r'" 
          by (use x u'_\<aa>\<^sub>P\<^sub>L_is_arr in \<open>cs_prems cs_shallow cs_simp: cat_cs_simps\<close>)          
        from \<gg>u'_eq_\<ff>u'[of x] assms x u'_\<aa>\<^sub>P\<^sub>L_is_arr have [simp]: 
          "\<gg>\<lparr>ArrVal\<rparr>\<lparr>u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>\<rparr> =
            \<ff>\<lparr>ArrVal\<rparr>\<lparr>u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>\<rparr>"
          by (cs_prems cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        from prems u'_\<aa>\<^sub>P\<^sub>L.arr_Set_ArrVal_vrange[unfolded u'_\<aa>\<^sub>P\<^sub>L] show 
          "y \<in>\<^sub>\<circ> vequalizer \<aa> \<gg> \<ff>"
          by (intro vequalizerI, unfold y_def) auto
      qed

      show q_is_arr: "q : r' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> vequalizer \<aa> \<gg> \<ff>" 
      proof(intro cat_Set_is_arrI arr_SetI)
        show "q\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" 
          by (auto simp: q_components intro: cat_cs_intros cat_lim_cs_intros)
      qed 
        (
          auto 
            simp: 
              cat_Set_cs_simps nat_omega_simps 
              u'_\<aa>\<^sub>P\<^sub>L 
              q_def 
              u'_NTMap_vrange
              \<aa>\<bb>\<gg>\<ff>.NTDom.HomCod.cat_in_Obj_in_Vset
            intro: cat_cs_intros cat_lim_cs_intros
        )  

      from q_is_arr have \<aa>_q:  
        "incl_Set (vequalizer \<aa> \<gg> \<ff>) \<aa> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> q : 
          r' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<aa>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps
              cs_intro: V_cs_intros cat_cs_intros cat_Set_cs_intros
          )
      interpret arr_Set \<alpha> \<open>incl_Set (vequalizer \<aa> \<gg> \<ff>) \<aa> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> q\<close>
        using \<aa>_q by (auto dest: cat_Set_is_arrD)

      show "u' = ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II (cat_Set \<alpha>) q"
      proof(rule ntcf_eqI)
        from q_is_arr show 
          "ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II (cat_Set \<alpha>) q :
            cf_const ?II (cat_Set \<alpha>) r' \<mapsto>\<^sub>C\<^sub>F 
            ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
          by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        have dom_lhs: "\<D>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>) = ?II\<lparr>Obj\<rparr>" 
          by (cs_concl cs_shallow cs_simp: cat_cs_simps)
        from q_is_arr have dom_rhs:
          "\<D>\<^sub>\<circ> 
            (
              (ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
              ntcf_const ?II (cat_Set \<alpha>) q
            )\<lparr>NTMap\<rparr>) =  ?II\<lparr>Obj\<rparr>"
          by (cs_concl cs_shallow cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        show "u'\<lparr>NTMap\<rparr> =
          (
            ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II (cat_Set \<alpha>) q
          )\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          show "vsv ((
            ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II (cat_Set \<alpha>) q
            )\<lparr>NTMap\<rparr>)"
            by (cs_concl cs_shallow cs_intro: cat_cs_intros)
          fix a assume prems: "a \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>"
          have [symmetric, cat_Set_cs_simps]: 
            "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = incl_Set (vequalizer \<aa> \<gg> \<ff>) \<aa> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> q"
          proof(rule arr_Set_eqI[of \<alpha>])
            from u'_\<aa>\<^sub>P\<^sub>L_is_arr have dom_lhs: "\<D>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>) = r'"
              by 
                (
                  cs_concl cs_shallow 
                    cs_simp: cat_cs_simps cs_intro: cat_cs_intros
                )
            from \<aa>_q have dom_rhs: 
              "\<D>\<^sub>\<circ> ((incl_Set (vequalizer \<aa> \<gg> \<ff>) \<aa> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> q)\<lparr>ArrVal\<rparr>) = r'"
              by 
                (
                  cs_concl cs_shallow 
                    cs_simp: cat_cs_simps cs_intro: cat_cs_intros
                )
            show "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr> =
              (incl_Set (vequalizer \<aa> \<gg> \<ff>) \<aa> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> q)\<lparr>ArrVal\<rparr>"
            proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
              fix a assume prems: "a \<in>\<^sub>\<circ> r'"
              with u'_NTMap_vrange dom_lhs u'_\<aa>\<^sub>P\<^sub>L.ArrVal.vsv_vimageI2 have 
                "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> vequalizer \<aa> \<gg> \<ff>"
                by blast
              with prems q_is_arr u'_\<aa>\<^sub>P\<^sub>L_is_arr show 
                "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> =
                  (incl_Set (vequalizer \<aa> \<gg> \<ff>) \<aa> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> q)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
                by 
                  (
                    cs_concl cs_shallow
                      cs_simp: cat_Set_cs_simps cat_cs_simps 
                      cs_intro: V_cs_intros cat_cs_intros cat_Set_cs_intros
                  )
            qed auto
          qed 
            (
              use u'_\<aa>\<^sub>P\<^sub>L \<aa>_q in \<open>
                cs_concl cs_shallow 
                  cs_intro: cat_Set_is_arrD(1) cs_simp: cat_cs_simps
                \<close>
            )+
          from q_is_arr have u'_NTMap_app_I: "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> =
            (
              ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II (cat_Set \<alpha>) q
            )\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
            by 
              (
                cs_concl 
                  cs_intro: cat_cs_intros cat_parallel_cs_intros 
                  cs_simp: cat_Set_cs_simps cat_cs_simps V_cs_simps
              )
          from q_is_arr assms have u'_NTMap_app_sI: "u'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr> =
            (
              ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II (cat_Set \<alpha>) q
            )\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<^sub>2\<rparr>"
            by 
              (
                cs_concl 
                  cs_simp: cat_Set_cs_simps cat_cs_simps u'_\<gg>u' 
                  cs_intro: 
                    V_cs_intros 
                    cat_cs_intros 
                    cat_Set_cs_intros 
                    cat_parallel_cs_intros
              )
          from prems consider \<open>a = \<aa>\<^sub>P\<^sub>L\<^sub>2\<close> | \<open>a = \<bb>\<^sub>P\<^sub>L\<^sub>2\<close> 
            by (elim the_cat_parallel_2_ObjE)
          then show 
            "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
              (
                ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
                ntcf_const ?II (cat_Set \<alpha>) q
              )\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by cases (simp_all add: u'_NTMap_app_I u'_NTMap_app_sI)
        qed auto
      qed (simp_all add: u'.is_ntcf_axioms)
        
      fix f' assume prems:
        "f' : r' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> vequalizer \<aa> \<gg> \<ff>"
        "u' = ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II (cat_Set \<alpha>) f'"
      from prems(2) have u'_NTMap_app: 
        "u'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> =
          (ntcf_Set_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
          ntcf_const ?II (cat_Set \<alpha>) f')\<lparr>NTMap\<rparr>\<lparr>x\<rparr>"
        for x
        by simp
      have u'_f': 
        "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<^sub>2\<rparr> = incl_Set (vequalizer \<aa> \<gg> \<ff>) \<aa> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> f'"
        using u'_NTMap_app[of \<aa>\<^sub>P\<^sub>L\<^sub>2] prems(1)
        by 
          (
            cs_prems
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_parallel_cs_intros
          )
          (
            cs_prems cs_shallow 
              cs_simp: cat_Set_cs_simps cs_intro: cat_parallel_cs_intros
          )

      note f' = cat_Set_is_arrD[OF prems(1)]
      note q = cat_Set_is_arrD[OF q_is_arr]

      interpret f': arr_Set \<alpha> f' using prems(1) by (auto dest: cat_Set_is_arrD)
      interpret q: arr_Set \<alpha> q using q by (auto dest: cat_Set_is_arrD)

      show "f' = q"
      proof(rule arr_Set_eqI[of \<alpha>])
        have dom_lhs: "\<D>\<^sub>\<circ> (f'\<lparr>ArrVal\<rparr>) = r'" by (simp add: cat_Set_cs_simps f')
        from q_is_arr have dom_rhs: "\<D>\<^sub>\<circ> (q\<lparr>ArrVal\<rparr>) = r'" 
          by 
            (
              cs_concl cs_shallow 
                cs_simp: cat_cs_simps cs_intro: cat_Set_cs_intros
            )
        show "f'\<lparr>ArrVal\<rparr> = q\<lparr>ArrVal\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix i assume "i \<in>\<^sub>\<circ> r'"
          with prems(1) show "f'\<lparr>ArrVal\<rparr>\<lparr>i\<rparr> = q\<lparr>ArrVal\<rparr>\<lparr>i\<rparr>"
            by 
              (
                cs_concl cs_shallow
                  cs_simp: cat_Set_cs_simps cat_cs_simps q_components u'_f'
                  cs_intro: V_cs_intros cat_cs_intros cat_Set_cs_intros
              )
        qed auto
      qed 
        (
          use prems(1) q_is_arr in \<open>
            cs_concl cs_shallow
              cs_simp: cat_cs_simps cs_intro: q cat_Set_is_arrD
            \<close>
        )+
    qed
  qed

qed (auto intro: assms)



subsection\<open>The category \<open>Set\<close> is small-complete\<close>

lemma (in \<Z>) cat_small_complete_cat_Set: "cat_small_complete \<alpha> (cat_Set \<alpha>)"
  \<comment>\<open>This lemma appears as a remark on page 113 in
\cite{mac_lane_categories_2010}.\<close>
proof(rule category.cat_small_complete_if_eq_and_obj_prod)
  show "\<exists>E \<epsilon>. \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    if "\<ff> : \<aa> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>" and "\<gg> : \<aa> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>" for \<aa> \<bb> \<gg> \<ff>
    using ntcf_Set_equalizer_2_is_cat_equalizer_2[OF that(2,1)] by auto
  show "\<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    if "tm_cf_discrete \<alpha> I A (cat_Set \<alpha>)" for A I
  proof(intro exI, rule tm_cf_discrete_ntcf_obj_prod_base_is_cat_obj_prod)
    interpret tm_cf_discrete \<alpha> I A \<open>cat_Set \<alpha>\<close> by (rule that)
    show "VLambda I A \<in>\<^sub>\<circ> Vset \<alpha>" by (rule tm_cf_discrete_ObjMap_in_Vset)
  qed
qed (rule category_cat_Set)

text\<open>\newpage\<close>

end