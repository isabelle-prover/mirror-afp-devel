(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Categories with parallel arrows between two objects\<close>
theory CZH_ECAT_Parallel
  imports CZH_ECAT_Small_Functor
begin



subsection\<open>Background: category with parallel arrows between two objects\<close>

named_theorems cat_parallel_cs_simps
named_theorems cat_parallel_cs_intros

definition \<aa>\<^sub>P\<^sub>L :: "V \<Rightarrow> V" where "\<aa>\<^sub>P\<^sub>L F = set {F, 0}"
definition \<bb>\<^sub>P\<^sub>L :: "V \<Rightarrow> V" where "\<bb>\<^sub>P\<^sub>L F = set {F, 1\<^sub>\<nat>}"

lemma cat_PL_\<aa>_nin_F[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L F \<notin>\<^sub>\<circ> F" 
  unfolding \<aa>\<^sub>P\<^sub>L_def using mem_not_sym by auto

lemma cat_PL_\<bb>_nin_F[cat_parallel_cs_intros]: "\<bb>\<^sub>P\<^sub>L F \<notin>\<^sub>\<circ> F"
  unfolding \<bb>\<^sub>P\<^sub>L_def using mem_not_sym by auto

lemma cat_PL_\<aa>\<bb>[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L F \<noteq> \<bb>\<^sub>P\<^sub>L F"
  unfolding \<aa>\<^sub>P\<^sub>L_def \<bb>\<^sub>P\<^sub>L_def by (simp add: Set.doubleton_eq_iff)

lemmas cat_PL_\<bb>\<aa>[cat_parallel_cs_intros] = cat_PL_\<aa>\<bb>[symmetric]



subsection\<open>
Composable arrows for a category with parallel arrows between two objects
\<close>

definition cat_parallel_composable :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cat_parallel_composable \<aa> \<bb> F \<equiv>
    set {[\<aa>, \<aa>]\<^sub>\<circ>, [\<bb>, \<bb>]\<^sub>\<circ>} \<union>\<^sub>\<circ>
    (F \<times>\<^sub>\<bullet> set {\<aa>}) \<union>\<^sub>\<circ>
    (set {\<bb>} \<times>\<^sub>\<bullet> F)"


text\<open>Rules.\<close>

lemma cat_parallel_composable_\<aa>\<aa>[cat_parallel_cs_intros]:
  assumes "g = \<aa>" and "f = \<aa>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
  unfolding assms cat_parallel_composable_def by auto

lemma cat_parallel_composable_\<bb>\<ff>[cat_parallel_cs_intros]:
  assumes "g = \<bb>" and "f \<in>\<^sub>\<circ> F"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
  using assms(2) unfolding assms(1) cat_parallel_composable_def by auto

lemma cat_parallel_composable_\<ff>\<aa>[cat_parallel_cs_intros]:
  assumes "g \<in>\<^sub>\<circ> F" and "f = \<aa>" 
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
  using assms(1) unfolding assms(2) cat_parallel_composable_def by auto

lemma cat_parallel_composable_\<bb>\<bb>[cat_parallel_cs_intros]:
  assumes "g = \<bb>" and "f = \<bb>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
  unfolding assms cat_parallel_composable_def by auto

lemma cat_parallel_composableE:
  assumes "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
  obtains "g = \<bb>" and "f = \<bb>"
        | "g = \<bb>" and "f \<in>\<^sub>\<circ> F" 
        | "g \<in>\<^sub>\<circ> F" and "f = \<aa>"
        | "g = \<aa>" and "f = \<aa>"
  using assms that unfolding cat_parallel_composable_def by auto


text\<open>Elementary properties.\<close>

lemma cat_parallel_composable_fconverse: 
  "(cat_parallel_composable \<aa> \<bb> F)\<inverse>\<^sub>\<bullet> = cat_parallel_composable \<bb> \<aa> F"
  unfolding cat_parallel_composable_def by auto



subsection\<open>
Local assumptions for a category with parallel arrows between two objects
\<close>

locale cat_parallel = \<Z> \<alpha> for \<alpha> +  
  fixes \<aa> \<bb> F
  assumes cat_parallel_\<aa>\<bb>[cat_parallel_cs_intros]: "\<aa> \<noteq> \<bb>"
    and cat_parallel_\<aa>F[cat_parallel_cs_intros]: "\<aa> \<notin>\<^sub>\<circ> F"
    and cat_parallel_\<bb>F[cat_parallel_cs_intros]: "\<bb> \<notin>\<^sub>\<circ> F"
    and cat_parallel_\<aa>_in_Vset[cat_parallel_cs_intros]: "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_parallel_\<bb>_in_Vset[cat_parallel_cs_intros]: "\<bb> \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_parallel_F_in_Vset[cat_parallel_cs_intros]: "F \<in>\<^sub>\<circ> Vset \<alpha>"

lemmas (in cat_parallel) cat_parallel_ineq =
  cat_parallel_\<aa>\<bb>
  cat_parallel_\<aa>F
  cat_parallel_\<bb>F


text\<open>Rules.\<close>

lemmas (in cat_parallel) [cat_parallel_cs_intros] = cat_parallel_axioms

mk_ide rf cat_parallel_def[unfolded cat_parallel_axioms_def]
  |intro cat_parallelI|
  |dest cat_parallelD[dest]|
  |elim cat_parallelE[elim]|


text\<open>Duality.\<close>

lemma (in cat_parallel) cat_parallel_op[cat_op_intros]: 
  "cat_parallel \<alpha> \<bb> \<aa> F"
  by (intro cat_parallelI) 
    (auto intro!: cat_parallel_cs_intros cat_parallel_\<aa>\<bb>[symmetric])


text\<open>Elementary properties.\<close>

lemma (in \<Z>) cat_parallel_PL: 
  assumes "F \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "cat_parallel \<alpha> (\<aa>\<^sub>P\<^sub>L F) (\<bb>\<^sub>P\<^sub>L F) F"
proof (rule cat_parallelI)
  show "\<aa>\<^sub>P\<^sub>L F \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding \<aa>\<^sub>P\<^sub>L_def by (intro Limit_vdoubleton_in_VsetI assms) auto
  show "\<bb>\<^sub>P\<^sub>L F \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding \<bb>\<^sub>P\<^sub>L_def
    by (intro Limit_vdoubleton_in_VsetI ord_of_nat_in_Vset assms) simp
qed (auto simp: assms cat_PL_\<aa>\<bb> cat_PL_\<aa>_nin_F cat_PL_\<bb>_nin_F)



subsection\<open>\<open>\<Up>\<close>: category with parallel arrows between two objects\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 and Chapter III-3 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition the_cat_parallel :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>\<Up>\<^sub>C\<close>)
  where "\<Up>\<^sub>C \<aa> \<bb> F =
    [
      set {\<aa>, \<bb>},
      set {\<aa>, \<bb>} \<union>\<^sub>\<circ> F,
      (\<lambda>x\<in>\<^sub>\<circ>set {\<aa>, \<bb>} \<union>\<^sub>\<circ> F. (x = \<bb> ? \<bb> : \<aa>)),
      (\<lambda>x\<in>\<^sub>\<circ>set {\<aa>, \<bb>} \<union>\<^sub>\<circ> F. (x = \<aa> ? \<aa> : \<bb>)),
      (
        \<lambda>gf\<in>\<^sub>\<circ>cat_parallel_composable \<aa> \<bb> F.
         if gf = [\<bb>, \<bb>]\<^sub>\<circ> \<Rightarrow> \<bb>
          | \<exists>f. gf = [\<bb>, f]\<^sub>\<circ> \<Rightarrow> gf\<lparr>1\<^sub>\<nat>\<rparr>
          | \<exists>f. gf = [f, \<aa>]\<^sub>\<circ> \<Rightarrow> gf\<lparr>0\<rparr>
          | otherwise \<Rightarrow> \<aa>
      ),
      vid_on (set {\<aa>, \<bb>})
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_cat_parallel_components: 
  shows "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr> = set {\<aa>, \<bb>}"
    and "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr> = set {\<aa>, \<bb>} \<union>\<^sub>\<circ> F"
    and "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Dom\<rparr> = (\<lambda>x\<in>\<^sub>\<circ>set {\<aa>, \<bb>} \<union>\<^sub>\<circ> F. (x = \<bb> ? \<bb> : \<aa>))"
    and "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Cod\<rparr> = (\<lambda>x\<in>\<^sub>\<circ>set {\<aa>, \<bb>} \<union>\<^sub>\<circ> F. (x = \<aa> ? \<aa> : \<bb>))"
    and "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Comp\<rparr> =
      (
        \<lambda>gf\<in>\<^sub>\<circ>cat_parallel_composable \<aa> \<bb> F.
         if gf = [\<bb>, \<bb>]\<^sub>\<circ> \<Rightarrow> \<bb>
          | \<exists>f. gf = [\<bb>, f]\<^sub>\<circ> \<Rightarrow> gf\<lparr>1\<^sub>\<nat>\<rparr>
          | \<exists>f. gf = [f, \<aa>]\<^sub>\<circ> \<Rightarrow> gf\<lparr>0\<rparr>
          | otherwise \<Rightarrow> \<aa>
      )"
    and "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr> = vid_on (set {\<aa>, \<bb>})"
  unfolding the_cat_parallel_def dg_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Objects\<close>

lemma the_cat_parallel_Obj_\<aa>I[cat_parallel_cs_intros]:
  assumes "a = \<aa>"
  shows "a \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_Obj_\<bb>I[cat_parallel_cs_intros]:
  assumes "a = \<bb>"
  shows "a \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_ObjE:
  assumes "a \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>"
  obtains "a = \<aa>" | "a = \<bb>" 
  using assms unfolding the_cat_parallel_components(1) by fastforce


subsubsection\<open>Arrows\<close>

lemma the_cat_parallel_Arr_\<aa>I[cat_parallel_cs_intros]:
  assumes "f = \<aa>"  
  shows "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_Arr_\<bb>I[cat_parallel_cs_intros]:
  assumes "f = \<bb>"  
  shows "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_Arr_FI[cat_parallel_cs_intros]:
  assumes "f \<in>\<^sub>\<circ> F"
  shows "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_ArrE:
  assumes "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
  obtains "f = \<aa>" | "f = \<bb>" | "f \<in>\<^sub>\<circ> F"  
  using assms that unfolding the_cat_parallel_components by auto


subsubsection\<open>Domain\<close>

mk_VLambda the_cat_parallel_components(3)
  |vsv the_cat_parallel_Dom_vsv[cat_parallel_cs_intros]|
  |vdomain the_cat_parallel_Dom_vdomain[cat_parallel_cs_simps]|

lemma (in cat_parallel) the_cat_parallel_Dom_app_\<bb>[cat_parallel_cs_simps]:
  assumes "f = \<bb>"
  shows "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<bb>"
  unfolding the_cat_parallel_components assms by simp

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Dom_app_\<bb>

lemma (in cat_parallel) the_cat_parallel_Dom_app_F[cat_parallel_cs_simps]:
  assumes "f \<in>\<^sub>\<circ> F"
  shows "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>"
  unfolding the_cat_parallel_components using assms cat_parallel_ineq by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Dom_app_F

lemma (in cat_parallel) the_cat_parallel_Dom_app_\<aa>[cat_parallel_cs_simps]:
  assumes "f = \<aa>"
  shows "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>"
  unfolding the_cat_parallel_components assms by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Dom_app_\<aa>


subsubsection\<open>Codomain\<close>

mk_VLambda the_cat_parallel_components(4)
  |vsv the_cat_parallel_Cod_vsv[cat_parallel_cs_intros]|
  |vdomain the_cat_parallel_Cod_vdomain[cat_parallel_cs_simps]|

lemma (in cat_parallel) the_cat_parallel_Cod_app_\<bb>[cat_parallel_cs_simps]:
  assumes "f = \<bb>"
  shows "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
  unfolding the_cat_parallel_components assms by simp

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Cod_app_\<bb>

lemma (in cat_parallel) the_cat_parallel_Cod_app_F[cat_parallel_cs_simps]:
  assumes "f \<in>\<^sub>\<circ> F"
  shows "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
  unfolding the_cat_parallel_components using assms cat_parallel_ineq by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Cod_app_F

lemma (in cat_parallel) the_cat_parallel_Cod_app_\<aa>[cat_parallel_cs_simps]:
  assumes "f = \<aa>"
  shows "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<aa>"
  unfolding the_cat_parallel_components assms by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Cod_app_\<aa>


subsubsection\<open>Composition\<close>

mk_VLambda the_cat_parallel_components(5)
  |vsv the_cat_parallel_Comp_vsv[cat_parallel_cs_intros]|
  |vdomain the_cat_parallel_Comp_vdomain[cat_parallel_cs_simps]|
  |app the_cat_parallel_Comp_app[cat_parallel_cs_simps]|

lemma the_cat_parallel_Comp_app_\<bb>\<bb>[cat_parallel_cs_simps]:
  assumes "g = \<bb>" and "f = \<bb>"
  shows "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
    by (cs_concl cs_shallow cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = f"
    unfolding the_cat_parallel_components(5) assms 
    by (auto simp: nat_omega_simps)
qed

lemma the_cat_parallel_Comp_app_\<aa>\<aa>[cat_parallel_cs_simps]:
  assumes "g = \<aa>" and "f = \<aa>"
  shows "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
    by (cs_concl cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = f"
    unfolding the_cat_parallel_components(5) assms 
    by (auto simp: nat_omega_simps)
qed

lemma the_cat_parallel_Comp_app_\<bb>F[cat_parallel_cs_simps]:
  assumes "g = \<bb>" and "f \<in>\<^sub>\<circ> F"
  shows "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = f" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
    by (cs_concl cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = f"
    unfolding the_cat_parallel_components(5) assms 
    by (auto simp: nat_omega_simps)
qed

lemma (in cat_parallel) the_cat_parallel_Comp_app_F\<aa>[cat_parallel_cs_simps]:
  assumes "g \<in>\<^sub>\<circ> F" and "f = \<aa>"
  shows "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = g" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
    by (cs_concl cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = g"
    unfolding the_cat_parallel_components(5)  
    using assms cat_parallel_ineq
    by (auto simp: nat_omega_simps)
qed


subsubsection\<open>Identity\<close>

mk_VLambda the_cat_parallel_components(6)[unfolded VLambda_vid_on[symmetric]]
  |vsv the_cat_parallel_CId_vsv[cat_parallel_cs_intros]|
  |vdomain the_cat_parallel_CId_vdomain[cat_parallel_cs_simps]|
  |app the_cat_parallel_CId_app|

lemma the_cat_parallel_CId_app_\<aa>[cat_parallel_cs_simps]: 
  assumes "a = \<aa>"
  shows "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<aa>"
  unfolding assms by (auto simp: the_cat_parallel_CId_app)

lemma the_cat_parallel_CId_app_\<bb>[cat_parallel_cs_simps]: 
  assumes "a = \<bb>"
  shows "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<bb>"
  unfolding assms by (auto simp: the_cat_parallel_CId_app)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma (in cat_parallel) the_cat_parallel_is_arr_\<aa>\<aa>\<aa>[cat_parallel_cs_intros]:
  assumes "a' = \<aa>" and "b' = \<aa>" and "f = \<aa>"
  shows "f : a' \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b'"
proof(intro is_arrI, unfold assms)
  show "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Dom\<rparr>\<lparr>\<aa>\<rparr> = \<aa>" "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Cod\<rparr>\<lparr>\<aa>\<rparr> = \<aa>"
    by (cs_concl cs_shallow cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)+
qed (auto simp: the_cat_parallel_components)

lemma (in cat_parallel) the_cat_parallel_is_arr_\<bb>\<bb>\<bb>[cat_parallel_cs_intros]:
  assumes "a' = \<bb>" and "b' = \<bb>" and "f = \<bb>"
  shows "f : a' \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b'"
proof(intro is_arrI, unfold assms)
  show "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Dom\<rparr>\<lparr>\<bb>\<rparr> = \<bb>" "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Cod\<rparr>\<lparr>\<bb>\<rparr> = \<bb>"
    by (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)+
qed (auto simp: the_cat_parallel_components)

lemma (in cat_parallel) the_cat_parallel_is_arr_\<aa>\<bb>F[cat_parallel_cs_intros]:
  assumes "a' = \<aa>" and "b' = \<bb>" and "f \<in>\<^sub>\<circ> F"
  shows "f : a' \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b'"
proof(intro is_arrI, unfold assms(1,2))
  from assms(3) show "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>" "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
    by (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)+
qed (auto simp: the_cat_parallel_components assms(3))

lemma (in cat_parallel) the_cat_parallel_is_arrE:
  assumes "f' : a' \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b'"
  obtains "a' = \<aa>" and "b' = \<aa>" and "f' = \<aa>"
        | "a' = \<bb>" and "b' = \<bb>" and "f' = \<bb>"
        | "a' = \<aa>" and "b' = \<bb>" and "f' \<in>\<^sub>\<circ> F"
proof-
  note f = is_arrD[OF assms]
  from f(1) consider (\<aa>) \<open>f' = \<aa>\<close> | (\<bb>) \<open>f' = \<bb>\<close> | (F) \<open>f' \<in>\<^sub>\<circ> F\<close> 
    unfolding the_cat_parallel_components(2) by auto
  then show ?thesis
  proof cases
    case \<aa>
    moreover from f(2)[unfolded \<aa>, symmetric] have "a' = \<aa>"
      by 
        (
          cs_prems cs_shallow 
            cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros
        )
    moreover from f(3)[unfolded \<aa>, symmetric] have "b' = \<aa>"
      by 
        (
          cs_prems cs_shallow
            cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros
        )
    ultimately show ?thesis using that by auto
  next
    case \<bb>
    moreover from f(2)[unfolded \<bb>, symmetric] have "a' = \<bb>"
      by 
        (
          cs_prems cs_shallow 
            cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros
        )
    moreover from f(3)[unfolded \<bb>, symmetric] have "b' = \<bb>"
      by 
        (
          cs_prems cs_shallow 
            cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros
        )
    ultimately show ?thesis using that by auto
  next
    case F
    moreover from f(2)[symmetric] F have "a' = \<aa>"
      by 
        (
          cs_prems cs_shallow 
            cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros
        )
    moreover from f(3)[symmetric] F have "b' = \<bb>"
      by (cs_prems cs_shallow cs_simp: cat_parallel_cs_simps)
    ultimately show ?thesis using that by auto
  qed
qed


subsubsection\<open>\<open>\<Up>\<close> is a category\<close>

lemma (in cat_parallel) tiny_category_the_cat_parallel[cat_parallel_cs_intros]:
  "tiny_category \<alpha> (\<Up>\<^sub>C \<aa> \<bb> F)"
proof(intro tiny_categoryI'')
  show "vfsequence (\<Up>\<^sub>C \<aa> \<bb> F)" unfolding the_cat_parallel_def by simp
  show "vcard (\<Up>\<^sub>C \<aa> \<bb> F) = 6\<^sub>\<nat>"
    unfolding the_cat_parallel_def by (simp_all add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>" 
    by (auto simp: the_cat_parallel_components)
  show "\<R>\<^sub>\<circ> (\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>" 
    by (auto simp: the_cat_parallel_components)
  show "(gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Comp\<rparr>)) =
    (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b)"
    for gf
    unfolding the_cat_parallel_Comp_vdomain
  proof
    assume prems: "gf \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
    then obtain g f where gf_def: "gf = [g, f]\<^sub>\<circ>" 
      unfolding cat_parallel_composable_def by auto
    from prems show 
      "\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b"
      unfolding gf_def
      by (*slow*)
        (
          cases rule: cat_parallel_composableE; 
          (intro exI conjI)?; 
          cs_concl_step?;
          (simp only:)?,
          all\<open>intro is_arrI, unfold the_cat_parallel_components(2)\<close>
        )
        (
          cs_concl 
            cs_simp: cat_parallel_cs_simps V_cs_simps cs_intro: V_cs_intros
        )+
  next
    assume 
      "\<exists>g f b' c' a'. 
        gf = [g, f]\<^sub>\<circ> \<and> g : b' \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> c' \<and> f : a' \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b'"
    then obtain g f b c a 
      where gf_def: "gf = [g, f]\<^sub>\<circ>" 
        and g: "g : b \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> c"
        and f: "f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b" 
      by clarsimp
    from g f show "gf \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> F"
      unfolding gf_def 
      by (elim the_cat_parallel_is_arrE) (auto simp: cat_parallel_cs_intros)
  qed
  show "\<D>\<^sub>\<circ> (\<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr>) = \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>"
    by (simp add: cat_parallel_cs_simps the_cat_parallel_components)
  show "g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> c"
    if "g : b \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> c" and "f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b" for b c g a f
    using that
    by (elim the_cat_parallel_is_arrE; simp only:)
      (
        all\<open>
          solves\<open>simp add: cat_parallel_\<aa>\<bb>[symmetric]\<close> |
          cs_concl cs_simp: cat_parallel_cs_simps 
        \<close>
      )
  show 
    "h \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = 
      h \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> (g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f)"
    if "h : c \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> d" 
      and "g : b \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> c" 
      and "f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b"
    for c d h b g a f
    using that 
    by (elim the_cat_parallel_is_arrE; simp only:) (*slow*)
      (
        all\<open>
          solves\<open>simp only: cat_parallel_ineq cat_parallel_\<aa>\<bb>[symmetric]\<close> |
          cs_concl 
            cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros
          \<close>
      )
  show "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> a" if "a \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>" 
    for a
  proof-
    from that consider \<open>a = \<aa>\<close> | \<open>a = \<bb>\<close>
      unfolding the_cat_parallel_components(1) by auto
    then show "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> a"
      by cases
        (
          cs_concl 
            cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros
        )+
  qed
  show "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f = f" 
    if "f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b" for a b f
    using that
    by (elim the_cat_parallel_is_arrE)
      (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros)
  show "f \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr>\<lparr>b\<rparr> = f" 
    if "f : b \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> c" for b c f
    using that
    by (elim the_cat_parallel_is_arrE)
      (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros)
  show "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by 
      (
        cs_concl cs_shallow
          cs_simp: the_cat_parallel_components nat_omega_simps 
          cs_intro: V_cs_intros cat_parallel_cs_intros
      )
qed 
  (
    cs_concl  
      cs_simp: 
        nat_omega_simps cat_parallel_cs_simps the_cat_parallel_components(2) 
      cs_intro: 
        cat_cs_intros 
        cat_parallel_cs_intros 
        V_cs_intros 
        Limit_succ_in_VsetI
  )+

lemmas [cat_parallel_cs_intros] = cat_parallel.tiny_category_the_cat_parallel


subsubsection\<open>Opposite parallel category\<close>

lemma (in cat_parallel) op_cat_the_cat_parallel[cat_op_simps]: 
  "op_cat (\<Up>\<^sub>C \<aa> \<bb> F) = \<Up>\<^sub>C \<bb> \<aa> F"
proof(rule cat_eqI)
  interpret par: cat_parallel \<alpha> \<bb> \<aa> F by (rule cat_parallel_op) 
  show \<bb>\<aa>: "category \<alpha> (\<Up>\<^sub>C \<bb> \<aa> F)"
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_parallel_cs_intros)
  show \<aa>\<bb>: "category \<alpha> (op_cat (\<Up>\<^sub>C \<aa> \<bb> F))" 
    by 
      (
        cs_concl cs_shallow 
          cs_intro: cat_small_cs_intros cat_op_intros cat_parallel_cs_intros
      )
  interpret \<bb>\<aa>: category \<alpha> \<open>\<Up>\<^sub>C \<bb> \<aa> F\<close> by (rule \<bb>\<aa>)
  interpret \<aa>\<bb>: category \<alpha> \<open>\<Up>\<^sub>C \<aa> \<bb> F\<close>
    by (cs_concl cs_shallow cs_intro: cat_small_cs_intros cat_parallel_cs_intros)
  show "op_cat (\<Up>\<^sub>C \<aa> \<bb> F)\<lparr>Comp\<rparr> = \<Up>\<^sub>C \<bb> \<aa> F\<lparr>Comp\<rparr>"
  proof(rule vsv_eqI)
    show "vsv (op_cat (\<Up>\<^sub>C \<aa> \<bb> F)\<lparr>Comp\<rparr>)"
      unfolding op_cat_components by (rule fflip_vsv)
    show "vsv (\<Up>\<^sub>C \<bb> \<aa> F\<lparr>Comp\<rparr>)"
      by (cs_concl cs_shallow cs_intro: cat_parallel_cs_intros)
    show [cat_op_simps]: "\<D>\<^sub>\<circ> (op_cat (\<Up>\<^sub>C \<aa> \<bb> F)\<lparr>Comp\<rparr>) = \<D>\<^sub>\<circ> (\<Up>\<^sub>C \<bb> \<aa> F\<lparr>Comp\<rparr>)"
      by 
        (
          cs_concl cs_shallow
            cs_simp: 
              cat_parallel_composable_fconverse
              op_cat_components(5) 
              vdomain_fflip 
              cat_parallel_cs_simps 
            cs_intro: cat_cs_intros
        )
    fix gf assume "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_cat (\<Up>\<^sub>C \<aa> \<bb> F)\<lparr>Comp\<rparr>)"
    then have "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<Up>\<^sub>C \<bb> \<aa> F\<lparr>Comp\<rparr>)" unfolding cat_op_simps by simp
    then obtain g f a b c 
      where gf_def: "gf = [g, f]\<^sub>\<circ>" 
        and g: "g : b \<mapsto>\<^bsub>\<Up>\<^sub>C \<bb> \<aa> F\<^esub> c"
        and f: "f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<bb> \<aa> F\<^esub> b"
      by auto
    from g f show "op_cat (\<Up>\<^sub>C \<aa> \<bb> F)\<lparr>Comp\<rparr>\<lparr>gf\<rparr> = \<Up>\<^sub>C \<bb> \<aa> F\<lparr>Comp\<rparr>\<lparr>gf\<rparr>"
      unfolding gf_def
      by (elim par.the_cat_parallel_is_arrE)
        (
          simp add: cat_parallel_cs_intros | 
          cs_concl 
            cs_simp: cat_op_simps cat_parallel_cs_simps 
            cs_intro: cat_cs_intros cat_parallel_cs_intros
        )+
  qed
  show "op_cat (\<Up>\<^sub>C \<aa> \<bb> F)\<lparr>CId\<rparr> = \<Up>\<^sub>C \<bb> \<aa> F\<lparr>CId\<rparr>"
  proof(unfold cat_op_simps, rule vsv_eqI, unfold cat_parallel_cs_simps)  
    fix a assume "a \<in>\<^sub>\<circ> set {\<aa>, \<bb>}"
    then consider \<open>a = \<aa>\<close> | \<open>a = \<bb>\<close> by auto
    then show "\<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<Up>\<^sub>C \<bb> \<aa> F\<lparr>CId\<rparr>\<lparr>a\<rparr>"
      by cases (cs_concl cs_simp: cat_parallel_cs_simps)+
  qed auto
qed (auto simp: the_cat_parallel_components op_cat_components)

lemmas [cat_op_simps] = cat_parallel.op_cat_the_cat_parallel



subsection\<open>Parallel functor\<close>


subsubsection\<open>Background\<close>


text\<open>
See Chapter III-3 and Chapter III-4 in \<^cite>\<open>"mac_lane_categories_2010"\<close>).
\<close>


subsubsection\<open>Local assumptions for the parallel functor\<close>

locale cf_parallel = cat_parallel \<alpha> \<aa> \<bb> F + category \<alpha> \<CC> + F': vsv F'
  for \<alpha> \<aa> \<bb> F \<aa>' \<bb>' F' \<CC> :: V +
  assumes cf_parallel_F'_vdomain[cat_parallel_cs_simps]: "\<D>\<^sub>\<circ> F' = F"
    and cf_parallel_F'[cat_parallel_cs_intros]: "\<ff> \<in>\<^sub>\<circ> F \<Longrightarrow> F'\<lparr>\<ff>\<rparr> : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"
    and cf_parallel_\<aa>'[cat_parallel_cs_intros]: "\<aa>' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and cf_parallel_\<bb>'[cat_parallel_cs_intros]: "\<bb>' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"

lemmas (in cf_parallel) [cat_parallel_cs_intros] = F'.vsv_axioms 

lemma (in cf_parallel) cf_parallel_F''[cat_parallel_cs_intros]:
  assumes "\<ff> \<in>\<^sub>\<circ> F" and "a = \<aa>'" and "b = \<bb>'"
  shows "F'\<lparr>\<ff>\<rparr> : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using assms(1) unfolding assms(2-3) by (rule cf_parallel_F')

lemma (in cf_parallel) cf_parallel_F'''[cat_parallel_cs_intros]:
  assumes "\<ff> \<in>\<^sub>\<circ> F" and "f = F'\<lparr>\<ff>\<rparr>" and "b = \<bb>'"
  shows "f : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using assms(1) unfolding assms(2-3) by (rule cf_parallel_F')

lemma (in cf_parallel) cf_parallel_F''''[cat_parallel_cs_intros]:
  assumes "\<ff> \<in>\<^sub>\<circ> F" and "f = F'\<lparr>\<ff>\<rparr>" and "a = \<aa>'"
  shows "f : a \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"
  using assms(1) unfolding assms(2,3) by (rule cf_parallel_F')


text\<open>Rules.\<close>

lemma (in cf_parallel) cf_parallel_axioms'[cat_parallel_cs_intros]:
  assumes "\<alpha>' = \<alpha>" 
    and "a'' = \<aa>" 
    and "b'' = \<bb>" 
    and "F'' = F" 
    and "a''' = \<aa>'" 
    and "b''' = \<bb>'" 
    and "F''' = F'" 
  shows "cf_parallel \<alpha>' a'' b'' F'' a''' b''' F''' \<CC>"
  unfolding assms by (rule cf_parallel_axioms)

mk_ide rf cf_parallel_def[unfolded cf_parallel_axioms_def]
  |intro cf_parallelI|
  |dest cf_parallelD[dest]|
  |elim cf_parallelE[elim]|

lemmas [cat_parallel_cs_intros] = cf_parallelD(1,2)


text\<open>Duality.\<close>

lemma (in cf_parallel) cf_parallel_op[cat_op_intros]: 
  "cf_parallel \<alpha> \<bb> \<aa> F \<bb>' \<aa>' F' (op_cat \<CC>)"
  by (intro cf_parallelI, unfold cat_op_simps insert_commute) 
    (
      cs_concl 
        cs_simp: cat_parallel_cs_simps  
        cs_intro: cat_parallel_cs_intros cat_cs_intros cat_op_intros
    )+

lemmas [cat_op_intros] = cf_parallel.cf_parallel_op


subsubsection\<open>Definition and elementary properties\<close>

definition the_cf_parallel :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" 
  (\<open>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F\<close>)
  where "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F' =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>. (a = \<aa> ? \<aa>' : \<bb>')),
      (
        \<lambda>f\<in>\<^sub>\<circ>\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>.
          (
           if f = \<aa> \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>
            | f = \<bb> \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>
            | otherwise \<Rightarrow> F'\<lparr>f\<rparr> 
          )
      ),
      \<Up>\<^sub>C \<aa> \<bb> F,
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_cf_parallel_components:
  shows "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr> =
      (\<lambda>a\<in>\<^sub>\<circ>\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>. (a = \<aa> ? \<aa>' : \<bb>'))"
    and "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>\<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>.
          (
           if f = \<aa> \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>
            | f = \<bb> \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>
            | otherwise \<Rightarrow> F'\<lparr>f\<rparr> 
          )
      )"
    and [cat_parallel_cs_simps]: "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>HomDom\<rparr> = \<Up>\<^sub>C \<aa> \<bb> F"
    and [cat_parallel_cs_simps]: "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>HomCod\<rparr> = \<CC>"
  unfolding the_cf_parallel_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda the_cf_parallel_components(1)
  |vsv the_cf_parallel_ObjMap_vsv[cat_parallel_cs_intros]|
  |vdomain the_cf_parallel_ObjMap_vdomain[cat_parallel_cs_simps]|
  |app the_cf_parallel_ObjMap_app|

lemma (in cf_parallel) the_cf_parallel_ObjMap_app_\<aa>[cat_parallel_cs_simps]:
  assumes "x = \<aa>"
  shows "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<aa>'"
  by 
    (
      cs_concl 
        cs_simp: 
          assms the_cf_parallel_ObjMap_app cat_parallel_cs_simps V_cs_simps 
        cs_intro: cat_parallel_cs_intros
    )

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ObjMap_app_\<aa>

lemma (in cf_parallel) the_cf_parallel_ObjMap_app_\<bb>[cat_parallel_cs_simps]:
  assumes "x = \<bb>"
  shows "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<bb>'"
  using cat_parallel_ineq
  by 
    (
      cs_concl 
        cs_simp: 
          assms the_cf_parallel_ObjMap_app cat_parallel_cs_simps V_cs_simps 
        cs_intro: cat_parallel_cs_intros
    )

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ObjMap_app_\<bb>

lemma (in cf_parallel) the_cf_parallel_ObjMap_vrange:
  "\<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>) = set {\<aa>', \<bb>'}"
proof(intro vsubset_antisym)
  show "\<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> set {\<aa>', \<bb>'}"
    unfolding the_cf_parallel_components
    by (intro vrange_VLambda_vsubset)
      (simp_all add: cat_parallel_\<aa>\<bb> cf_parallel_\<aa>' cf_parallel_\<bb>')
  show "set {\<aa>', \<bb>'} \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>)"
  proof(rule vsubsetI)
    fix x assume prems: "x \<in>\<^sub>\<circ> set {\<aa>', \<bb>'}"
    from prems consider \<open>x = \<aa>'\<close> | \<open>x = \<bb>'\<close> by auto
    moreover have "\<aa>' \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>)"
      by (rule vsv.vsv_vimageI2'[of _ _ \<aa>])
        (
          cs_concl 
            cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros 
        )
    moreover have "\<bb>' \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>)"
      by (rule vsv.vsv_vimageI2'[of _ _ \<bb>])
        (
          cs_concl 
            cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros 
        )
    ultimately show "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>)" by auto
  qed
qed

lemma (in cf_parallel) the_cf_parallel_ObjMap_vrange_vsubset_Obj:
  "\<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  unfolding the_cf_parallel_components
  by (intro vrange_VLambda_vsubset)
    (simp_all add: cat_parallel_\<aa>\<bb> cf_parallel_\<aa>' cf_parallel_\<bb>')


subsubsection\<open>Arrow map\<close>

mk_VLambda the_cf_parallel_components(2)
  |vsv the_cf_parallel_ArrMap_vsv[cat_parallel_cs_intros]|
  |vdomain the_cf_parallel_ArrMap_vdomain[cat_parallel_cs_simps]|
  |app the_cf_parallel_ArrMap_app|

lemma (in cf_parallel) the_cf_parallel_ArrMap_app_F[cat_parallel_cs_simps]:
  assumes "f \<in>\<^sub>\<circ> F"
  shows "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = F'\<lparr>f\<rparr>"
proof-
  from assms have "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
    by (cs_concl cs_shallow cs_intro: cat_parallel_cs_intros a_in_succ_xI)
  from assms this show ?thesis
    using cat_parallel_ineq 
    by (auto simp: the_cf_parallel_ArrMap_app cat_parallel_cs_simps)
qed

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ArrMap_app_F

lemma (in cf_parallel) the_cf_parallel_ArrMap_app_\<aa>[cat_parallel_cs_simps]:
  assumes "f = \<aa>"
  shows "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>"
proof-
  from assms have "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
    by (cs_concl cs_intro: cat_parallel_cs_intros a_in_succ_xI)
  from this show ?thesis
    using cat_parallel_ineq
    by (elim the_cat_parallel_ArrE; simp only: assms) 
      (auto simp: the_cf_parallel_ArrMap_app)
qed

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ArrMap_app_\<aa>

lemma (in cf_parallel) the_cf_parallel_ArrMap_app_\<bb>[cat_parallel_cs_simps]:
  assumes "f = \<bb>"
  shows "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>"
proof-
  from assms have "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
    by (cs_concl cs_intro: cat_parallel_cs_intros a_in_succ_xI)
  from this show ?thesis
    using cat_parallel_ineq
    by (elim the_cat_parallel_ArrE; simp only: assms) 
      (auto simp: the_cf_parallel_ArrMap_app)
qed

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ArrMap_app_\<bb>

lemma (in cf_parallel) the_cf_parallel_ArrMap_vrange:
  "\<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>) = (F' `\<^sub>\<circ> F) \<union>\<^sub>\<circ> set {\<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>}"
  (is \<open>\<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>) = ?FF \<union>\<^sub>\<circ> ?CID\<close>)
proof(intro vsubset_antisym)

  show "\<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> ?FF \<union>\<^sub>\<circ> ?CID"
  proof
    (
      intro vsv.vsv_vrange_vsubset the_cf_parallel_ArrMap_vsv, 
      unfold the_cf_parallel_ArrMap_vdomain
    )
    fix f assume prems: "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
    from prems show "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> ?FF \<union>\<^sub>\<circ> ?CID"
      by (elim the_cat_parallel_ArrE; (simp only:)?)
        (
          cs_concl  
            cs_simp: vinsert_set_insert_eq cat_parallel_cs_simps 
            cs_intro: vsv.vsv_vimageI1 V_cs_intros
        )
  qed

  show "?FF \<union>\<^sub>\<circ> ?CID \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>)"
  proof(rule vsubsetI)
    fix f assume prems: "f \<in>\<^sub>\<circ> F' `\<^sub>\<circ> F \<union>\<^sub>\<circ> set {\<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>}"
    then consider \<open>f \<in>\<^sub>\<circ> F' `\<^sub>\<circ> F\<close> | \<open>f = \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>\<close> | \<open>f = \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>\<close> by auto
    then show "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>)"
    proof cases
      assume "f \<in>\<^sub>\<circ> F' `\<^sub>\<circ> F"
      then obtain \<ff> where \<ff>: "\<ff> \<in>\<^sub>\<circ> F" and f_def: "f = F'\<lparr>\<ff>\<rparr>" by auto
      from \<ff> have f_def': "f = \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>\<ff>\<rparr>"
        unfolding f_def by (cs_concl cs_simp: cat_parallel_cs_simps)
      from \<ff> have "\<ff> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>)"
        by 
          (
            cs_concl cs_shallow
              cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros
          )
      then show "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>)"
        unfolding f_def' 
        by (auto simp: cat_parallel_cs_intros intro: vsv.vsv_vimageI2)
    next
      assume prems: "f = \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>"
      have f_def': "f = \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>\<aa>\<rparr>"
        by (cs_concl cs_simp: cat_parallel_cs_simps prems)
      have "\<aa> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>)"
        by 
          (
            cs_concl 
              cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros
          )
      then show "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>)"
        unfolding f_def'
        by (auto simp: cat_parallel_cs_intros intro: vsv.vsv_vimageI2)
    next
      assume prems: "f = \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>"
      have f_def': "f = \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>\<bb>\<rparr>"
        by (cs_concl cs_shallow cs_simp: V_cs_simps cat_parallel_cs_simps prems)
      have "\<bb> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>)"
        by 
          (
            cs_concl 
              cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros
          )
      then show "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>)"
        unfolding f_def'
        by (auto simp: cat_parallel_cs_intros intro: vsv.vsv_vimageI2)
    qed
  qed

qed

lemma (in cf_parallel) the_cf_parallel_ArrMap_vrange_vsubset_Arr:
  "\<R>\<^sub>\<circ> (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof(intro vsv.vsv_vrange_vsubset, unfold cat_parallel_cs_simps)
  show "vsv (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>)" 
    by (cs_intro_step cat_parallel_cs_intros)
  fix f assume "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
  then show "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by (elim the_cat_parallel_ArrE)
      (
        cs_concl 
          cs_simp: cat_parallel_cs_simps  
          cs_intro: cat_cs_intros cat_parallel_cs_intros 
      )+
qed


subsubsection\<open>Parallel functor is a functor\<close>

lemma (in cf_parallel) cf_parallel_the_cf_parallel_is_tm_functor:
  "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F' : \<Up>\<^sub>C \<aa> \<bb> F \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_tm_functorI' is_functorI')

  interpret tcp: tiny_category \<alpha> \<open>\<Up>\<^sub>C \<aa> \<bb> F\<close> 
    by (rule tiny_category_the_cat_parallel)

  show "vfsequence (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F')" 
    unfolding the_cf_parallel_def by auto
  show "vcard (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F') = 4\<^sub>\<nat>"
    unfolding the_cf_parallel_def by (simp add: nat_omega_simps)
  show "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
    \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub>
    \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b" for a b f
    using that
    by (cases rule: the_cat_parallel_is_arrE; simp only:)
      (
        cs_concl 
          cs_simp: cat_parallel_cs_simps
          cs_intro: cat_cs_intros cat_parallel_cs_intros
      )+

  show
    "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> f\<rparr> =
      \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
      \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    if "g : b \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> c" and "f : a \<mapsto>\<^bsub>\<Up>\<^sub>C \<aa> \<bb> F\<^esub> b" for b c g a f
    using that
    by (elim the_cat_parallel_is_arrE) (*very slow*)
      (
        all\<open>simp only:\<close>, 
        all\<open>
          solves\<open>simp add: cat_parallel_ineq cat_parallel_\<aa>\<bb>[symmetric]\<close> | 
          cs_concl 
            cs_simp: cat_cs_simps cat_parallel_cs_simps 
            cs_intro: cat_cs_intros cat_parallel_cs_intros
          \<close>
      )

  show 
    "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>\<Up>\<^sub>C \<aa> \<bb> F\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> =
      \<CC>\<lparr>CId\<rparr>\<lparr>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
    if "c \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>" for c
    using that
    by (elim the_cat_parallel_ObjE; simp only:)
      (cs_concl cs_simp: cat_parallel_cs_simps)+

  show "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  proof
    (
      rule vbrelation.vbrelation_Limit_in_VsetI,
      unfold 
        the_cf_parallel_ObjMap_vdomain 
        the_cf_parallel_ObjMap_vrange 
        the_cat_parallel_components(1);
      (intro Limit_vdoubleton_in_VsetI)?
    )
    show "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" "\<bb> \<in>\<^sub>\<circ> Vset \<alpha>" "\<aa>' \<in>\<^sub>\<circ> Vset \<alpha>" "\<bb>' \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cs_concl cs_intro: cat_cs_intros cat_parallel_cs_intros)+
  qed (use the_cf_parallel_ObjMap_vsv in blast)+

  show "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  proof
    (
      rule vbrelation.vbrelation_Limit_in_VsetI,
      unfold 
        the_cf_parallel_ArrMap_vdomain 
        the_cf_parallel_ArrMap_vrange 
        the_cat_parallel_components(1);
      (intro tcp.tiny_cat_Arr_in_Vset vunion_in_VsetI Limit_vdoubleton_in_VsetI)?
    )
    show "\<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" "\<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cs_concl cs_intro: cat_cs_intros cat_parallel_cs_intros)+
    from cf_parallel_F' have "F' `\<^sub>\<circ> F \<subseteq>\<^sub>\<circ> Hom \<CC> \<aa>' \<bb>'"
      by (simp add: F'.vsv_vimage_vsubsetI)
    moreover have "Hom \<CC> \<aa>' \<bb>' \<in>\<^sub>\<circ> Vset \<alpha>"
      by (auto simp: cat_Hom_in_Vset cf_parallel_\<aa>' cf_parallel_\<bb>')
    ultimately show "F' `\<^sub>\<circ> F \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  qed (use the_cf_parallel_ArrMap_vsv in blast)+

qed
  (
    cs_concl 
      cs_simp: cat_parallel_cs_simps 
      cs_intro: 
        the_cf_parallel_ObjMap_vrange_vsubset_Obj 
        cat_parallel_cs_intros cat_cs_intros cat_small_cs_intros
  )+

lemma (in cf_parallel) cf_parallel_the_cf_parallel_is_tm_functor':
  assumes "\<AA>' = \<Up>\<^sub>C \<aa> \<bb> F" and "\<CC>' = \<CC>"
  shows "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule cf_parallel_the_cf_parallel_is_tm_functor)

lemmas [cat_parallel_cs_intros] =
  cf_parallel.cf_parallel_the_cf_parallel_is_tm_functor'


subsubsection\<open>Opposite parallel functor\<close>

lemma (in cf_parallel) cf_parallel_the_cf_parallel_op[cat_op_simps]:
  "op_cf (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F') = \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F (op_cat \<CC>) \<bb> \<aa> F \<bb>' \<aa>' F'"
proof-
  interpret \<up>: is_tm_functor \<alpha> \<open>\<Up>\<^sub>C \<aa> \<bb> F\<close> \<CC> \<open>\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<close>
    by (rule cf_parallel_the_cf_parallel_is_tm_functor)
  show ?thesis
  proof
    (
      rule cf_eqI[of \<alpha> \<open>\<Up>\<^sub>C \<bb> \<aa> F\<close> \<open>op_cat \<CC>\<close> _ \<open>\<Up>\<^sub>C \<bb> \<aa> F\<close> \<open>op_cat \<CC>\<close>], 
      unfold cat_op_simps
    )
    show "op_cf (\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F') : \<Up>\<^sub>C \<bb> \<aa> F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
      by (cs_concl cs_shallow cs_simp: cat_op_simps cs_intro: cat_op_intros)
    show "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F (op_cat \<CC>) \<bb> \<aa> F \<bb>' \<aa>' F' : \<Up>\<^sub>C \<bb> \<aa> F \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
      by 
        (
          cs_concl 
            cs_intro: cat_op_intros cat_small_cs_intros cat_parallel_cs_intros
        )
    show
      "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr> =
        \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F (op_cat \<CC>) \<bb> \<aa> F \<bb>' \<aa>' F'\<lparr>ObjMap\<rparr>"
    proof
      (
        rule vsv_eqI;
        (intro cat_parallel_cs_intros)?;
        unfold cat_parallel_cs_simps
      )
      fix a assume "a \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Obj\<rparr>"
      then consider \<open>a = \<aa>\<close> | \<open>a = \<bb>\<close> by (elim the_cat_parallel_ObjE) simp
      then show
        "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> =
          \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F (op_cat \<CC>) \<bb> \<aa> F \<bb>' \<aa>' F'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by cases
          (
            cs_concl 
              cs_simp: cat_parallel_cs_simps
              cs_intro: cat_parallel_cs_intros cat_op_intros
          )
    qed (auto simp: the_cat_parallel_components)
    show 
      "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr> =
        \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F (op_cat \<CC>) \<bb> \<aa> F \<bb>' \<aa>' F'\<lparr>ArrMap\<rparr>"
    proof
      (
        rule vsv_eqI;
        (intro cat_parallel_cs_intros)?; 
        unfold cat_parallel_cs_simps
      )
      fix f assume "f \<in>\<^sub>\<circ> \<Up>\<^sub>C \<aa> \<bb> F\<lparr>Arr\<rparr>"
      then consider \<open>f = \<aa>\<close> | \<open>f = \<bb>\<close> | \<open>f \<in>\<^sub>\<circ> F\<close>
        by (elim the_cat_parallel_ArrE) simp
      then show
        "\<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> F \<aa>' \<bb>' F'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
          \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F (op_cat \<CC>) \<bb> \<aa> F \<bb>' \<aa>' F'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        by cases
          (
            cs_concl 
              cs_simp: cat_parallel_cs_simps cat_op_simps 
              cs_intro: cat_parallel_cs_intros cat_op_intros
          )+
    qed (auto simp: the_cat_parallel_components)
  qed simp_all
qed

lemmas [cat_op_simps] = cf_parallel.cf_parallel_the_cf_parallel_op



subsection\<open>
Background for the definition of a category with two parallel arrows 
between two objects
\<close>


text\<open>
The case of two parallel arrows between two objects is treated explicitly 
because it is prevalent in applications.
\<close>

definition \<gg>\<^sub>P\<^sub>L :: V where "\<gg>\<^sub>P\<^sub>L = 0"
definition \<ff>\<^sub>P\<^sub>L :: V where "\<ff>\<^sub>P\<^sub>L = 1\<^sub>\<nat>"

definition \<aa>\<^sub>P\<^sub>L\<^sub>2 :: V where "\<aa>\<^sub>P\<^sub>L\<^sub>2 = \<aa>\<^sub>P\<^sub>L (set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L})"
definition \<bb>\<^sub>P\<^sub>L\<^sub>2 :: V where "\<bb>\<^sub>P\<^sub>L\<^sub>2 = \<bb>\<^sub>P\<^sub>L (set {\<gg>\<^sub>P\<^sub>L, \<ff>\<^sub>P\<^sub>L})"

lemma cat_PL2_ineq:
  shows cat_PL2_\<aa>\<bb>[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L\<^sub>2 \<noteq> \<bb>\<^sub>P\<^sub>L\<^sub>2"
    and cat_PL2_\<aa>\<gg>[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L\<^sub>2 \<noteq> \<gg>\<^sub>P\<^sub>L"
    and cat_PL2_\<aa>\<ff>[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L\<^sub>2 \<noteq> \<ff>\<^sub>P\<^sub>L"
    and cat_PL2_\<bb>\<gg>[cat_parallel_cs_intros]: "\<bb>\<^sub>P\<^sub>L\<^sub>2 \<noteq> \<gg>\<^sub>P\<^sub>L"
    and cat_PL2_\<bb>\<ff>[cat_parallel_cs_intros]: "\<bb>\<^sub>P\<^sub>L\<^sub>2 \<noteq> \<ff>\<^sub>P\<^sub>L"
    and cat_PL2_\<gg>\<ff>[cat_parallel_cs_intros]: "\<gg>\<^sub>P\<^sub>L \<noteq> \<ff>\<^sub>P\<^sub>L"
  unfolding \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def \<gg>\<^sub>P\<^sub>L_def \<ff>\<^sub>P\<^sub>L_def \<aa>\<^sub>P\<^sub>L_def \<bb>\<^sub>P\<^sub>L_def 
  by (simp_all add: Set.doubleton_eq_iff one)
  
lemma (in \<Z>) 
  shows cat_PL2_\<aa>[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L\<^sub>2 \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_PL2_\<bb>[cat_parallel_cs_intros]: "\<bb>\<^sub>P\<^sub>L\<^sub>2 \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_PL2_\<gg>[cat_parallel_cs_intros]: "\<gg>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_PL2_\<ff>[cat_parallel_cs_intros]: "\<ff>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> Vset \<alpha>"
  unfolding \<aa>\<^sub>P\<^sub>L_def \<bb>\<^sub>P\<^sub>L_def \<aa>\<^sub>P\<^sub>L\<^sub>2_def \<bb>\<^sub>P\<^sub>L\<^sub>2_def \<gg>\<^sub>P\<^sub>L_def \<ff>\<^sub>P\<^sub>L_def 
  by (simp_all add: Limit_vdoubleton_in_VsetI)



subsection\<open>
Local assumptions for a category with two parallel arrows between two objects
\<close>

locale cat_parallel_2 = \<Z> \<alpha> for \<alpha> +  
  fixes \<aa> \<bb> \<gg> \<ff>
  assumes cat_parallel_2_\<aa>\<bb>[cat_parallel_cs_intros]: "\<aa> \<noteq> \<bb>"
    and cat_parallel_2_\<aa>\<gg>[cat_parallel_cs_intros]: "\<aa> \<noteq> \<gg>"
    and cat_parallel_2_\<aa>\<ff>[cat_parallel_cs_intros]: "\<aa> \<noteq> \<ff>"
    and cat_parallel_2_\<bb>\<gg>[cat_parallel_cs_intros]: "\<bb> \<noteq> \<gg>"
    and cat_parallel_2_\<bb>\<ff>[cat_parallel_cs_intros]: "\<bb> \<noteq> \<ff>"
    and cat_parallel_2_\<gg>\<ff>[cat_parallel_cs_intros]: "\<gg> \<noteq> \<ff>"
    and cat_parallel_2_\<aa>_in_Vset[cat_parallel_cs_intros]: "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_parallel_2_\<bb>_in_Vset[cat_parallel_cs_intros]: "\<bb> \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_parallel_2_\<gg>_in_Vset[cat_parallel_cs_intros]: "\<gg> \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_parallel_2_\<ff>_in_Vset[cat_parallel_cs_intros]: "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>"

lemmas (in cat_parallel_2) cat_parallel_ineq =
  cat_parallel_2_\<aa>\<bb>
  cat_parallel_2_\<aa>\<gg>
  cat_parallel_2_\<aa>\<ff>
  cat_parallel_2_\<bb>\<gg>
  cat_parallel_2_\<bb>\<ff>
  cat_parallel_2_\<gg>\<ff>


text\<open>Rules.\<close>

lemmas (in cat_parallel_2) [cat_parallel_cs_intros] = cat_parallel_2_axioms

mk_ide rf cat_parallel_2_def[unfolded cat_parallel_2_axioms_def]
  |intro cat_parallel_2I|
  |dest cat_parallel_2D[dest]|
  |elim cat_parallel_2E[elim]|

sublocale cat_parallel_2 \<subseteq> cat_parallel \<alpha> \<aa> \<bb> \<open>set {\<gg>, \<ff>}\<close>
  by unfold_locales 
    (simp_all add: cat_parallel_cs_intros Limit_vdoubleton_in_VsetI)


text\<open>Duality.\<close>

lemma (in cat_parallel_2) cat_parallel_op[cat_op_intros]: 
  "cat_parallel_2 \<alpha> \<bb> \<aa> \<ff> \<gg>"
  by (intro cat_parallel_2I) 
    (auto intro!: cat_parallel_cs_intros cat_parallel_ineq[symmetric])



subsection\<open>\<open>\<up>\<up>\<close>: category with two parallel arrows between two objects\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 and Chapter III-3 in \<^cite>\<open>"mac_lane_categories_2010"\<close>.\<close>

definition the_cat_parallel_2 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>\<up>\<up>\<^sub>C\<close>)
  where "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff> = \<Up>\<^sub>C \<aa> \<bb> (set {\<gg>, \<ff>})"


text\<open>Components.\<close>

lemma the_cat_parallel_2_components:
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr> = set {\<aa>, \<bb>}"
    and "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr> = set {\<aa>, \<bb>, \<gg>, \<ff>}"
  unfolding the_cat_parallel_2_def the_cat_parallel_components by auto


text\<open>Elementary properties.\<close>

lemma the_cat_parallel_2_commute: "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff> = \<up>\<up>\<^sub>C \<aa> \<bb> \<ff> \<gg>"
  unfolding the_cat_parallel_2_def by (simp add: insert_commute)

lemma cat_parallel_is_cat_parallel_2:
  assumes "cat_parallel \<alpha> \<aa> \<bb> (set {\<gg>, \<ff>})" and "\<gg> \<noteq> \<ff>"
  shows "cat_parallel_2 \<alpha> \<aa> \<bb> \<gg> \<ff>"
proof-
  interpret cat_parallel \<alpha> \<aa> \<bb> \<open>set {\<gg>, \<ff>}\<close> by (rule assms(1))
  show ?thesis
    using cat_parallel_\<aa>F cat_parallel_\<bb>F cat_parallel_F_in_Vset assms
    by (intro cat_parallel_2I)
      (
        auto 
          dest: vdoubleton_in_VsetD 
          simp: cat_parallel_\<aa>_in_Vset cat_parallel_\<bb>_in_Vset
     )
qed


subsubsection\<open>Objects\<close>

lemma the_cat_parallel_2_Obj_\<aa>I[cat_parallel_cs_intros]:
  assumes "a = \<aa>"
  shows "a \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
  unfolding the_cat_parallel_2_def
  by (cs_concl cs_simp: assms cs_intro: cat_parallel_cs_intros)

lemma the_cat_parallel_2_Obj_\<bb>I[cat_parallel_cs_intros]:
  assumes "a = \<bb>"
  shows "a \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
  unfolding the_cat_parallel_2_def
  by (cs_concl cs_shallow cs_simp: assms cs_intro: cat_parallel_cs_intros)

lemma the_cat_parallel_2_ObjE:
  assumes "a \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
  obtains "a = \<aa>" | "a = \<bb>" 
  using assms unfolding the_cat_parallel_2_def by (elim the_cat_parallel_ObjE)


subsubsection\<open>Arrows\<close>

lemma the_cat_parallel_2_Arr_\<aa>I[cat_parallel_cs_intros]:
  assumes "f = \<aa>"  
  shows "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_parallel_2_def by (intro the_cat_parallel_Arr_\<aa>I)

lemma the_cat_parallel_2_Arr_\<bb>I[cat_parallel_cs_intros]:
  assumes "f = \<bb>"  
  shows "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_parallel_2_def by (intro the_cat_parallel_Arr_\<bb>I)

lemma the_cat_parallel_2_Arr_\<gg>I[cat_parallel_cs_intros]:
  assumes "f = \<gg>"
  shows "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  unfolding assms(1) the_cat_parallel_2_def
  by (cs_concl cs_simp: V_cs_simps cs_intro: V_cs_intros cat_parallel_cs_intros)

lemma the_cat_parallel_2_Arr_\<ff>I[cat_parallel_cs_intros]:
  assumes "f = \<ff>"
  shows "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  unfolding assms(1) the_cat_parallel_2_def
  by 
    (
      cs_concl cs_shallow 
        cs_simp: V_cs_simps cs_intro: V_cs_intros cat_parallel_cs_intros
    )

lemma the_cat_parallel_2_ArrE:
  assumes "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  obtains "f = \<aa>" | "f = \<bb>" | "f = \<gg>" | "f = \<ff>"
  using assms that 
  unfolding the_cat_parallel_2_def
  by (auto elim!: the_cat_parallel_ArrE)


subsubsection\<open>Domain\<close>

lemma the_cat_parallel_2_Dom_vsv[cat_parallel_cs_intros]: "vsv (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>)"
  unfolding the_cat_parallel_2_def by (rule the_cat_parallel_Dom_vsv)

lemma the_cat_parallel_2_Dom_vdomain[cat_parallel_cs_simps]: 
  "\<D>\<^sub>\<circ> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>) = set {\<aa>, \<bb>, \<gg>, \<ff>}"
  unfolding the_cat_parallel_2_def the_cat_parallel_Dom_vdomain by auto

lemma (in cat_parallel_2) the_cat_parallel_2_Dom_app_\<bb>[cat_parallel_cs_simps]:
  assumes "f = \<bb>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<bb>"
  using assms 
  unfolding the_cat_parallel_2_def 
  by (simp add: the_cat_parallel_Dom_app_\<bb>)

lemmas [cat_parallel_cs_simps] = cat_parallel_2.the_cat_parallel_2_Dom_app_\<bb>

lemma (in cat_parallel_2) the_cat_parallel_2_Dom_app_\<gg>[cat_parallel_cs_simps]:
  assumes "f = \<gg>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>"
  using assms
  unfolding the_cat_parallel_2_def
  by (intro the_cat_parallel_Dom_app_F) simp

lemmas [cat_parallel_cs_simps] = cat_parallel_2.the_cat_parallel_2_Dom_app_\<gg>

lemma (in cat_parallel_2) the_cat_parallel_2_Dom_app_\<ff>[cat_parallel_cs_simps]:
  assumes "f = \<ff>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>"
  using assms
  unfolding the_cat_parallel_2_def
  by (intro the_cat_parallel_Dom_app_F) simp

lemmas [cat_parallel_cs_simps] = cat_parallel_2.the_cat_parallel_2_Dom_app_\<ff>

lemma (in cat_parallel_2) the_cat_parallel_2_Dom_app_\<aa>[cat_parallel_cs_simps]:
  assumes "f = \<aa>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>"
  using assms 
  unfolding the_cat_parallel_2_def 
  by (simp add: the_cat_parallel_Dom_app_\<aa>)

lemmas [cat_parallel_cs_simps] = cat_parallel_2.the_cat_parallel_2_Dom_app_\<aa>


subsubsection\<open>Codomain\<close>

lemma the_cat_parallel_2_Cod_vsv[cat_parallel_cs_intros]: "vsv (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>)"
  unfolding the_cat_parallel_2_def by (rule the_cat_parallel_Cod_vsv)

lemma the_cat_parallel_2_Cod_vdomain[cat_parallel_cs_simps]: 
  "\<D>\<^sub>\<circ> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>) = set {\<aa>, \<bb>, \<gg>, \<ff>}"
  unfolding the_cat_parallel_2_def the_cat_parallel_Cod_vdomain by auto

lemma (in cat_parallel_2) the_cat_parallel_2_Cod_app_\<bb>[cat_parallel_cs_simps]:
  assumes "f = \<bb>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
  using assms 
  unfolding the_cat_parallel_2_def 
  by (simp add: the_cat_parallel_Cod_app_\<bb>)

lemmas [cat_parallel_cs_simps] = cat_parallel_2.the_cat_parallel_2_Cod_app_\<bb>

lemma (in cat_parallel_2) the_cat_parallel_2_Cod_app_\<gg>[cat_parallel_cs_simps]:
  assumes "f = \<gg>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
  using assms
  unfolding the_cat_parallel_2_def
  by (intro the_cat_parallel_Cod_app_F) simp

lemmas [cat_parallel_cs_simps] = cat_parallel_2.the_cat_parallel_2_Cod_app_\<gg>

lemma (in cat_parallel_2) the_cat_parallel_2_Cod_app_\<ff>[cat_parallel_cs_simps]:
  assumes "f = \<ff>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
  using assms
  unfolding the_cat_parallel_2_def
  by (intro the_cat_parallel_Cod_app_F) simp

lemmas [cat_parallel_cs_simps] = cat_parallel_2.the_cat_parallel_2_Cod_app_\<ff>

lemma (in cat_parallel_2) the_cat_parallel_2_Cod_app_\<aa>[cat_parallel_cs_simps]:
  assumes "f = \<aa>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<aa>"
  using assms 
  unfolding the_cat_parallel_2_def 
  by (simp add: the_cat_parallel_Cod_app_\<aa>)

lemmas [cat_parallel_cs_simps] = cat_parallel_2.the_cat_parallel_2_Cod_app_\<aa>


subsubsection\<open>Composition\<close>

lemma the_cat_parallel_2_Comp_vsv[cat_parallel_cs_intros]:
  "vsv (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Comp\<rparr>)"
  unfolding the_cat_parallel_2_def by (rule the_cat_parallel_Comp_vsv)

lemma the_cat_parallel_2_Comp_app_\<bb>\<bb>[cat_parallel_cs_simps]:
  assumes "g = \<bb>" and "f = \<bb>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
proof-
  note gf = the_cat_parallel_Comp_app_\<bb>\<bb>[OF assms, where F=\<open>set {\<gg>, \<ff>}\<close>]
  show "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
    unfolding the_cat_parallel_2_def 
    subgoal unfolding gf(1) by simp
    subgoal unfolding gf(2) by simp
    done
qed

lemma the_cat_parallel_2_Comp_app_\<aa>\<aa>[cat_parallel_cs_simps]:
  assumes "g = \<aa>" and "f = \<aa>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
proof-
  note gf = the_cat_parallel_Comp_app_\<aa>\<aa>[OF assms, where F=\<open>set {\<gg>, \<ff>}\<close>]
  show "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
    unfolding the_cat_parallel_2_def 
    subgoal unfolding gf(1) by simp
    subgoal unfolding gf(2) by simp
    done
qed

lemma the_cat_parallel_2_Comp_app_\<bb>\<gg>[cat_parallel_cs_simps]:
  assumes "g = \<bb>" and "f = \<gg>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
  unfolding 
    the_cat_parallel_2_def assms
    the_cat_parallel_Comp_app_\<bb>F[
      where F=\<open>set {\<gg>, \<ff>}\<close>, OF assms(1), of \<gg>, unfolded assms, simplified
      ]
  by simp

lemma the_cat_parallel_2_Comp_app_\<bb>\<ff>[cat_parallel_cs_simps]:
  assumes "g = \<bb>" and "f = \<ff>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f" 
  unfolding 
    the_cat_parallel_2_def assms
    the_cat_parallel_Comp_app_\<bb>F[
      where F=\<open>set {\<gg>, \<ff>}\<close>, OF assms(1), of \<ff>, unfolded assms, simplified
      ]
  by simp

lemma (in cat_parallel_2) the_cat_parallel_2_Comp_app_\<gg>\<aa>[cat_parallel_cs_simps]:
  assumes "g = \<gg>" and "f = \<aa>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" 
  unfolding 
    the_cat_parallel_2_def assms
    the_cat_parallel_Comp_app_F\<aa>[
      of \<gg>, OF _ assms(2), unfolded assms, simplified
      ]
  by simp

lemma (in cat_parallel_2) the_cat_parallel_2_Comp_app_\<ff>\<aa>[cat_parallel_cs_simps]:
  assumes "g = \<ff>" and "f = \<aa>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" 
  unfolding 
    the_cat_parallel_2_def assms
    the_cat_parallel_Comp_app_F\<aa>[
      of \<ff>, OF _ assms(2), unfolded assms, simplified
      ]
  by simp


subsubsection\<open>Identity\<close>

lemma the_cat_parallel_2_CId_vsv[cat_parallel_cs_intros]: "vsv (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>)"
  unfolding the_cat_parallel_2_def by (rule the_cat_parallel_CId_vsv)

lemma the_cat_parallel_2_CId_vdomain[cat_parallel_cs_simps]:
  "\<D>\<^sub>\<circ> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>) = set {\<aa>, \<bb>}"
  unfolding the_cat_parallel_2_def by (rule the_cat_parallel_CId_vdomain)
  
lemma the_cat_parallel_2_CId_app_\<aa>[cat_parallel_cs_simps]: 
  assumes "a = \<aa>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<aa>"
  unfolding assms the_cat_parallel_2_def
  by (simp add: the_cat_parallel_CId_app_\<aa>)

lemma the_cat_parallel_2_CId_app_\<bb>[cat_parallel_cs_simps]: 
  assumes "a = \<bb>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<bb>"
  unfolding assms the_cat_parallel_2_def
  by (simp add: the_cat_parallel_CId_app_\<bb>)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma (in cat_parallel_2) the_cat_parallel_2_is_arr_\<aa>\<aa>\<aa>[cat_parallel_cs_intros]:
  assumes "a' = \<aa>" and "b' = \<aa>" and "f = \<aa>"
  shows "f : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
  unfolding assms the_cat_parallel_2_def
  by (simp add: the_cat_parallel_is_arr_\<aa>\<aa>\<aa>)

lemma (in cat_parallel_2) the_cat_parallel_2_is_arr_\<bb>\<bb>\<bb>[cat_parallel_cs_intros]:
  assumes "a' = \<bb>" and "b' = \<bb>" and "f = \<bb>"
  shows "f : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
  unfolding assms the_cat_parallel_2_def
  by (simp add: the_cat_parallel_is_arr_\<bb>\<bb>\<bb>)

lemma (in cat_parallel_2) the_cat_parallel_2_is_arr_\<aa>\<bb>\<gg>[cat_parallel_cs_intros]:
  assumes "a' = \<aa>" and "b' = \<bb>" and "f = \<gg>"
  shows "f : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
  unfolding assms the_cat_parallel_2_def
  by 
    (
      rule the_cat_parallel_is_arr_\<aa>\<bb>F[
        OF assms(1,2), of \<gg>, unfolded assms, simplified
        ]
    )

lemma (in cat_parallel_2) the_cat_parallel_2_is_arr_\<aa>\<bb>\<ff>[cat_parallel_cs_intros]:
  assumes "a' = \<aa>" and "b' = \<bb>" and "f = \<ff>"
  shows "f : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
  unfolding assms the_cat_parallel_2_def
  by 
    (
      rule the_cat_parallel_is_arr_\<aa>\<bb>F[
        OF assms(1,2), of \<ff>, unfolded assms, simplified
        ]
    )

lemma (in cat_parallel_2) the_cat_parallel_2_is_arrE:
  assumes "f' : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
  obtains "a' = \<aa>" and "b' = \<aa>" and "f' = \<aa>"
        | "a' = \<bb>" and "b' = \<bb>" and "f' = \<bb>"
        | "a' = \<aa>" and "b' = \<bb>" and "f' = \<gg>"
        | "a' = \<aa>" and "b' = \<bb>" and "f' = \<ff>"
  using assms 
  unfolding the_cat_parallel_2_def
  by (elim the_cat_parallel_is_arrE) auto


subsubsection\<open>\<open>\<up>\<up>\<close> is a category\<close>

lemma (in cat_parallel_2) 
  finite_category_the_cat_parallel_2[cat_parallel_cs_intros]:
  "finite_category \<alpha> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)"
proof(intro finite_categoryI'' )
  show "tiny_category \<alpha> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)"
    unfolding the_cat_parallel_2_def by (rule tiny_category_the_cat_parallel)
qed (auto simp: the_cat_parallel_2_components)

lemmas [cat_parallel_cs_intros] = 
  cat_parallel_2.finite_category_the_cat_parallel_2


subsubsection\<open>Opposite parallel category\<close>

lemma (in cat_parallel_2) op_cat_the_cat_parallel_2[cat_op_simps]: 
  "op_cat (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>) = \<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>"
  unfolding the_cat_parallel_2_def cat_op_simps by (metis doubleton_eq_iff)

lemmas [cat_op_simps] = cat_parallel_2.op_cat_the_cat_parallel_2



subsection\<open>
Parallel functor for a category with two parallel arrows between two objects
\<close>

locale cf_parallel_2 = cat_parallel_2 \<alpha> \<aa> \<bb> \<gg> \<ff> + category \<alpha> \<CC> 
  for \<alpha> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' \<CC> :: V +
  assumes cf_parallel_\<gg>'[cat_parallel_cs_intros]: "\<gg>' : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"
    and cf_parallel_\<ff>'[cat_parallel_cs_intros]: "\<ff>' : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"

sublocale cf_parallel_2 \<subseteq> 
  cf_parallel \<alpha> \<aa> \<bb> \<open>set {\<gg>, \<ff>}\<close> \<aa>' \<bb>' \<open>\<lambda>f\<in>\<^sub>\<circ>set {\<gg>, \<ff>}. (f = \<ff> ? \<ff>' : \<gg>')\<close> \<CC>
  by unfold_locales (auto intro: cat_parallel_cs_intros cat_cs_intros)

lemma (in cf_parallel_2) cf_parallel_2_\<gg>''[cat_parallel_cs_intros]:
  assumes "a = \<aa>'" and "b = \<bb>'"
  shows "\<gg>' : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_parallel_\<gg>')

lemma (in cf_parallel_2) cf_parallel_2_\<gg>'''[cat_parallel_cs_intros]:
  assumes "g = \<gg>'" and "b = \<bb>'"
  shows "g : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_parallel_\<gg>')

lemma (in cf_parallel_2) cf_parallel_2_\<gg>''''[cat_parallel_cs_intros]:
  assumes "g = \<gg>'" and "a = \<aa>'"
  shows "g : a \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"
  unfolding assms by (rule cf_parallel_\<gg>')

lemma (in cf_parallel_2) cf_parallel_2_\<ff>''[cat_parallel_cs_intros]:
  assumes "a = \<aa>'" and "b = \<bb>'"
  shows "\<ff>' : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_parallel_\<ff>') 

lemma (in cf_parallel_2) cf_parallel_2_\<ff>'''[cat_parallel_cs_intros]:
  assumes "f = \<ff>'" and "b = \<bb>'"
  shows "f : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_parallel_\<ff>')

lemma (in cf_parallel_2) cf_parallel_2_\<ff>''''[cat_parallel_cs_intros]:
  assumes "f = \<ff>'" and "a = \<aa>'"
  shows "f : a \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"
  unfolding assms by (rule cf_parallel_\<ff>') 


text\<open>Rules.\<close>

lemma (in cf_parallel_2) cf_parallel_axioms'[cat_parallel_cs_intros]:
  assumes "\<alpha>' = \<alpha>" 
    and "a = \<aa>" 
    and "b = \<bb>" 
    and "g = \<gg>" 
    and "f = \<ff>" 
    and "a' = \<aa>'" 
    and "b' = \<bb>'" 
    and "g' = \<gg>'" 
    and "f' = \<ff>'" 
  shows "cf_parallel_2 \<alpha>' a b g f a' b' g' f' \<CC>"
  unfolding assms by (rule cf_parallel_2_axioms)

mk_ide rf cf_parallel_2_def[unfolded cf_parallel_2_axioms_def]
  |intro cf_parallel_2I|
  |dest cf_parallel_2D[dest]|
  |elim cf_parallel_2E[elim]|

lemmas [cat_parallel_cs_intros] = cf_parallelD(1,2)


text\<open>Duality.\<close>

lemma (in cf_parallel_2) cf_parallel_2_op[cat_op_intros]: 
  "cf_parallel_2 \<alpha> \<bb> \<aa> \<ff> \<gg> \<bb>' \<aa>' \<ff>' \<gg>' (op_cat \<CC>)"
  by (intro cf_parallel_2I, unfold cat_op_simps)
    (cs_concl cs_intro: cat_parallel_cs_intros cat_cs_intros cat_op_intros)

lemmas [cat_op_intros] = cf_parallel.cf_parallel_op


subsubsection\<open>Definition and elementary properties\<close>

definition the_cf_parallel_2 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" 
  (\<open>\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F\<close>)
  where "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' =
    \<Up>\<rightarrow>\<Up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> (set {\<gg>, \<ff>}) \<aa>' \<bb>' (\<lambda>f\<in>\<^sub>\<circ>set {\<gg>, \<ff>}. (f = \<ff> ? \<ff>' : \<gg>'))"


text\<open>Components.\<close>

lemma the_cf_parallel_2_components:
  shows [cat_parallel_cs_simps]: 
      "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>HomDom\<rparr> = \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>"
    and [cat_parallel_cs_simps]: 
      "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>HomCod\<rparr> = \<CC>"
  unfolding 
    the_cf_parallel_2_def the_cat_parallel_2_def the_cf_parallel_components
  by simp_all


text\<open>Elementary properties.\<close>

lemma (in cf_parallel_2) cf_parallel_2_the_cf_parallel_2_commute:
  "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' = \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<ff> \<gg> \<aa>' \<bb>' \<ff>' \<gg>'"
  using cat_parallel_2_\<gg>\<ff> 
  unfolding the_cf_parallel_2_def insert_commute
  by (force simp: VLambda_vdoubleton)

lemma cf_parallel_is_cf_parallel_2:
  assumes 
    "cf_parallel \<alpha> \<aa> \<bb> (set {\<gg>, \<ff>}) \<aa>' \<bb>' (\<lambda>f\<in>\<^sub>\<circ>set {\<gg>, \<ff>}. (f = \<ff> ? \<ff>' : \<gg>')) \<CC>" 
    and "\<gg> \<noteq> \<ff>"
  shows "cf_parallel_2 \<alpha> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' \<CC>"
proof-
  interpret
    cf_parallel \<alpha> \<aa> \<bb> \<open>set {\<gg>, \<ff>}\<close> \<aa>' \<bb>' \<open>\<lambda>f\<in>\<^sub>\<circ>set {\<gg>, \<ff>}. (f = \<ff> ? \<ff>' : \<gg>')\<close> \<CC>  
    by (rule assms(1))
  have \<gg>\<ff>: "\<gg> \<in>\<^sub>\<circ> set {\<gg>, \<ff>}" "\<ff> \<in>\<^sub>\<circ> set {\<gg>, \<ff>}" by auto
  show ?thesis
    using cat_parallel_axioms assms(2) category_axioms \<gg>\<ff>[THEN cf_parallel_F']
    by (intro cf_parallel_2I cat_parallel_is_cat_parallel_2) 
      (auto simp: assms(2))
qed


subsubsection\<open>Object map\<close>

lemma the_cf_parallel_2_ObjMap_vsv[cat_parallel_cs_intros]: 
  "vsv (\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>)"
  unfolding the_cf_parallel_2_def by (intro cat_parallel_cs_intros)

lemma the_cf_parallel_2_ObjMap_vdomain[cat_parallel_cs_simps]: 
  "\<D>\<^sub>\<circ> (\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>) = \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
  unfolding the_cf_parallel_2_def
  by (cs_concl cs_shallow cs_simp: cat_parallel_cs_simps the_cat_parallel_2_def) 

lemma (in cf_parallel_2) the_cf_parallel_2_ObjMap_app_\<aa>[cat_parallel_cs_simps]:
  assumes "x = \<aa>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<aa>'"
  unfolding the_cf_parallel_2_def 
  by (cs_concl cs_simp: assms cat_parallel_cs_simps)

lemmas [cat_parallel_cs_simps] = cf_parallel_2.the_cf_parallel_2_ObjMap_app_\<aa>

lemma (in cf_parallel_2) the_cf_parallel_2_ObjMap_app_\<bb>[cat_parallel_cs_simps]:
  assumes "x = \<bb>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<bb>'"
  unfolding the_cf_parallel_2_def 
  by (cs_concl cs_shallow cs_simp: assms cat_parallel_cs_simps)

lemmas [cat_parallel_cs_simps] = cf_parallel_2.the_cf_parallel_2_ObjMap_app_\<bb>

lemma (in cf_parallel_2) the_cf_parallel_2_ObjMap_vrange:
  "\<R>\<^sub>\<circ> (\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>) = set {\<aa>', \<bb>'}"
  unfolding the_cf_parallel_2_def by (rule the_cf_parallel_ObjMap_vrange)

lemma (in cf_parallel_2) the_cf_parallel_2_ObjMap_vrange_vsubset_Obj:
  "\<R>\<^sub>\<circ> (\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  unfolding the_cf_parallel_2_def 
  by (rule the_cf_parallel_ObjMap_vrange_vsubset_Obj)


subsubsection\<open>Arrow map\<close>

lemma (in cf_parallel_2) the_cf_parallel_2_ArrMap_app_\<gg>[cat_parallel_cs_simps]:
  assumes "f = \<gg>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<gg>'"
  unfolding the_cf_parallel_2_def assms
  by
    (
      cs_concl 
        cs_simp: V_cs_simps cat_parallel_cs_simps 
        cs_intro: V_cs_intros cat_parallel_cs_intros
    )

lemmas [cat_parallel_cs_simps] = cf_parallel_2.the_cf_parallel_2_ArrMap_app_\<gg>

lemma (in cf_parallel_2) the_cf_parallel_2_ArrMap_app_\<ff>[cat_parallel_cs_simps]:
  assumes "f = \<ff>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<ff>'"
  unfolding the_cf_parallel_2_def assms
  by
    (
      cs_concl 
        cs_simp: V_cs_simps cat_parallel_cs_simps 
        cs_intro: V_cs_intros cat_parallel_cs_intros
    )

lemmas [cat_parallel_cs_simps] = cf_parallel_2.the_cf_parallel_2_ArrMap_app_\<ff>

lemma (in cf_parallel_2) the_cf_parallel_2_ArrMap_app_\<aa>[cat_parallel_cs_simps]:
  assumes "f = \<aa>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>"
  unfolding the_cf_parallel_2_def assms
  by (cs_concl cs_simp: cat_parallel_cs_simps)

lemmas [cat_parallel_cs_simps] = cf_parallel_2.the_cf_parallel_2_ArrMap_app_\<aa>

lemma (in cf_parallel_2) the_cf_parallel_2_ArrMap_app_\<bb>[cat_parallel_cs_simps]:
  assumes "f = \<bb>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>"
  unfolding the_cf_parallel_2_def assms
  by (cs_concl cs_shallow cs_simp: cat_parallel_cs_simps)

lemmas [cat_parallel_cs_simps] = cf_parallel_2.the_cf_parallel_2_ArrMap_app_\<bb>

lemma (in cf_parallel_2) the_cf_parallel_2_ArrMap_vrange:
  "\<R>\<^sub>\<circ> (\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>) = set {\<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>, \<ff>', \<gg>'}"
  unfolding the_cf_parallel_2_def the_cf_parallel_ArrMap_vrange
  using cat_parallel_2_\<gg>\<ff> 
  by (auto simp: app_vimage_iff VLambda_vdoubleton)

lemma (in cf_parallel_2) the_cf_parallel_2_ArrMap_vrange_vsubset_Arr:
  "\<R>\<^sub>\<circ> (\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  unfolding the_cf_parallel_2_def 
  by (rule the_cf_parallel_ArrMap_vrange_vsubset_Arr)


subsubsection\<open>
Parallel functor for a category with two parallel arrows between 
two objects is a functor
\<close>

lemma (in cf_parallel_2) cf_parallel_2_the_cf_parallel_2_is_tm_functor:
  "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' : \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  unfolding the_cf_parallel_2_def the_cat_parallel_2_def
  by (rule cf_parallel_the_cf_parallel_is_tm_functor)

lemma (in cf_parallel_2) cf_parallel_2_the_cf_parallel_2_is_tm_functor':
  assumes "\<AA>' = \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>" and "\<CC>' = \<CC>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule cf_parallel_2_the_cf_parallel_2_is_tm_functor)

lemmas [cat_parallel_cs_intros] = 
  cf_parallel_2.cf_parallel_2_the_cf_parallel_2_is_tm_functor'


subsubsection\<open>
Opposite parallel functor for a category with two parallel arrows between 
two objects
\<close>

lemma (in cf_parallel_2) cf_parallel_2_the_cf_parallel_2_op[cat_op_simps]:
  "op_cf (\<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>') = 
    \<up>\<up>\<rightarrow>\<up>\<up>\<^sub>C\<^sub>F (op_cat \<CC>) \<bb> \<aa> \<ff> \<gg> \<bb>' \<aa>' \<ff>' \<gg>'"
  using cat_parallel_2_\<gg>\<ff>
  unfolding the_cf_parallel_2_def cf_parallel_the_cf_parallel_op
  by (auto simp: VLambda_vdoubleton insert_commute)

lemmas [cat_op_simps] = cf_parallel_2.cf_parallel_2_the_cf_parallel_2_op

text\<open>\newpage\<close>

end