(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Substitutions\<close>

theory Substitutions
  imports
    Main
    "HOL-Library.FuncSet"
begin

type_synonym ('v, 'a) subst = "'v \<rightharpoonup> 'a"

definition substs :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'a) subst set" where
  "substs V H = {\<sigma>. dom \<sigma> = V \<and> ran \<sigma> \<subseteq> H}"

text \<open>Small lemmas about the set of substitutions\<close>

lemma substE [elim]: "\<lbrakk> \<sigma> \<in> substs V H; \<lbrakk> dom \<sigma> = V; ran \<sigma> \<subseteq> H \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: substs_def)

lemma substs_empty_dom [simp]: "substs {} H = {Map.empty}"
  by (auto simp add: substs_def)

lemma substs_finite: "\<lbrakk> finite V; finite H \<rbrakk> \<Longrightarrow> finite (substs V H)"
  by (simp add: finite_set_of_finite_maps substs_def)

lemma substs_nonempty:
  assumes "H \<noteq> {}"
  shows "substs V H \<noteq> {}" 
proof -
  obtain h where A1: "h \<in> H" using assms by(auto)
  obtain \<rho> where A2: "\<rho> = (\<lambda>v. if v \<in> V then Some h else None)" by(simp)
  have "\<rho> \<in> substs V H" using A1 A2 by(auto simp add: substs_def ran_def dom_def)
  then show ?thesis by(auto)
qed

lemma subst_dom: \<open>\<lbrakk> \<rho> \<in> substs V H; x \<notin> V \<rbrakk> \<Longrightarrow> x \<notin> dom \<rho>\<close>
  by(auto simp add: substs_def)

lemma subst_add:
  assumes  "x \<in> V" and "\<rho> \<in> substs (V - {x}) H" and "a \<in> H"
  shows "\<rho>(x \<mapsto> a) \<in> substs V H"
  using assms
  by(simp add: substs_def)
    (auto simp add: dom_def ran_def)

lemma subst_im:
  assumes "x \<in> V" and "\<rho> \<in> substs V H"
  shows "the (\<rho> x) \<in> H"
  using assms
  by(auto simp add: substs_def dom_def ran_def)

lemma subst_restr:
  assumes "x \<in> V" and "\<rho> \<in> substs V H"
  shows "\<rho> |` (dom \<rho> - {x}) \<in> substs (V - {x}) H"
  using assms
  by(auto simp add: substs_def ran_def dom_def restrict_map_def)


text \<open>Bijection between sets of substitutions\<close>

lemma restrict_map_dom: "\<sigma> |` dom \<sigma> = \<sigma>"
  by (metis (no_types, lifting) domIff map_le_antisym map_le_def restrict_in restrict_out)
   

lemma bij_betw_set_substs:
  assumes "x \<in> V" 
  defines "f \<equiv> \<lambda>(a, \<sigma>::'v \<rightharpoonup> 'a). \<sigma>(x \<mapsto> a)" 
      and "g \<equiv> \<lambda>\<theta>::'v \<rightharpoonup> 'a. (the (\<theta> x), \<theta>|`(dom \<theta> - {x}))"
    shows "bij_betw f
                    (H \<times> substs (V - {x}) H) 
                    (substs V H)"
proof (intro bij_betwI) 
  show "f \<in> H \<times> substs (V - {x}) H \<rightarrow> substs V H"
    using assms
    by(auto simp add: f_def subst_add)
next 
  show "g \<in> substs V H \<rightarrow> H \<times> substs (V - {x}) H" 
    using assms
    by(auto simp add: g_def subst_im subst_restr)
next 
  fix xa
  assume "xa \<in> H \<times> substs (V - {x}) H"
  then show "g (f xa) = xa" using assms
    by (smt (z3) Diff_empty Diff_insert0 Diff_insert_absorb SigmaE case_prod_conv 
            fun_upd_None_restrict fun_upd_same fun_upd_upd mk_disjoint_insert option.sel 
            restrict_map_dom subst_dom)
next
  fix y
  assume "y \<in> substs V H"
  then show "f (g y) = y" using assms 
    by(auto simp add: g_def f_def)
      (metis domIff fun_upd_restrict map_upd_triv option.exhaust_sel restrict_map_dom substE)
qed

end