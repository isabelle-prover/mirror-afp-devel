(*  Author: Tobias Nipkow  *)

header "Completeness of Archive Test"

theory ArchCompProps
imports TameEnumProps ArchCompAux
begin
lemma mgp_pre_iso_test: "minGraphProps g \<Longrightarrow> pre_iso_test(fgraph g)"
apply(simp add:pre_iso_test_def fgraph_def image_def)
apply(rule conjI) apply(blast dest: mgp_vertices_nonempty[symmetric])
apply(rule conjI) apply(blast intro:minGraphProps)
apply(drule minGraphProps11)
apply(simp add:normFaces_def normFace_def verticesFrom_def minVertex_def
               rotate_min_def o_def)
done

corollary iso_test_correct:
 "\<lbrakk> pre_iso_test Fs\<^isub>1; pre_iso_test Fs\<^isub>2 \<rbrakk> \<Longrightarrow>
  iso_test Fs\<^isub>1 Fs\<^isub>2 = (Fs\<^isub>1 \<simeq> Fs\<^isub>2)"
by(simp add:pre_iso_test_def iso_correct inj_on_rotate_min_iff[symmetric]
            distinct_map nof_vertices_def length_remdups_concat)

lemma trie_all_eq_set_of_trie:
  "Tries.inv t \<Longrightarrow> Tries.all P t = (\<forall>v \<in> Tries.set_of t. P v)"
apply(induct t rule:Tries.inv.induct)
apply (auto simp: Tries.set_of_def)
  apply(case_tac a)
   apply simp
  apply auto
  apply blast
 apply(erule allE)
 apply(erule impE)
  apply(rule_tac x = "[]" in exI)
  apply(rule HOL.refl)
 apply simp
apply(erule meta_allE)+
apply(erule meta_impE)
 apply assumption
apply(erule meta_impE)
 apply fast
apply(erule meta_impE)
 apply fast
apply clarsimp
apply(erule allE)
apply(erule impE)
 apply(rule_tac x = "a#aa" in exI)
apply(rule HOL.refl)
apply auto
done


lemma samet_imp_iso_seteq:
assumes pre1: "\<And>gs g. gsopt = Some gs \<Longrightarrow> g \<in> Tries.set_of gs \<Longrightarrow> pre_iso_test g"
and pre2: "\<And>g. g \<in> set arch \<Longrightarrow> pre_iso_test g"
and inv: "!!gs. gsopt = Some gs \<Longrightarrow> Tries.inv gs"
and same: "samet gsopt arch"
shows "\<exists>gs. gsopt = Some gs \<and> Tries.set_of gs =\<^isub>\<simeq> set arch"
proof -
  obtain gs where [simp]: "gsopt = Some gs" and test1: "\<And>g. g \<in> Tries.set_of gs \<Longrightarrow>
    \<exists>h \<in> set arch. iso_test g h" and test2: "\<And>g. g \<in> set arch \<Longrightarrow>
    \<exists>h \<in> Tries.set_of gs. iso_test g h"
    using same inv
    by(force simp: samet_def trie_all_eq_set_of_trie inv_of_list
      split:option.splits
      dest: in_set_lookup_of_listD in_set_lookup_set_ofD)
  have "Tries.set_of gs \<subseteq>\<^isub>\<simeq> set arch"
  proof (auto simp:qle_gr.defs)
    fix g assume g: "g \<in> Tries.set_of gs"
    obtain h where h: "h \<in> set arch" and test: "iso_test g h"
      using test1[OF g] by blast
    thus "\<exists>h\<in>set arch. g \<simeq> h"
      using h pre1[OF _ g] pre2[OF h] by (auto simp:iso_test_correct)
  qed
  moreover
  have "set arch \<subseteq>\<^isub>\<simeq> Tries.set_of gs"
  proof (auto simp:qle_gr.defs)
    fix g assume g: "g \<in> set arch"
    obtain h where h: "h \<in> Tries.set_of gs" and test: "iso_test g h"
      using test2[OF g] by blast
    thus "\<exists>h \<in> Tries.set_of gs. g \<simeq> h"
      using h pre1[OF _ h] pre2[OF g] by (auto simp:iso_test_correct)
  qed
  ultimately show ?thesis by (auto simp: qle_gr.seteq_qle_def)
qed

lemma samet_imp_iso_subseteq:
assumes pre1: "\<And>gs g. gsopt = Some gs \<Longrightarrow> g \<in> Tries.set_of gs \<Longrightarrow> pre_iso_test g"
and pre2: "\<And>g. g \<in> set arch \<Longrightarrow> pre_iso_test g"
and inv: "!!gs. gsopt = Some gs \<Longrightarrow> Tries.inv gs"
and same: "samet gsopt arch"
shows "\<exists>gs. gsopt = Some gs \<and> Tries.set_of gs \<subseteq>\<^isub>\<simeq> set arch"
using qle_gr.seteq_qle_def assms samet_imp_iso_seteq by metis

definition [code del]:
"insert_mod_trie = set_mod_maps.insert_mod Tries.update Tries.lookup iso_test hash"
definition [code del]:
"worklist_tree_coll_trie = set_modulo.worklist_tree_coll (Tries [] []) insert_mod_trie"
definition [code del]:
"worklist_tree_coll_aux_trie = set_modulo.worklist_tree_coll_aux insert_mod_trie"
definition [code del]:
"insert_mod2_trie = set_modulo.insert_mod2 insert_mod_trie"

interpretation set_mod_trie:
  set_mod_maps "Tries [] []" Tries.update Tries.lookup Tries.inv "op \<simeq>" iso_test pre_iso_test hash
where "set_modulo.worklist_tree_coll (Tries [] []) insert_mod_trie = worklist_tree_coll_trie"
and "set_modulo.worklist_tree_coll_aux insert_mod_trie = worklist_tree_coll_aux_trie"
and "set_mod_maps.insert_mod Tries.update Tries.lookup iso_test hash = insert_mod_trie"
and "set_modulo.insert_mod2 insert_mod_trie = insert_mod2_trie"
proof unfold_locales
qed (auto simp:iso_test_correct worklist_tree_coll_trie_def worklist_tree_coll_aux_trie_def insert_mod_trie_def insert_mod2_trie_def)

definition enum_filter_finals ::
  "(graph \<Rightarrow> graph list) \<Rightarrow> graph list
   \<Rightarrow> (nat,nat fgraph) tries option" where
"enum_filter_finals succs = set_mod_trie.worklist_tree_coll succs final fgraph"

definition tameEnumFilter :: "nat \<Rightarrow> (nat,nat fgraph)tries option" where
"tameEnumFilter p = enum_filter_finals (next_tame p) [Seed p]"

lemma TameEnum_tameEnumFilter:
  "tameEnumFilter p = Some t \<Longrightarrow>  Tries.set_of t  =\<^isub>\<simeq> fgraph ` TameEnum\<^bsub>p\<^esub>"
apply(auto simp: tameEnumFilter_def TameEnumP_def enum_filter_finals_def)
apply(drule set_mod_trie.worklist_tree_coll_equiv[OF _ inv_inv_next_tame])
apply (auto simp: Tries.set_of_conv inv_Seed mgp_pre_iso_test RTranCl_conv)
done

lemma tameEnumFilter_subseteq_TameEnum:
  "tameEnumFilter p = Some t \<Longrightarrow> Tries.set_of t <= fgraph ` TameEnum\<^bsub>p\<^esub>"
by(auto simp add:tameEnumFilter_def TameEnumP_def enum_filter_finals_def
     Tries.set_of_conv inv_Seed mgp_pre_iso_test RTranCl_conv
     dest!: set_mod_trie.worklist_tree_coll_subseteq[OF _ inv_inv_next_tame])


lemma inv_tries_tameEnumFilter:
  "tameEnumFilter p = Some t \<Longrightarrow> Tries.inv t"
unfolding tameEnumFilter_def enum_filter_finals_def
by(erule set_mod_trie.worklist_tree_coll_inv)

theorem combine_evals_filter:
 "\<forall>g \<in> set arch. pre_iso_test g \<Longrightarrow> samet (tameEnumFilter p) arch
  \<Longrightarrow> fgraph ` TameEnum\<^bsub>p\<^esub> \<subseteq>\<^isub>\<simeq> set arch"
apply(subgoal_tac "\<exists>t. tameEnumFilter p = Some t \<and> Tries.set_of t \<subseteq>\<^isub>\<simeq> set arch")
 apply(metis TameEnum_tameEnumFilter qle_gr.seteq_qle_def qle_gr.subseteq_qle_trans)
apply(fastsimp intro!: samet_imp_iso_subseteq
  dest: inv_tries_tameEnumFilter tameEnumFilter_subseteq_TameEnum mgp_TameEnum mgp_pre_iso_test)
done

end
