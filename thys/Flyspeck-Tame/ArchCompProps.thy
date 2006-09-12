(*  ID:         $Id: ArchCompProps.thy,v 1.2 2006-09-12 11:21:48 makarius Exp $
    Author:     Tobias Nipkow
*)

header "Completeness of Archive Test"

theory ArchCompProps
imports TameEnumProps ArchComp
begin


corollary iso_test_correct:
 "\<lbrakk> pre_iso_test Fs\<^isub>1; pre_iso_test Fs\<^isub>2 \<rbrakk> \<Longrightarrow>
  iso_test (nof_vertices Fs\<^isub>1,Fs\<^isub>1) (nof_vertices Fs\<^isub>2,Fs\<^isub>2) = (Fs\<^isub>1 \<simeq> Fs\<^isub>2)"
by(simp add:pre_iso_test_def iso_correct inj_on_rotate_min_iff[symmetric]
            distinct_map nof_vertices_def length_remdups_concat)


lemma same_imp_iso_subset:
assumes pre1: "\<And>gs g. gsopt = Some gs \<Longrightarrow> g \<in> set gs \<Longrightarrow> pre_iso_test g"
and pre2: "\<And>g. g \<in> set arch \<Longrightarrow> pre_iso_test g"
and same: "same gsopt arch"
shows "\<exists>gs. gsopt = Some gs \<and> set gs \<subseteq>\<^isub>\<simeq> set arch"
proof -
  obtain gs where [simp]: "gsopt = Some gs" and test: "\<And>g. g \<in> set gs \<Longrightarrow>
    \<exists>h \<in> set arch. iso_test (nof_vertices g,g) (nof_vertices h,h)"
    using same by(force simp:same_def split:option.splits
                        dest: in_set_lookup_trie_of_listD)
  have "set gs \<subseteq>\<^isub>\<simeq> set arch"
  proof (auto simp:iso_subseteq_def iso_in_def)
    fix g assume g: "g\<in>set gs"
    obtain h where h: "h \<in> set arch" and
      test: "iso_test (nof_vertices g,g) (nof_vertices h,h)"
      using test[OF g] by blast
    thus "\<exists>h\<in>set arch. g \<simeq> h"
      using h pre1[OF _ g] pre2[OF h] by (auto simp:iso_test_correct)
  qed
  thus ?thesis by auto
qed

lemma enum_finals_tree:
 "\<forall>g. final g \<longrightarrow> next g = [] \<Longrightarrow> enum_finals next n todo Fs\<^isub>0 = Some Fs \<Longrightarrow>
  set Fs = set Fs\<^isub>0 \<union> fgraph ` {h. \<exists>g \<in> set todo. g [next]\<rightarrow>* h \<and> final h}"
apply(induct n arbitrary: todo Fs\<^isub>0) apply simp
apply (clarsimp simp:image_def neq_Nil_conv split:split_if_asm)
 apply(rule equalityI)
  apply (blast intro:RTranCl.refl)
 apply(rule)
 apply simp
 apply(erule disjE) apply blast
 apply (erule exE conjE)+
 apply(erule disjE) apply (fastsimp elim:RTranCl_elim)
 apply(blast)
apply(rule equalityI)
 apply (blast intro:succs)
apply(rule)
apply simp
apply(erule disjE) apply blast
apply (erule exE conjE)+
apply(erule disjE) apply (fastsimp elim:RTranCl_elim)
apply(blast)
done

lemma next_tame_of_final: "\<forall>g. final g \<longrightarrow> next_tame\<^bsub>p\<^esub> g = []"
by(auto simp: next_tame_def next_tame1_def next_tame0_def
              nonFinals_def filter_empty_conv finalGraph_def)

lemma tameEnum_TameEnum: "tameEnum p n = Some Fs \<Longrightarrow> set Fs = fgraph ` TameEnum\<^bsub>p\<^esub>"
by(simp add: tameEnum_def TameEnumP_def enum_finals_tree[OF next_tame_of_final])

lemma mgp_pre_iso_test: "minGraphProps g \<Longrightarrow> pre_iso_test(fgraph g)"
apply(simp add:pre_iso_test_def fgraph_def image_def)
apply(rule conjI) apply(blast dest: mgp_vertices_nonempty[symmetric])
apply(rule conjI) apply(blast intro:minGraphProps)
apply(drule minGraphProps11)
apply(simp add:normFaces_def normFace_def verticesFrom_def minVertex_def
               rotate_min_def map_compose[symmetric] o_def)
done

theorem combine_evals:
 "\<forall>g \<in> set arch. pre_iso_test g \<Longrightarrow> same (tameEnum p n) arch
  \<Longrightarrow> fgraph ` TameEnum\<^bsub>p\<^esub> \<subseteq>\<^isub>\<simeq> set arch"
apply(subgoal_tac "\<exists>gs. tameEnum p n = Some gs \<and> set gs \<subseteq>\<^isub>\<simeq> set arch")
 apply(fastsimp simp: image_def dest: tameEnum_TameEnum)
apply(fastsimp intro!: same_imp_iso_subset simp: image_def
  dest: tameEnum_TameEnum mgp_TameEnum mgp_pre_iso_test)
done

end
