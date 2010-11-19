(*  Author:     Tobias Nipkow
*)

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


lemma same_imp_iso_subseteq:
assumes pre1: "\<And>gs g. gsopt = Some gs \<Longrightarrow> g \<in> set gs \<Longrightarrow> pre_iso_test g"
and pre2: "\<And>g. g \<in> set arch \<Longrightarrow> pre_iso_test g"
and same: "same gsopt arch"
shows "\<exists>gs. gsopt = Some gs \<and> set gs \<subseteq>\<^isub>\<simeq> set arch"
proof -
  obtain gs where [simp]: "gsopt = Some gs" and test: "\<And>g. g \<in> set gs \<Longrightarrow>
    \<exists>h \<in> set arch. iso_test g h"
    using same by(force simp:same_def split:option.splits
                        dest: in_set_lookup_trie_of_listD)
  have "set gs \<subseteq>\<^isub>\<simeq> set arch"
  proof (auto simp:iso_subseteq_def iso_in_def)
    fix g assume g: "g\<in>set gs"
    obtain h where h: "h \<in> set arch" and test: "iso_test g h"
      using test[OF g] by blast
    thus "\<exists>h\<in>set arch. g \<simeq> h"
      using h pre1[OF _ g] pre2[OF h] by (auto simp:iso_test_correct)
  qed
  thus ?thesis by auto
qed

lemma foldl_fgraph:
  "foldl (%fins g. if final g then fgraph g # fins else fins) fgs gs =
  rev(map fgraph (filter final gs)) @ fgs"
by (induct gs arbitrary: fgs) simp_all

lemma RTranCl_conv:
  "g [next]\<rightarrow>* h \<longleftrightarrow> (g,h) : ((succs_rel next)^*)" (is "?L = ?R")
proof-
  have "?L \<Longrightarrow> ?R"
    apply(erule RTranCl_induct)
    apply blast
    apply (auto elim: rtrancl_into_rtrancl)
    done
  moreover
  have "?R \<Longrightarrow> ?L"
    apply(erule converse_rtrancl_induct)
    apply(rule RTranCl.refl)
    apply (auto elim: RTranCl.succs)
    done
  ultimately show ?thesis by blast
qed

lemma enum_finals_tree:
 "enum_finals next todo Fs\<^isub>0 = Some Fs \<Longrightarrow>
  set Fs = set Fs\<^isub>0 \<union> fgraph ` {h. (\<exists>g \<in> set todo. g [next]\<rightarrow>* h) \<and> final h}"
apply(simp add: enum_finals_def)
apply(drule worklist)
apply (clarsimp simp add: foldl_fgraph RTranCl_conv)
apply blast
done


lemma enum_filter_finals1:
  "enum_filter_finals next n todo Fs\<^isub>0 t = Some Fs \<Longrightarrow>
  set Fs\<^isub>0 \<subseteq> set Fs"
apply(induct n arbitrary: todo Fs\<^isub>0 t) apply simp
apply (force simp: neq_Nil_conv split:split_if_asm)
done

definition contents :: "('a,'b)trie \<Rightarrow> 'b set" where
"contents t = Union {gs. \<exists>a. gs = set(lookup_trie t a)}"

lemma contents_empty[simp]: "contents (Trie [] []) = {}"
by(simp add: contents_def)

lemma contents_insert_trie[simp]:
  "contents (insert_trie t a x) = insert x (contents t)"
by(auto simp: contents_def insert_trie_conv lookup_update_trie)

lemma enum_filter_finals2:
assumes "\<forall>g. final g \<longrightarrow> next g = []" and "invariant inv next"
shows "\<forall>g \<in> set todo. inv g \<Longrightarrow> \<forall>g \<in> contents t. pre_iso_test g \<Longrightarrow>
  enum_filter_finals next n todo Fs\<^isub>0 t = Some Fs \<Longrightarrow>
  fgraph ` {h. \<exists>g \<in> set todo. g [next]\<rightarrow>* h \<and> final h} \<subseteq>\<^isub>\<simeq> set Fs \<union> contents t"
proof(induct n arbitrary: todo Fs\<^isub>0 t)
  case 0 thus ?case by simp
next
  case (Suc n)
  show ?case
  proof(cases todo)
    case Nil thus ?thesis by simp
  next
    case (Cons g todo')
    hence inv_todo': "\<forall>g\<in>set todo'. inv g" using Suc.prems(1) by auto
    show ?thesis (is "?L \<subseteq>\<^isub>\<simeq> ?R")
    proof(rule iso_subseteqI2)
      fix f assume "f : ?L"
      then obtain h h' where
        hh': "h\<in>set todo" "h[next]\<rightarrow>* h'" "final h'" "f = fgraph h'"
        by auto
      show "EX f' : ?R. f \<simeq> f'"
      proof (cases "final g")
        case True
        have 2: "h = g \<or> (h\<in>set todo')" using `h\<in>set todo` Cons by simp
        let ?fg = "fgraph g" let ?ags = "lookup_trie t (hash ?fg)"
        let ?t' = "insert_trie t (hash ?fg) ?fg"
        show ?thesis
        proof (cases "EX ag : set ?ags. iso_test ?fg ag")
          case True
          hence p: "enum_filter_finals next n todo' Fs\<^isub>0 t = Some Fs"
            using Suc.prems Cons `final g` by simp
          from 2 show ?thesis
          proof
            assume "h=g"
            hence "h' = h"
              using `final g` assms RTranCl_elim[OF `h [next]\<rightarrow>* h'`] by auto
            from True obtain ag where ag: "ag\<in>set (lookup_trie t (hash ?fg))"
              and iso: "iso_test ?fg ag" by auto
            from ag have "ag : contents t"
              by(fastsimp simp: contents_def)
            with `h=g` `h' = h` have "ag : ?R" by auto
            have "f \<simeq> ag"
              by (metis Suc(2) Suc(3) `ag \<in> contents t` `h = g` `h' = h` hh'(1) hh'(4) inv_mgp iso iso_test_correct mgp_pre_iso_test)
            with `ag : ?R` show ?thesis by blast
          next
            assume "h \<in> set todo'"
            thus ?thesis using hh'
              by(rule_tac iso_subseteqD2[OF Suc(1)[OF inv_todo' Suc.prems(2) p]])
                (auto simp: image_def)
          qed
        next
          case False
          hence p: "enum_filter_finals next n todo' (fgraph g # Fs\<^isub>0) ?t' =
            Some Fs"
            using Suc.prems Cons `final g` by simp
          have "?fg : set Fs" using enum_filter_finals1[OF p] by auto
          from 2 show ?thesis
          proof
            assume "h=g"
            hence "h' = h"
              using `final g` assms RTranCl_elim[OF `h [next]\<rightarrow>* h'`] by auto
            with `h=g` `?fg : set Fs` `f = fgraph h'`
            have "?fg : ?R & f \<simeq> ?fg" by auto
            thus ?thesis by blast
          next
            assume "h\<in>set todo'"
            hence f: "f : fgraph ` {h. \<exists>g\<in>set todo'. g [next]\<rightarrow>* h \<and> final h}"
              using `h[next]\<rightarrow>* h'` `final h'` `f = fgraph h'` by auto
            have "ALL g:contents(insert_trie t (hash ?fg) ?fg). pre_iso_test g"
              using Cons Suc.prems(1,2)
              by(simp add: ball_Un inv_mgp[THEN mgp_pre_iso_test])
            from iso_subseteqD2[OF Suc(1)[OF inv_todo' this p] f]
            obtain f' where "f \<simeq> f'" and
              "f' \<in> set Fs \<union> contents (insert_trie t (hash ?fg) ?fg)"
              by auto
            hence "f' : ?R" using `?fg : set Fs` by auto
            with `f \<simeq> f'` show ?thesis by blast
          qed
        qed
      next
        case False
        hence p: "enum_filter_finals next n (next g @ todo') Fs\<^isub>0 t = Some Fs"
          using Suc.prems Cons `~final g` by simp
        have inv: "\<forall>g\<in>set (next g @ todo'). inv g"
          using inv_todo' assms(2) Suc(2) Cons by (auto simp: invariant_def)
        show ?thesis
          apply(rule iso_subseteqD2[OF Suc(1)[OF inv Suc.prems(2) p]])
          using `h\<in>set todo` Cons `h[next]\<rightarrow>* h'` `final h'` `f = fgraph h'` False
          apply (auto simp: image_def)
          by (metis RTranCl_elim Un_commute mem_def sup1I2)
      qed
    qed
  qed
qed

lemma enum_filter_finals_subseteq:
  "enum_filter_finals next n todo Fs\<^isub>0 t = Some Fs \<Longrightarrow>
  set Fs \<subseteq> set Fs\<^isub>0 \<union> fgraph ` {h. \<exists>g \<in> set todo. g [next]\<rightarrow>* h \<and> final h}"
apply(induct n arbitrary: todo Fs\<^isub>0 t) apply simp
apply (clarsimp simp: neq_Nil_conv split: split_if_asm)
  apply blast
 apply(erule meta_allE)+
 apply(erule meta_impE)
  apply assumption
 apply (fastsimp intro!:RTranCl.refl)
apply (force intro:RTranCl.succs)
done

lemma next_tame_of_final: "\<forall>g. final g \<longrightarrow> next_tame\<^bsub>p\<^esub> g = []"
by(auto simp: next_tame_def next_tame0_def
              nonFinals_def filter_empty_conv finalGraph_def)

lemma tameEnum_TameEnum:
  "tameEnum p = Some Fs \<Longrightarrow> set Fs = fgraph ` TameEnum\<^bsub>p\<^esub>"
by(simp add:tameEnum_def TameEnumP_def enum_finals_tree)

lemma TameEnum_iso_subseteq_tameEnumFilter:
  "tameEnumFilter p n = Some Fs \<Longrightarrow> fgraph ` TameEnum\<^bsub>p\<^esub> \<subseteq>\<^isub>\<simeq> set Fs"
apply(auto simp: tameEnumFilter_def TameEnumP_def)
using enum_filter_finals2[OF next_tame_of_final inv_inv_next_tame, of "[Seed\<^bsub>p\<^esub>]" "Trie [] []"]
apply (auto simp: inv_Seed)
done

lemma tameEnumFilter_subseteq_TameEnum:
  "tameEnumFilter p n = Some Fs \<Longrightarrow> set Fs <= fgraph ` TameEnum\<^bsub>p\<^esub>"
by(auto simp add:tameEnumFilter_def TameEnumP_def
     dest!: enum_filter_finals_subseteq)

theorem combine_evals:
 "\<forall>g \<in> set arch. pre_iso_test g \<Longrightarrow> same (tameEnum p) arch
  \<Longrightarrow> fgraph ` TameEnum\<^bsub>p\<^esub> \<subseteq>\<^isub>\<simeq> set arch"
apply(subgoal_tac "\<exists>gs. tameEnum p = Some gs \<and> set gs \<subseteq>\<^isub>\<simeq> set arch")
 apply(fastsimp simp: image_def dest: tameEnum_TameEnum)
apply(fastsimp intro!: same_imp_iso_subseteq
  dest: tameEnum_TameEnum mgp_TameEnum mgp_pre_iso_test)
done

theorem combine_evals_filter:
 "\<forall>g \<in> set arch. pre_iso_test g \<Longrightarrow> same (tameEnumFilter p n) arch
  \<Longrightarrow> fgraph ` TameEnum\<^bsub>p\<^esub> \<subseteq>\<^isub>\<simeq> set arch"
apply(subgoal_tac "\<exists>gs. tameEnumFilter p n = Some gs \<and> set gs \<subseteq>\<^isub>\<simeq> set arch")
 apply(blast dest: TameEnum_iso_subseteq_tameEnumFilter intro: iso_fgraph_subseteq_trans)
apply(fastsimp intro!: same_imp_iso_subseteq
  dest: TameEnum_iso_subseteq_tameEnumFilter tameEnumFilter_subseteq_TameEnum mgp_TameEnum mgp_pre_iso_test)
done

end
