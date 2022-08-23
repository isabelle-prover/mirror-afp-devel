section \<open>Refined Code Generation for Test Suites\<close>

text \<open>This theory provides alternative code equations for selected functions on test suites.
      Currently only Mapping via RBT is supported.\<close>

theory Test_Suite_Representations_Refined
imports Test_Suite_Representations "../Prefix_Tree_Refined" "../Util_Refined"
begin

declare [[code drop: Test_Suite_Representations.test_suite_from_io_tree]]

lemma test_suite_from_io_tree_refined[code] :
  fixes M :: "('a,'b :: ccompare, 'c :: ccompare) fsm"
    and m :: "(('b\<times>'c), ('b\<times>'c) prefix_tree) mapping_rbt"
  shows "test_suite_from_io_tree M q (MPT (RBT_Mapping m)) 
          = (case ID CCOMPARE(('b \<times> 'c)) of
              None \<Rightarrow> Code.abort (STR ''test_suite_from_io_tree RBT_set: ccompare = None'') (\<lambda>_ . test_suite_from_io_tree M q (MPT (RBT_Mapping m))) |
              Some _ \<Rightarrow> MPT (Mapping.tabulate (map (\<lambda>((x,y),t) . ((x,y),h_obs M q x y \<noteq> None)) (RBT_Mapping2.entries m)) (\<lambda> ((x,y),b) . case h_obs M q x y of None \<Rightarrow> Prefix_Tree.empty | Some q' \<Rightarrow> test_suite_from_io_tree M q' (case RBT_Mapping2.lookup m (x,y) of Some t' \<Rightarrow> t'))))" 
proof (cases "ID CCOMPARE(('b \<times> 'c))")
  case None
  then show ?thesis by auto
next
  case (Some a)
  then have "ID CCOMPARE(('b \<times> 'c)) \<noteq> None"
    using Some by auto

  have "distinct (map fst (RBT_Mapping2.entries m))"
    apply transfer  
    using linorder.distinct_entries[OF ID_ccompare[OF Some]]
          ord.is_rbt_rbt_sorted
          Some 
    by auto

  have "\<And> a b . (RBT_Mapping2.lookup m a = Some b) = ((a,b) \<in> List.set (RBT_Mapping2.entries m))"
    using map_of_entries[OF \<open>ID CCOMPARE(('b \<times> 'c)) \<noteq> None\<close>, of m] 
    using map_of_eq_Some_iff[OF \<open>distinct (map fst (RBT_Mapping2.entries m))\<close>] by auto

  let ?f2 = "Mapping.tabulate (map (\<lambda>((x,y),t) . ((x,y),h_obs M q x y \<noteq> None)) (RBT_Mapping2.entries m)) (\<lambda> ((x,y),b) . case h_obs M q x y of None \<Rightarrow> Prefix_Tree.empty | Some q' \<Rightarrow> test_suite_from_io_tree M q' (case RBT_Mapping2.lookup m (x,y) of Some t' \<Rightarrow> t'))"
  let ?f1 = "\<lambda> xs . \<lambda> ((x,y),b) . case map_of xs (x,y) of
    None \<Rightarrow> None |
    Some t \<Rightarrow> (case h_obs M q x y of
      None \<Rightarrow> (if b then None else Some empty) |
      Some q' \<Rightarrow> (if b then Some (test_suite_from_io_tree M q' t) else None))"

  have "Mapping.lookup ?f2 = ?f1 (RBT_Mapping2.entries m)"
  proof 
    fix k 
    show "Mapping.lookup ?f2 k = ?f1 (RBT_Mapping2.entries m) k"
    proof -
      obtain x y b where "k = ((x,y),b)"
        by (metis prod.exhaust_sel)

      show ?thesis proof (cases "RBT_Mapping2.lookup m (x,y)")
        case None

        then have "((x,y),b) \<notin> List.set (map (\<lambda>((x,y),t) . ((x,y),h_obs M q x y \<noteq> None)) (RBT_Mapping2.entries m))"
          using \<open>\<And> a b . (RBT_Mapping2.lookup m a = Some b) = ((a,b) \<in> List.set (RBT_Mapping2.entries m))\<close>[of "(x,y)"] 
          by auto
        then have "Mapping.lookup ?f2 ((x,y),b) = None"
          by (metis (mono_tags, lifting) Mapping.lookup.rep_eq map_of_map_Pair_key tabulate.rep_eq)
        moreover have "?f1 (RBT_Mapping2.entries m) ((x,y),b) = None"
          using \<open>\<And> a b . (RBT_Mapping2.lookup m a = Some b) = ((a,b) \<in> List.set (RBT_Mapping2.entries m))\<close>[of "(x,y)"] 
                None
          by (metis (no_types, lifting) map_of_SomeD not_None_eq old.prod.case option.simps(4))
        ultimately show ?thesis 
          unfolding \<open>k = ((x,y),b)\<close> by simp
      next
        case (Some t')
        then have "((x,y),t') \<in> List.set (RBT_Mapping2.entries m)"
          using \<open>\<And> a b . (RBT_Mapping2.lookup m a = Some b) = ((a,b) \<in> List.set (RBT_Mapping2.entries m))\<close> by auto

        show ?thesis proof (cases "h_obs M q x y")
          case None

          show ?thesis proof (cases b)
            case True

            then have "((x,y),b) \<notin> List.set (map (\<lambda>((x,y),t) . ((x,y),h_obs M q x y \<noteq> None)) (RBT_Mapping2.entries m))"
              using None by auto
            then have "Mapping.lookup ?f2 ((x,y),b) = None"
              by (metis (mono_tags, lifting) Mapping.lookup.rep_eq map_of_map_Pair_key tabulate.rep_eq)
            moreover have "?f1 (RBT_Mapping2.entries m) ((x,y),b) = None"
              using Some None True
              using \<open>((x, y), t') \<in> list.set (RBT_Mapping2.entries m)\<close> \<open>distinct (map fst (RBT_Mapping2.entries m))\<close> 
              by auto 
            ultimately show ?thesis 
              unfolding \<open>k = ((x,y),b)\<close> by simp
          next
            case False

            then have "((x,y),b) \<in> List.set (map (\<lambda>((x,y),t) . ((x,y),h_obs M q x y \<noteq> None)) (RBT_Mapping2.entries m))"
              using None \<open>((x,y),t') \<in> List.set (RBT_Mapping2.entries m)\<close> by force
            then have "Mapping.lookup ?f2 ((x,y),b) = Some empty"
            proof - 
              have "\<And>p ps f. (p::('b \<times> 'c) \<times> bool) \<notin> list.set ps \<or> Mapping.lookup (Mapping.tabulate ps f) p = Some (f p::(('b \<times> 'c) \<times> bool) prefix_tree)"
                by (simp add: Mapping.lookup.rep_eq map_of_map_Pair_key tabulate.rep_eq)
              then show ?thesis
                using None \<open>((x, y), b) \<in> list.set (map (\<lambda>((x, y), t). ((x, y), h_obs M q x y \<noteq> None)) (RBT_Mapping2.entries m))\<close> by auto
            qed
            moreover have "?f1 (RBT_Mapping2.entries m) ((x,y),b) = Some empty"
              using Some None False
              using \<open>((x, y), t') \<in> list.set (RBT_Mapping2.entries m)\<close>
              using \<open>distinct (map fst (RBT_Mapping2.entries m))\<close> by auto 
            ultimately show ?thesis 
              unfolding \<open>k = ((x,y),b)\<close> by simp
          qed
        next
          case (Some q')
          show ?thesis proof (cases b)
            case True
            then have "((x,y),b) \<in> List.set (map (\<lambda>((x,y),t) . ((x,y),h_obs M q x y \<noteq> None)) (RBT_Mapping2.entries m))"
              using Some \<open>((x,y),t') \<in> List.set (RBT_Mapping2.entries m)\<close> by force
            then have "Mapping.lookup ?f2 ((x,y),b) = Some (test_suite_from_io_tree M q' t')"
            proof - 
              have "\<And>p ps f. (p::('b \<times> 'c) \<times> bool) \<notin> list.set ps \<or> Mapping.lookup (Mapping.tabulate ps f) p = Some (f p::(('b \<times> 'c) \<times> bool) prefix_tree)"
                by (simp add: Mapping.lookup.rep_eq map_of_map_Pair_key tabulate.rep_eq)
              then show ?thesis
                using Some \<open>RBT_Mapping2.lookup m (x, y) = Some t'\<close> \<open>((x, y), b) \<in> list.set (map (\<lambda>((x, y), t). ((x, y), h_obs M q x y \<noteq> None)) (RBT_Mapping2.entries m))\<close> by auto
            qed
            moreover have "?f1 (RBT_Mapping2.entries m) ((x,y),b) = Some (test_suite_from_io_tree M q' t')"
              using Some \<open>RBT_Mapping2.lookup m (x, y) = Some t'\<close> True
              using \<open>((x, y), t') \<in> list.set (RBT_Mapping2.entries m)\<close>
              using \<open>distinct (map fst (RBT_Mapping2.entries m))\<close> by auto
            ultimately show ?thesis 
              unfolding \<open>k = ((x,y),b)\<close> by simp
          next
            case False
            then have "((x,y),b) \<notin> List.set (map (\<lambda>((x,y),t) . ((x,y),h_obs M q x y \<noteq> None)) (RBT_Mapping2.entries m))"
              using Some by auto
            then have "Mapping.lookup ?f2 ((x,y),b) = None"
              by (metis (mono_tags, lifting) Mapping.lookup.rep_eq map_of_map_Pair_key tabulate.rep_eq)
            moreover have "?f1 (RBT_Mapping2.entries m) ((x,y),b) = None"
              using Some \<open>RBT_Mapping2.lookup m (x, y) = Some t'\<close> False
              using \<open>((x, y), t') \<in> list.set (RBT_Mapping2.entries m)\<close> \<open>distinct (map fst (RBT_Mapping2.entries m))\<close> 
              by auto 
            ultimately show ?thesis 
              unfolding \<open>k = ((x,y),b)\<close> by simp
          qed
        qed
      qed
    qed
  qed
  
  obtain m' where "test_suite_from_io_tree M q (MPT (RBT_Mapping m)) = MPT m'"
    by (simp add: test_suite_from_io_tree_MPT)
  then have "test_suite_from_io_tree M q (MPT (RBT_Mapping m)) = PT (Mapping.lookup m')"
    using MPT_def by simp
  have "Mapping.lookup m' = (\<lambda> ((x,y),b) . case RBT_Mapping2.lookup m (x,y) of
    None \<Rightarrow> None |
    Some t \<Rightarrow> (case h_obs M q x y of
      None \<Rightarrow> (if b then None else Some empty) |
      Some q' \<Rightarrow> (if b then Some (test_suite_from_io_tree M q' t) else None)))"
  proof - 
    have "test_suite_from_io_tree M q (PT (Mapping.lookup (RBT_Mapping m))) = PT (Mapping.lookup m')"
      by (metis MPT_def \<open>test_suite_from_io_tree M q (MPT (RBT_Mapping m)) = PT (Mapping.lookup m')\<close>)
    then have "Mapping.lookup m' = (\<lambda>((b, c), ba). case Mapping.lookup (RBT_Mapping m) (b, c) of None \<Rightarrow> None | Some p \<Rightarrow> (case h_obs M q b c of None \<Rightarrow> if ba then None else Some Prefix_Tree.empty | Some a \<Rightarrow> if ba then Some (test_suite_from_io_tree M a p) else None))"
      by auto
    then show ?thesis
      by (metis (no_types) lookup_Mapping_code(2))
  qed
  then have "Mapping.lookup m' = ?f1 (RBT_Mapping2.entries m)"
    unfolding map_of_entries[OF \<open>ID CCOMPARE(('b \<times> 'c)) \<noteq> None\<close>, of m] by simp
  then have "Mapping.lookup ?f2 = Mapping.lookup m'"
    using \<open>Mapping.lookup ?f2 = ?f1 (RBT_Mapping2.entries m)\<close> by simp
  then show ?thesis 
    using Some unfolding \<open>test_suite_from_io_tree M q (MPT (RBT_Mapping m)) = MPT m'\<close>
    by (simp add: MPT_def) 
qed

end