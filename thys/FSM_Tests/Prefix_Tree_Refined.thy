section \<open>Refined Code Generation for Prefix Trees\<close>

text \<open>This theory provides alternative code equations for selected functions on prefix trees.
      Currently only Mapping via RBT is supported.\<close>

theory Prefix_Tree_Refined
imports Prefix_Tree Containers.Containers
begin


declare [[code drop: Prefix_Tree.combine]]

lemma combine_refined[code] :
  fixes m1 :: "('a :: ccompare, 'a prefix_tree) mapping_rbt" 
  shows "Prefix_Tree.combine (MPT (RBT_Mapping m1)) (MPT (RBT_Mapping m2)) 
            = (case ID CCOMPARE('a) of 
                None \<Rightarrow> Code.abort (STR ''combine_MPT_RBT_Mapping: ccompare = None'') (\<lambda>_. Prefix_Tree.combine (MPT (RBT_Mapping m1)) (MPT (RBT_Mapping m2)))
                | Some _ \<Rightarrow> MPT (RBT_Mapping (RBT_Mapping2.join (\<lambda> a t1 t2 . Prefix_Tree.combine t1 t2)  m1 m2)))"
    (is "?PT1 = ?PT2")
proof (cases "ID CCOMPARE('a)")
  case None
  then show ?thesis by simp
next
  case (Some a)
  then have *: "?PT2 = MPT (RBT_Mapping (RBT_Mapping2.join (\<lambda> a t1 t2 . Prefix_Tree.combine t1 t2)  m1 m2))"
    by auto

  have "ID CCOMPARE('a) \<noteq> None"
    using Some by auto

  have "Mapping.lookup (Mapping.combine Prefix_Tree.combine (RBT_Mapping m1) (RBT_Mapping m2)) = Mapping.lookup (RBT_Mapping (RBT_Mapping2.join (\<lambda> a b c . Prefix_Tree.combine b c) m1 m2))"
  proof 
    fix x

    show "Mapping.lookup (Mapping.combine Prefix_Tree.combine (RBT_Mapping m1) (RBT_Mapping m2)) x =
         Mapping.lookup (RBT_Mapping (RBT_Mapping2.join (\<lambda>a. Prefix_Tree.combine) m1 m2)) x"
    (is "?M1 = ?M2")
    proof (cases "RBT_Mapping2.lookup m1 x")
      case None
      show ?thesis proof (cases "RBT_Mapping2.lookup m2 x")
        case None

        have "?M1 = None"
          using \<open>RBT_Mapping2.lookup m1 x = None\<close> None
          by (metis combine_options_simps(1) lookup_Mapping_code(2) lookup_combine)
        moreover have "?M2 = None"
          using \<open>RBT_Mapping2.lookup m1 x = None\<close> None
          by (simp add: Mapping.lookup.abs_eq \<open>ID ccompare \<noteq> None\<close> lookup_join) 
        ultimately show ?thesis
          by simp
      next
        case (Some a)
        have "?M1 = Some a"
          using \<open>RBT_Mapping2.lookup m1 x = None\<close> Some
          by (metis combine_options_simps(1) lookup_Mapping_code(2) lookup_combine)
        moreover have "?M2 = Some a"
          using \<open>RBT_Mapping2.lookup m1 x = None\<close> Some
          by (simp add: Mapping.lookup.abs_eq \<open>ID ccompare \<noteq> None\<close> lookup_join) 
        ultimately show ?thesis
          by simp
      qed
    next
      case (Some a)
      show ?thesis proof (cases "RBT_Mapping2.lookup m2 x")
        case None

        have "?M1 = Some a"
          using None Some
          by (metis combine_options_simps(2) lookup_Mapping_code(2) lookup_combine) 
        moreover have "?M2 = Some a"
          using None Some 
          by (simp add: Mapping.lookup.abs_eq \<open>ID ccompare \<noteq> None\<close> lookup_join) 
        ultimately show ?thesis
          by simp
      next
        case (Some b)

        have "?M1 = Some (Prefix_Tree.combine a b)"
          using \<open>RBT_Mapping2.lookup m1 x = Some a\<close> Some
          by (metis combine_options_simps(3) lookup_Mapping_code(2) lookup_combine) 
        moreover have "?M2 = Some (Prefix_Tree.combine a b)"
          using \<open>RBT_Mapping2.lookup m1 x = Some a\<close> Some 
          by (simp add: Mapping.lookup.abs_eq \<open>ID ccompare \<noteq> None\<close> lookup_join) 
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
  then have "(Mapping.combine Prefix_Tree.combine (RBT_Mapping m1) (RBT_Mapping m2)) = (RBT_Mapping (RBT_Mapping2.join (\<lambda> a b c . Prefix_Tree.combine b c) m1 m2))"
    by (metis Mapping.lookup.rep_eq rep_inverse)
  then show ?thesis
    unfolding * unfolding combine_MPT by simp
qed

declare [[code drop: Prefix_Tree.is_leaf]]

lemma is_leaf_refined[code] :
  fixes m :: "('a :: ccompare, 'a prefix_tree) mapping_rbt" 
  shows "Prefix_Tree.is_leaf (MPT (RBT_Mapping m))
            = (case ID CCOMPARE('a) of 
                None \<Rightarrow> Code.abort (STR ''is_leaf_MPT_RBT_Mapping: ccompare = None'') (\<lambda>_. Prefix_Tree.is_leaf (MPT (RBT_Mapping m)))
                | Some _ \<Rightarrow> RBT_Mapping2.is_empty m)"
    (is "?PT1 = ?PT2")
proof (cases "ID CCOMPARE('a)")
  case None
  then show ?thesis by simp
next
  case (Some a)
  then have *: "?PT2 = RBT_Mapping2.is_empty m"
    by auto
  show ?thesis
    unfolding *
    by (metis (no_types, opaque_lifting) MPT_def Mapping.is_empty_empty RBT_Mapping2.is_empty_empty Some is_leaf.elims(2) is_leaf_MPT lookup_Mapping_code(2) lookup_empty_empty mapping_empty_code(4) mapping_empty_def option.distinct(1) prefix_tree.inject) 
qed


end