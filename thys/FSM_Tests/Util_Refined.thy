section \<open>Refinements for Utilities \<close>

text \<open>Introduces program refinement for @{text "Util.thy"}.\<close>

theory Util_Refined
imports Util Containers.Containers
begin

subsection \<open>New Code Equations for @{text "set_as_map"}\<close>

declare [[code drop: set_as_map]]

lemma set_as_map_refined[code] :
  fixes t :: "('a :: ccompare \<times> 'c :: ccompare) set_rbt" 
  and   xs:: "('b :: ceq \<times> 'd :: ceq) set_dlist"
  shows "set_as_map (RBT_set t) = (case ID CCOMPARE(('a \<times> 'c)) of
           Some _ \<Rightarrow> Mapping.lookup (RBT_Set2.fold (\<lambda> (x,z) m . case Mapping.lookup m (x) of
                        None \<Rightarrow> Mapping.update (x) {z} m |
                        Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)
                      t
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_map (RBT_set t)))"
    (is "?C1")
  and   "set_as_map (DList_set xs) = (case ID CEQ(('b \<times> 'd)) of
            Some _ \<Rightarrow> Mapping.lookup (DList_Set.fold (\<lambda> (x,z) m . case Mapping.lookup m (x) of
                        None \<Rightarrow> Mapping.update (x) {z} m |
                        Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)
                      xs
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_map (DList_set xs)))"
    (is "?C2")
proof -
  show ?C1
  proof (cases "ID CCOMPARE(('a \<times> 'c))")
    case None
    then show ?thesis by auto
  next
    case (Some a)
    
    let ?f' = "(\<lambda> t' . (RBT_Set2.fold (\<lambda> (x,z) m . case Mapping.lookup m x of
                                                  None \<Rightarrow> Mapping.update x {z} m |
                                                  Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) m)
                             t'
                             Mapping.empty))"
   
    let ?f = "\<lambda> xs . (fold (\<lambda> (x,z) m . case Mapping.lookup m x of
                                                  None \<Rightarrow> Mapping.update x {z} m |
                                                  Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) m)
                            xs Mapping.empty)"
    have "\<And> xs :: ('a \<times> 'c) list . Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None)"
    proof - 
      fix xs :: "('a \<times> 'c) list"
      show "Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None)"
      proof (induction xs rule: rev_induct)
        case Nil
        then show ?case 
          by (simp add: Mapping.empty.abs_eq Mapping.lookup.abs_eq)
      next
        case (snoc xz xs)
        then obtain x z where "xz = (x,z)" 
          by (metis (mono_tags, opaque_lifting) surj_pair)
    
        have *: "(?f (xs@[(x,z)])) = (case Mapping.lookup (?f xs) x of
                                    None \<Rightarrow> Mapping.update x {z} (?f xs) |
                                    Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) (?f xs))"
          by auto
    
        then show ?case proof (cases "Mapping.lookup (?f xs) x")
          case None
          then have **: "Mapping.lookup (?f (xs@[(x,z)])) = Mapping.lookup (Mapping.update x {z} (?f xs))" using * by auto
    
          have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
            by (metis lookup_update')
    
    
          have m1: "Mapping.lookup (?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some {z} else Mapping.lookup (?f xs) x')"
            unfolding ** 
            unfolding scheme by force
    
          have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = None"
          using None snoc by auto
          then have "\<not>(\<exists> z . (x,z) \<in> set xs)"
            by (metis (mono_tags, lifting) option.distinct(1))
          then have "(\<exists> z' . (x,z') \<in> set (xs@[(x,z)]))" and "{z' . (x,z') \<in> set (xs@[(x,z)])} = {z}"
            by fastforce+
          then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None)
                       = (\<lambda> x' . if x' = x then Some {z} else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x')"
            by force
          
          show ?thesis using m1 m2 snoc
            using \<open>xz = (x, z)\<close> by presburger
        next
          case (Some zs)
          then have **: "Mapping.lookup (?f (xs@[(x,z)])) = Mapping.lookup (Mapping.update x (Set.insert z zs) (?f xs))" using * by auto
          have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
            by (metis lookup_update')
    
          have m1: "Mapping.lookup (?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else Mapping.lookup (?f xs) x')"
            unfolding ** 
            unfolding scheme by force
    
    
          have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = Some zs"
            using Some snoc by auto
          then have "(\<exists> z' . (x,z') \<in> set xs)"
            unfolding case_prod_conv using  option.distinct(2) by metis
          then have "(\<exists> z' . (x,z') \<in> set (xs@[(x,z)]))" by fastforce
    
          have "{z' . (x,z') \<in> set (xs@[(x,z)])} = Set.insert z zs"
          proof -
            have "Some {z . (x,z) \<in> set xs} = Some zs"
              using \<open>(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = Some zs\<close>
              unfolding case_prod_conv using  option.distinct(2) by metis
            then have "{z . (x,z) \<in> set xs} = zs" by auto
            then show ?thesis by auto
          qed
    
          have "\<And> a  . (\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None) a
                     = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x') a" 
          proof -
            fix a show "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None) a
                       = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x') a"
            using \<open>{z' . (x,z') \<in> set (xs@[(x,z)])} = Set.insert z zs\<close> \<open>(\<exists> z' . (x,z') \<in> set (xs@[(x,z)]))\<close>
            by (cases "a = x"; auto)
          qed
  
          then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None)
                       = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x')"
            by auto
    
    
          show ?thesis using m1 m2 snoc
            using \<open>xz = (x, z)\<close> by presburger
        qed
      qed
    qed
    then have "Mapping.lookup (?f' t) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set (RBT_Set2.keys t)) then Some {z . (x,z) \<in> set (RBT_Set2.keys t)} else None)"
      unfolding fold_conv_fold_keys by metis
    moreover have "set (RBT_Set2.keys t) = (RBT_set t)" 
      using Some by (simp add: RBT_set_conv_keys) 
    ultimately have "Mapping.lookup (?f' t) = (\<lambda> x . if (\<exists> z . (x,z) \<in> (RBT_set t)) then Some {z . (x,z) \<in> (RBT_set t)} else None)"
      by force
      
  
    then show ?thesis 
      using Some unfolding set_as_map_def by simp
  qed

  show ?C2
  proof (cases "ID CEQ(('b \<times> 'd))")
    case None
    then show ?thesis by auto
  next
    case (Some a)
    
    let ?f' = "(\<lambda> t' . (DList_Set.fold (\<lambda> (x,z) m . case Mapping.lookup m x of
                                                  None \<Rightarrow> Mapping.update x {z} m |
                                                  Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) m)
                             t'
                             Mapping.empty))"
   
    let ?f = "\<lambda> xs . (fold (\<lambda> (x,z) m . case Mapping.lookup m x of
                                                  None \<Rightarrow> Mapping.update x {z} m |
                                                  Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) m)
                            xs Mapping.empty)"
    have *: "\<And> xs :: ('b \<times> 'd) list . Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None)"
    proof - 
      fix xs :: "('b \<times> 'd) list"
      show "Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None)"
      proof (induction xs rule: rev_induct)
        case Nil
        then show ?case 
          by (simp add: Mapping.empty.abs_eq Mapping.lookup.abs_eq)
      next
        case (snoc xz xs)
        then obtain x z where "xz = (x,z)" 
          by (metis (mono_tags, opaque_lifting) surj_pair)
    
        have *: "(?f (xs@[(x,z)])) = (case Mapping.lookup (?f xs) x of
                                    None \<Rightarrow> Mapping.update x {z} (?f xs) |
                                    Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) (?f xs))"
          by auto
    
        then show ?case proof (cases "Mapping.lookup (?f xs) x")
          case None
          then have **: "Mapping.lookup (?f (xs@[(x,z)])) = Mapping.lookup (Mapping.update x {z} (?f xs))" using * by auto
    
          have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
            by (metis lookup_update')
    
    
          have m1: "Mapping.lookup (?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some {z} else Mapping.lookup (?f xs) x')"
            unfolding ** 
            unfolding scheme by force
    
          have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = None"
          using None snoc by auto
          then have "\<not>(\<exists> z . (x,z) \<in> set xs)"
            by (metis (mono_tags, lifting) option.distinct(1))
          then have "(\<exists> z' . (x,z') \<in> set (xs@[(x,z)]))" and "{z' . (x,z') \<in> set (xs@[(x,z)])} = {z}"
            by fastforce+
          then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None)
                       = (\<lambda> x' . if x' = x then Some {z} else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x')"
            by force
          
          show ?thesis using m1 m2 snoc
            using \<open>xz = (x, z)\<close> by presburger
        next
          case (Some zs)
          then have **: "Mapping.lookup (?f (xs@[(x,z)])) = Mapping.lookup (Mapping.update x (Set.insert z zs) (?f xs))" using * by auto
          have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
            by (metis lookup_update')
    
          have m1: "Mapping.lookup (?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else Mapping.lookup (?f xs) x')"
            unfolding ** 
            unfolding scheme by force
    
    
          have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = Some zs"
            using Some snoc by auto
          then have "(\<exists> z' . (x,z') \<in> set xs)"
            unfolding case_prod_conv using  option.distinct(2) by metis
          then have "(\<exists> z' . (x,z') \<in> set (xs@[(x,z)]))" by fastforce
    
          have "{z' . (x,z') \<in> set (xs@[(x,z)])} = Set.insert z zs"
          proof -
            have "Some {z . (x,z) \<in> set xs} = Some zs"
              using \<open>(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = Some zs\<close>
              unfolding case_prod_conv using  option.distinct(2) by metis
            then have "{z . (x,z) \<in> set xs} = zs" by auto
            then show ?thesis by auto
          qed
    
          have "\<And> a  . (\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None) a
                     = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x') a" 
          proof -
            fix a show "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None) a
                       = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x') a"
            using \<open>{z' . (x,z') \<in> set (xs@[(x,z)])} = Set.insert z zs\<close> \<open>(\<exists> z' . (x,z') \<in> set (xs@[(x,z)]))\<close>
            by (cases "a = x"; auto)
          qed
  
          then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None)
                       = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x')"
            by auto
    
    
          show ?thesis using m1 m2 snoc
            using \<open>xz = (x, z)\<close> by presburger
        qed
      qed
    qed

    have "ID CEQ('b \<times> 'd) \<noteq> None"
      using Some by auto
    then have **: "\<And> x . x \<in> set (list_of_dlist xs) = (x \<in> (DList_set xs))" 
      using DList_Set.member.rep_eq[of xs]
      using Set_member_code(2) ceq_class.ID_ceq in_set_member by fastforce 
    
    have "Mapping.lookup (?f' xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> (DList_set xs)) then Some {z . (x,z) \<in> (DList_set xs)} else None)"
      using *[of "(list_of_dlist xs)"] 
      unfolding DList_Set.fold.rep_eq ** by assumption
    then show ?thesis unfolding set_as_map_def using Some by simp
  qed
qed



end