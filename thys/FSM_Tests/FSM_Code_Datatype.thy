section \<open>Data Refinement on FSM Representations\<close>

text \<open>This section introduces a refinement of the type of finite state machines for 
      code generation, maintaining mappings to access the transition relation to
      avoid repeated computations.\<close>

theory FSM_Code_Datatype
imports FSM "HOL-Library.Mapping" Containers.Containers 
begin

subsection \<open>Mappings and Function @{text "h"}\<close>

fun list_as_mapping :: "('a \<times> 'c) list \<Rightarrow> ('a,'c set) mapping" where
  "list_as_mapping xs = (foldr (\<lambda> (x,z) m . case Mapping.lookup m x of
                                                None \<Rightarrow> Mapping.update x {z} m |
                                                Some zs \<Rightarrow> Mapping.update x (insert z zs) m)
                                xs
                                Mapping.empty)"


lemma list_as_mapping_lookup: 
  fixes xs :: "('a \<times> 'c) list"
  shows "(Mapping.lookup (list_as_mapping xs)) = (\<lambda> x . if (\<exists> z . (x,z) \<in> (set xs)) then Some {z . (x,z) \<in> (set xs)} else None)"
proof - 
  let ?P = "\<lambda>m :: ('a,'c set) mapping . (Mapping.lookup m) = (\<lambda> x . if (\<exists> z . (x,z) \<in> (set xs)) then Some {z . (x,z) \<in> (set xs)} else None)"

  have "?P (list_as_mapping xs)"
  proof (induction xs)
    case Nil
    then show ?case
      using Mapping.lookup_empty by fastforce
  next
    case (Cons xz xs)
    then obtain x z where "xz = (x,z)" 
      by (metis (mono_tags, opaque_lifting) surj_pair)

    have *: "(list_as_mapping ((x,z)#xs)) = (case Mapping.lookup (list_as_mapping xs) x of
                                None \<Rightarrow> Mapping.update x {z} (list_as_mapping xs) |
                                Some zs \<Rightarrow> Mapping.update x (insert z zs) (list_as_mapping xs))"
      unfolding list_as_mapping.simps
      by auto

    show ?case proof (cases "Mapping.lookup (list_as_mapping xs) x")
      case None
      then have **: "Mapping.lookup (list_as_mapping ((x,z)#xs)) = (Mapping.lookup (Mapping.update x {z} (list_as_mapping xs)))" 
        using * by auto
      then have m1: "Mapping.lookup (list_as_mapping ((x,z)#xs)) = (\<lambda> x' . if x' = x then Some {z} else Mapping.lookup (list_as_mapping xs) x')"
        by (metis (lifting) lookup_update') 

      have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = None"
        using None Cons by auto
      then have "\<not>(\<exists> z . (x,z) \<in> set xs)"
        by (metis (mono_tags, lifting) option.distinct(1))
      then have "(\<exists> z . (x,z) \<in> set ((x,z)#xs))" and "{z' . (x,z') \<in> set ((x,z)#xs)} = {z}"
        by auto
      then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set ((x,z)#xs)) 
                                then Some {z' . (x',z') \<in> set ((x,z)#xs)} 
                                else None)
                   = (\<lambda> x' . if x' = x 
                                then Some {z} else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) 
                                                            then Some {z . (x,z) \<in> set xs} 
                                                            else None) x')"
        by force

      show ?thesis using m1 m2 Cons
        using \<open>xz = (x, z)\<close> by presburger
    next
      case (Some zs)
      then have **: "Mapping.lookup (list_as_mapping ((x,z)#xs)) = (Mapping.lookup (Mapping.update x (insert z zs) (list_as_mapping xs)))" 
        using * by auto
       then have m1: "Mapping.lookup (list_as_mapping ((x,z)#xs)) = (\<lambda> x' . if x' = x then Some (insert z zs) else Mapping.lookup (list_as_mapping xs) x')"
        by (metis (lifting) lookup_update') 

      have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = Some zs"
        using Some Cons by auto
      then have "(\<exists> z . (x,z) \<in> set xs)"
        unfolding case_prod_conv using  option.distinct(2) by metis
      then have "(\<exists> z . (x,z) \<in> set ((x,z)#xs))" by simp

      have "{z' . (x,z') \<in> set ((x,z)#xs)} = insert z zs"
      proof -
        have "Some {z . (x,z) \<in> set xs} = Some zs"
          using \<open>(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x 
                  = Some zs\<close>
          unfolding case_prod_conv using  option.distinct(2) by metis
        then have "{z . (x,z) \<in> set xs} = zs" by auto
        then show ?thesis by auto
      qed

      have "\<And> a  . (\<lambda> x' . if (\<exists> z' . (x',z') \<in> set ((x,z)#xs)) 
                              then Some {z' . (x',z') \<in> set ((x,z)#xs)} else None) a
                   = (\<lambda> x' . if x' = x 
                              then Some (insert z zs) 
                              else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) 
                                            then Some {z . (x,z) \<in> set xs} else None) x') a" 
      proof -
        fix a show "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set ((x,z)#xs)) 
                              then Some {z' . (x',z') \<in> set ((x,z)#xs)} else None) a
                   = (\<lambda> x' . if x' = x 
                              then Some (insert z zs) 
                              else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) 
                                            then Some {z . (x,z) \<in> set xs} else None) x') a"
        using \<open>{z' . (x,z') \<in> set ((x,z)#xs)} = insert z zs\<close> \<open>(\<exists> z . (x,z) \<in> set ((x,z)#xs))\<close>
        by (cases "a = x"; auto)
      qed

      then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set ((x,z)#xs)) 
                                then Some {z' . (x',z') \<in> set ((x,z)#xs)} else None)
                   = (\<lambda> x' . if x' = x 
                                then Some (insert z zs) 
                                else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) 
                                              then Some {z . (x,z) \<in> set xs} else None) x')"
        by auto


      show ?thesis using m1 m2 Cons
        using \<open>xz = (x, z)\<close> by presburger
    qed
  qed
  then show ?thesis .
qed


lemma list_as_mapping_lookup_transitions : 
  "(case (Mapping.lookup (list_as_mapping (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) ts)) (q,x)) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}) = { (y,q') . (q,x,y,q') \<in> set ts}"
(is "?S1 = ?S2")
proof (cases "\<exists>z. ((q, x), z) \<in> set (map (\<lambda>(q, x, y, q'). ((q, x), y, q')) ts)")
  case True
  then have "?S1 = {z. ((q, x), z) \<in> set (map (\<lambda>(q, x, y, q'). ((q, x), y, q')) ts)}"
    unfolding list_as_mapping_lookup by auto
  also have "\<dots> = ?S2"
    by (induction ts; auto)
  finally show ?thesis .
next
  case False
  then have "?S1 = {}"
    unfolding list_as_mapping_lookup by auto
  also have "\<dots> = ?S2"
    using False by (induction ts; auto) 
  finally show ?thesis .
qed

lemma list_as_mapping_Nil :
  "list_as_mapping [] = Mapping.empty"
  by auto


definition set_as_mapping :: "('a \<times> 'c) set \<Rightarrow> ('a,'c set) mapping" where
  "set_as_mapping s = (THE m . Mapping.lookup m = (set_as_map s))"

lemma set_as_mapping_ob :
  obtains m where "set_as_mapping s = m" and "Mapping.lookup m = set_as_map s"
proof -
  obtain m where *:"Mapping.lookup m = set_as_map s"
    using Mapping.lookup.abs_eq by auto
  moreover have "(THE x. Mapping.lookup x = set_as_map s) = m"
    using the_equality[of "\<lambda>m . Mapping.lookup m = set_as_map s", OF *] 
    unfolding *[symmetric]
    by (simp add: mapping_eqI) 
  ultimately show ?thesis 
    using that[of m] unfolding set_as_mapping_def by blast
qed

lemma set_as_mapping_refined[code] :
  fixes t :: "('a :: ccompare \<times> 'c :: ccompare) set_rbt" 
  and   xs:: "('b :: ceq \<times> 'd :: ceq) set_dlist"
  shows "set_as_mapping (RBT_set t) = (case ID CCOMPARE(('a \<times> 'c)) of
           Some _ \<Rightarrow> (RBT_Set2.fold (\<lambda> (x,z) m . case Mapping.lookup m (x) of
                        None \<Rightarrow> Mapping.update (x) {z} m |
                        Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)
                      t
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_mapping (RBT_set t)))"
    (is "set_as_mapping (RBT_set t) = ?C1 (RBT_set t)")
  and   "set_as_mapping (DList_set xs) = (case ID CEQ(('b \<times> 'd)) of
            Some _ \<Rightarrow> (DList_Set.fold (\<lambda> (x,z) m . case Mapping.lookup m (x) of
                        None \<Rightarrow> Mapping.update (x) {z} m |
                        Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)
                      xs
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_mapping (DList_set xs)))"
    (is "set_as_mapping (DList_set xs) = ?C2 (DList_set xs)")
proof -
  show "set_as_mapping (RBT_set t) = ?C1 (RBT_set t)"
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
    then have "Mapping.lookup (?f' t) = set_as_map (RBT_set t)"
      unfolding set_as_map_def by blast
    then have *:"Mapping.lookup (?C1 (RBT_set t)) = set_as_map (RBT_set t)"
      unfolding Some by force
    
    have "\<And> t' . Mapping.lookup (?C1 (RBT_set t)) = Mapping.lookup (?C1 t') \<Longrightarrow> (?C1 (RBT_set t)) = (?C1 t')"
      by (simp add: Some)
    then have **: "(\<And>x. Mapping.lookup x = set_as_map (RBT_set t) \<Longrightarrow> x = (?C1 (RBT_set t)))"
      by (simp add: "*" mapping_eqI)


    show ?thesis
      using the_equality[of "\<lambda> m . Mapping.lookup m = (set_as_map (RBT_set t))", OF * **]
      unfolding set_as_mapping_def by blast
  qed

  show "set_as_mapping (DList_set xs) = ?C2 (DList_set xs)"
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
    then have "Mapping.lookup (?f' xs) = set_as_map (DList_set xs)"
      unfolding set_as_map_def by blast
    then have *:"Mapping.lookup (?C2 (DList_set xs)) = set_as_map (DList_set xs)"
      unfolding Some by force
    
    have "\<And> t' . Mapping.lookup (?C2 (DList_set xs)) = Mapping.lookup (?C2 t') \<Longrightarrow> (?C2 (DList_set xs)) = (?C2 t')"
      by (simp add: Some)
    then have **: "(\<And>x. Mapping.lookup x = set_as_map (DList_set xs) \<Longrightarrow> x = (?C2 (DList_set xs)))"
      by (simp add: "*" mapping_eqI)


    show ?thesis
      using the_equality[of "\<lambda> m . Mapping.lookup m = (set_as_map (DList_set xs))", OF * **]
      unfolding set_as_mapping_def by blast
  qed
qed


fun h_obs_impl_from_h :: "(('state \<times> 'input), ('output \<times> 'state) set) mapping \<Rightarrow> ('state \<times> 'input, ('output, 'state) mapping) mapping" where
  "h_obs_impl_from_h h' = Mapping.map_values
                            (\<lambda> _ yqs . let m' = set_as_mapping yqs;
                                           m'' = Mapping.filter (\<lambda> y qs . card qs = 1) m';
                                           m''' = Mapping.map_values (\<lambda> _ qs . the_elem qs) m''
                                        in m''')
                            h'"

fun h_obs_impl :: "(('state \<times> 'input), ('output \<times> 'state) set) mapping \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> 'output \<Rightarrow> 'state option" where
  "h_obs_impl h' q x y  = (let 
      tgts = snd ` Set.filter (\<lambda>(y',q') . y' = y) (case (Mapping.lookup h' (q,x)) of Some ts \<Rightarrow> ts | None \<Rightarrow> {})
    in if card tgts = 1
      then Some (the_elem tgts)
      else None)"

abbreviation(input) "h_obs_lookup \<equiv> (\<lambda> h' q x y . (case Mapping.lookup h' (q,x) of Some m \<Rightarrow> Mapping.lookup m y | None \<Rightarrow> None))" 

lemma h_obs_impl_from_h_invar : "h_obs_impl h' q x y = h_obs_lookup (h_obs_impl_from_h h') q x y" 
  (is "?A q x y = ?B q x y")
proof (cases "Mapping.lookup h' (q,x)")
  case None

  then have "Mapping.lookup (h_obs_impl_from_h h') (q,x) = None"
    unfolding h_obs_impl_from_h.simps Mapping.lookup_map_values
    by auto
  then have "?B q x y = None"
    by auto
  moreover have "?A q x y = None"
    unfolding h_obs_impl.simps Let_def None
    by (simp add: Set.filter_def) 
  ultimately show ?thesis 
    by presburger
next
  case (Some yqs)

  define m' where "m' = set_as_mapping yqs"
  define m'' where "m'' = Mapping.filter (\<lambda> y qs . card qs = 1) m'"
  define m''' where "m''' = Mapping.map_values (\<lambda> _ qs . the_elem qs) m''"

  have "Mapping.lookup (h_obs_impl_from_h h') (q,x) = Some m'''"
    unfolding m'''_def m''_def m'_def h_obs_impl_from_h.simps Let_def 
    unfolding Mapping.lookup_map_values Some
    by auto

  have "Mapping.lookup m' = set_as_map yqs"
    using set_as_mapping_ob m'_def
    by auto 

  have *:"(snd ` Set.filter (\<lambda>(y', q'). y' = y) (case Some yqs of None \<Rightarrow> {} | Some ts \<Rightarrow> ts)) = {z. (y, z) \<in> yqs}"
    by force

  have "\<And> qs . Mapping.lookup m'' y = Some qs \<longleftrightarrow> qs = {z. (y, z) \<in> yqs} \<and> card {z. (y, z) \<in> yqs} = 1"
    unfolding m''_def Mapping.lookup_filter 
    unfolding \<open>Mapping.lookup m' = set_as_map yqs\<close> set_as_map_def
    by auto
  then have **:"\<And> q' . Mapping.lookup m''' y = Some q' \<longleftrightarrow> card {z. (y, z) \<in> yqs} = 1 \<and> q' = the_elem {z. (y, z) \<in> yqs}"
    unfolding m'''_def lookup_map_values by auto
  then show ?thesis
    unfolding h_obs_impl.simps Let_def 
    unfolding \<open>Mapping.lookup (h_obs_impl_from_h h') (q,x) = Some m'''\<close>
    using "*" Some by force
qed







definition set_as_mapping_image :: "('a1 \<times> 'a2) set \<Rightarrow> (('a1 \<times> 'a2) \<Rightarrow> ('b1 \<times> 'b2)) \<Rightarrow> ('b1, 'b2 set) mapping" where 
  "set_as_mapping_image s f = (THE m . Mapping.lookup m = set_as_map (image f s))"

lemma set_as_mapping_image_ob :
  obtains m where "set_as_mapping_image s f = m" and "Mapping.lookup m = set_as_map (image f s)"
proof -
  obtain m where *:"Mapping.lookup m = set_as_map (image f s)"
    using Mapping.lookup.abs_eq by auto
  moreover have "(THE x. Mapping.lookup x = set_as_map (image f s)) = m"
    using the_equality[of "\<lambda>m . Mapping.lookup m = set_as_map (image f s)", OF *] 
    unfolding *[symmetric]
    by (simp add: mapping_eqI) 
  ultimately show ?thesis 
    using that[of m] unfolding set_as_mapping_image_def by blast
qed

lemma set_as_mapping_image_code[code]  :
  fixes t :: "('a1 ::ccompare \<times> 'a2 :: ccompare) set_rbt" 
  and   f1 :: "('a1 \<times> 'a2) \<Rightarrow> ('b1 :: ccompare \<times> 'b2 ::ccompare)"
  and   xs :: "('c1 :: ceq \<times> 'c2 :: ceq) set_dlist" 
  and   f2 :: "('c1 \<times> 'c2) \<Rightarrow> ('d1 \<times> 'd2)"
shows "set_as_mapping_image (RBT_set t) f1 = (case ID CCOMPARE(('a1 \<times> 'a2)) of
           Some _ \<Rightarrow> (RBT_Set2.fold (\<lambda> kv m1 .
                        ( case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1)))
                      t
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map_image RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_mapping_image (RBT_set t) f1))"
  (is "set_as_mapping_image (RBT_set t) f1 = ?C1 (RBT_set t)")
and   "set_as_mapping_image (DList_set xs) f2 = (case ID CEQ(('c1 \<times> 'c2)) of
            Some _ \<Rightarrow> (DList_Set.fold (\<lambda> kv m1 . 
                        ( case f2 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1)))
                      xs
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map_image DList_set: ccompare = None'') 
                                (\<lambda>_. set_as_mapping_image (DList_set xs) f2))"
  (is "set_as_mapping_image (DList_set xs) f2 = ?C2 (DList_set xs)")
proof -
  show "set_as_mapping_image (RBT_set t) f1 = ?C1 (RBT_set t)"

  proof (cases "ID CCOMPARE(('a1 \<times> 'a2))")
    case None
    then show ?thesis by auto
  next
    case (Some a)
  
    let ?f' = "\<lambda> t . (RBT_Set2.fold (\<lambda> kv m1 .
                          ( case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1)))
                        t
                        Mapping.empty)"
  
    let ?f = "\<lambda> xs . (fold (\<lambda> kv m1 . case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1))
                              xs Mapping.empty)"
    have "\<And> xs :: ('a1 \<times> 'a2) list . Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None)"
    proof -
      fix xs :: "('a1 \<times> 'a2) list"
      show "Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None)"
      proof (induction xs rule: rev_induct)
        case Nil
        then show ?case 
          by (simp add: Mapping.empty.abs_eq Mapping.lookup.abs_eq) 
      next
        case (snoc xz xs)
        then obtain x z where "f1  xz = (x,z)" 
          by (metis (mono_tags, opaque_lifting) surj_pair)
    
        then have *: "(?f (xs@[xz])) = (case Mapping.lookup (?f xs) x of
                                    None \<Rightarrow> Mapping.update x {z} (?f xs) |
                                    Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) (?f xs))"
          by auto
    
        then show ?case proof (cases "Mapping.lookup (?f xs) x")
          case None
          then have **: "Mapping.lookup (?f (xs@[xz])) = Mapping.lookup (Mapping.update x {z} (?f xs))" using * by auto
    
          have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
            by (metis lookup_update')
    
    
          have m1: "Mapping.lookup (?f (xs@[xz])) = (\<lambda> x' . if x' = x then Some {z} else Mapping.lookup (?f xs) x')"
            unfolding ** 
            unfolding scheme by force
    
          have "(\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x = None"
          using None snoc by auto
          then have "\<not>(\<exists> z . (x,z) \<in> f1 ` set xs)"
            by (metis (mono_tags, lifting) option.distinct(1))
          then have "(\<exists> z' . (x,z') \<in> f1 ` set (xs@[xz]))" and "{z' . (x,z') \<in> f1 ` set (xs@[xz])} = {z}"
            using \<open>f1  xz = (x,z)\<close> by fastforce+
          then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> f1 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f1 ` set (xs@[xz])} else None)
                       = (\<lambda> x' . if x' = x then Some {z} else (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x')"
            using \<open>f1  xz = (x,z)\<close> by fastforce
          
          show ?thesis using m1 m2 snoc
            using \<open>f1 xz = (x, z)\<close> by presburger
        next
          case (Some zs)
          then have **: "Mapping.lookup (?f (xs@[xz])) = Mapping.lookup (Mapping.update x (Set.insert z zs) (?f xs))" using * by auto
          have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
            by (metis lookup_update')
    
          have m1: "Mapping.lookup (?f (xs@[xz])) = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else Mapping.lookup (?f xs) x')"
            unfolding ** 
            unfolding scheme by force
    
    
          have "(\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x = Some zs"
            using Some snoc by auto
          then have "(\<exists> z' . (x,z') \<in> f1 ` set xs)"
            unfolding case_prod_conv using  option.distinct(2) by metis
          then have "(\<exists> z' . (x,z') \<in> f1 ` set (xs@[xz]))" by fastforce
    
          have "{z' . (x,z') \<in> f1 ` set (xs@[xz])} = Set.insert z zs"
          proof -
            have "Some {z . (x,z) \<in> f1 ` set xs} = Some zs"
              using \<open>(\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x = Some zs\<close>
              unfolding case_prod_conv using  option.distinct(2) by metis
            then have "{z . (x,z) \<in> f1 ` set xs} = zs" by auto
            then show ?thesis 
              using \<open>f1 xz = (x, z)\<close> by auto
          qed
    
          have "\<And> a  . (\<lambda> x' . if (\<exists> z' . (x',z') \<in> f1 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f1 ` set (xs@[xz])} else None) a
                     = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x') a" 
          proof -
            fix a show "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> f1 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f1 ` set (xs@[xz])} else None) a
                       = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x') a"
            using \<open>{z' . (x,z') \<in> f1 ` set (xs@[xz])} = Set.insert z zs\<close> \<open>(\<exists> z' . (x,z') \<in> f1 ` set (xs@[xz]))\<close> \<open>f1 xz = (x, z)\<close>
            by (cases "a = x"; auto)
          qed
  
          then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> f1 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f1 ` set (xs@[xz])} else None)
                       = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x')"
            by auto
    
    
          show ?thesis using m1 m2 snoc
            using \<open>f1 xz = (x, z)\<close> by presburger
        qed
      qed
    qed
  
  
    
    then have "Mapping.lookup (?f' t) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set (RBT_Set2.keys t)) then Some {z . (x,z) \<in> f1 ` set (RBT_Set2.keys t)} else None)"
      unfolding fold_conv_fold_keys by metis
    moreover have "set (RBT_Set2.keys t) = (RBT_set t)" 
      using Some by (simp add: RBT_set_conv_keys) 
    ultimately have "Mapping.lookup (?f' t) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` (RBT_set t)) then Some {z . (x,z) \<in> f1 ` (RBT_set t)} else None)"
      by force
  
    then have "Mapping.lookup (?f' t) = set_as_map (image f1 (RBT_set t))"
      unfolding set_as_map_def by blast
    then have *:"Mapping.lookup (?C1 (RBT_set t)) = set_as_map (image f1 (RBT_set t))"
      unfolding Some by force
    
    have "\<And> t' . Mapping.lookup (?C1 (RBT_set t)) = Mapping.lookup (?C1 t') \<Longrightarrow> (?C1 (RBT_set t)) = (?C1 t')"
      by (simp add: Some)
    then have **: "(\<And>x. Mapping.lookup x = set_as_map (image f1 (RBT_set t)) \<Longrightarrow> x = (?C1 (RBT_set t)))"
      by (simp add: "*" mapping_eqI)
  
    show ?thesis
      using the_equality[of "\<lambda> m . Mapping.lookup m = (set_as_map (image f1 (RBT_set t)))", OF * **]
      unfolding set_as_mapping_image_def by blast
  qed

  show "set_as_mapping_image (DList_set xs) f2 = ?C2 (DList_set xs)"
  proof (cases "ID CEQ(('c1 \<times> 'c2))")
    case None
    then show ?thesis by auto
  next
    case (Some a)
  
    let ?f' = "\<lambda> t . (DList_Set.fold (\<lambda> kv m1 .
                          ( case f2 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1)))
                        t
                        Mapping.empty)"
  
    let ?f = "\<lambda> xs . (fold (\<lambda> kv m1 . case f2 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1))
                              xs Mapping.empty)"
    have *:"\<And> xs :: ('c1 \<times> 'c2) list . Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` set xs) then Some {z . (x,z) \<in> f2 ` set xs} else None)"
    proof -
      fix xs :: "('c1 \<times> 'c2) list"
      show "Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` set xs) then Some {z . (x,z) \<in> f2 ` set xs} else None)"
      proof (induction xs rule: rev_induct)
        case Nil
        then show ?case 
          by (simp add: Mapping.empty.abs_eq Mapping.lookup.abs_eq) 
      next
        case (snoc xz xs)
        then obtain x z where "f2  xz = (x,z)" 
          by (metis (mono_tags, opaque_lifting) surj_pair)
    
        then have *: "(?f (xs@[xz])) = (case Mapping.lookup (?f xs) x of
                                    None \<Rightarrow> Mapping.update x {z} (?f xs) |
                                    Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) (?f xs))"
          by auto
    
        then show ?case proof (cases "Mapping.lookup (?f xs) x")
          case None
          then have **: "Mapping.lookup (?f (xs@[xz])) = Mapping.lookup (Mapping.update x {z} (?f xs))" using * by auto
    
          have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
            by (metis lookup_update')
    
    
          have m1: "Mapping.lookup (?f (xs@[xz])) = (\<lambda> x' . if x' = x then Some {z} else Mapping.lookup (?f xs) x')"
            unfolding ** 
            unfolding scheme by force
    
          have "(\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` set xs) then Some {z . (x,z) \<in> f2 ` set xs} else None) x = None"
          using None snoc by auto
          then have "\<not>(\<exists> z . (x,z) \<in> f2 ` set xs)"
            by (metis (mono_tags, lifting) option.distinct(1))
          then have "(\<exists> z' . (x,z') \<in> f2 ` set (xs@[xz]))" and "{z' . (x,z') \<in> f2 ` set (xs@[xz])} = {z}"
            using \<open>f2  xz = (x,z)\<close> by fastforce+
          then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> f2 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f2 ` set (xs@[xz])} else None)
                       = (\<lambda> x' . if x' = x then Some {z} else (\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` set xs) then Some {z . (x,z) \<in> f2 ` set xs} else None) x')"
            using \<open>f2  xz = (x,z)\<close> by fastforce
          
          show ?thesis using m1 m2 snoc
            using \<open>f2 xz = (x, z)\<close> by presburger
        next
          case (Some zs)
          then have **: "Mapping.lookup (?f (xs@[xz])) = Mapping.lookup (Mapping.update x (Set.insert z zs) (?f xs))" using * by auto
          have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
            by (metis lookup_update')
    
          have m1: "Mapping.lookup (?f (xs@[xz])) = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else Mapping.lookup (?f xs) x')"
            unfolding ** 
            unfolding scheme by force
    
    
          have "(\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` set xs) then Some {z . (x,z) \<in> f2 ` set xs} else None) x = Some zs"
            using Some snoc by auto
          then have "(\<exists> z' . (x,z') \<in> f2 ` set xs)"
            unfolding case_prod_conv using  option.distinct(2) by metis
          then have "(\<exists> z' . (x,z') \<in> f2 ` set (xs@[xz]))" by fastforce
    
          have "{z' . (x,z') \<in> f2 ` set (xs@[xz])} = Set.insert z zs"
          proof -
            have "Some {z . (x,z) \<in> f2 ` set xs} = Some zs"
              using \<open>(\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` set xs) then Some {z . (x,z) \<in> f2 ` set xs} else None) x = Some zs\<close>
              unfolding case_prod_conv using  option.distinct(2) by metis
            then have "{z . (x,z) \<in> f2 ` set xs} = zs" by auto
            then show ?thesis 
              using \<open>f2 xz = (x, z)\<close> by auto
          qed
    
          have "\<And> a  . (\<lambda> x' . if (\<exists> z' . (x',z') \<in> f2 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f2 ` set (xs@[xz])} else None) a
                     = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` set xs) then Some {z . (x,z) \<in> f2 ` set xs} else None) x') a" 
          proof -
            fix a show "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> f2 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f2 ` set (xs@[xz])} else None) a
                       = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` set xs) then Some {z . (x,z) \<in> f2 ` set xs} else None) x') a"
            using \<open>{z' . (x,z') \<in> f2 ` set (xs@[xz])} = Set.insert z zs\<close> \<open>(\<exists> z' . (x,z') \<in> f2 ` set (xs@[xz]))\<close> \<open>f2 xz = (x, z)\<close>
            by (cases "a = x"; auto)
          qed
  
          then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> f2 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f2 ` set (xs@[xz])} else None)
                       = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` set xs) then Some {z . (x,z) \<in> f2 ` set xs} else None) x')"
            by auto
    
    
          show ?thesis using m1 m2 snoc
            using \<open>f2 xz = (x, z)\<close> by presburger
        qed
      qed
    qed


    have "ID CEQ('c1 \<times> 'c2) \<noteq> None"
      using Some by auto
    then have **: "\<And> x . x \<in> f2 ` set (list_of_dlist xs) = (x \<in> f2 ` (DList_set xs))" 
      using DList_Set.member.rep_eq[of xs]
      using Set_member_code(2) ceq_class.ID_ceq in_set_member by fastforce 
    
    have "Mapping.lookup (?f' xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f2 ` (DList_set xs)) then Some {z . (x,z) \<in> f2 ` (DList_set xs)} else None)"
      using *[of "(list_of_dlist xs)"] 
      unfolding DList_Set.fold.rep_eq ** .
    then have "Mapping.lookup (?f' xs) = set_as_map (image f2 (DList_set xs))"
      unfolding set_as_map_def by blast
    then have *:"Mapping.lookup (?C2 (DList_set xs)) = set_as_map (image f2 (DList_set xs))"
      unfolding Some by force
    
    have "\<And> t' . Mapping.lookup (?C2 (DList_set xs)) = Mapping.lookup (?C2 t') \<Longrightarrow> (?C2 (DList_set xs)) = (?C2 t')"
      by (simp add: Some)
    then have **: "(\<And>x. Mapping.lookup x = set_as_map (image f2 (DList_set xs)) \<Longrightarrow> x = (?C2 (DList_set xs)))"
      by (simp add: "*" mapping_eqI)    
    then show ?thesis
      using *
      using set_as_mapping_image_ob by blast 
  qed
qed


subsection \<open>Impl Datatype\<close>

text \<open>The following type extends @{text "fsm_impl"} with fields for  @{text "h"} and  @{text "h_obs"}.\<close>

datatype ('state, 'input, 'output) fsm_with_precomputations_impl = 
        FSMWPI (initial_wpi : 'state)  
               (states_wpi : "'state set")
               (inputs_wpi  : "'input set")
               (outputs_wpi : "'output set")
               (transitions_wpi : "('state \<times> 'input \<times> 'output \<times> 'state) set")
               (h_wpi : "(('state \<times> 'input), ('output \<times> 'state) set) mapping")
               (h_obs_wpi: "('state \<times> 'input, ('output, 'state) mapping) mapping")

fun fsm_with_precomputations_impl_from_list :: "'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a, 'b, 'c) fsm_with_precomputations_impl" where
  "fsm_with_precomputations_impl_from_list q [] = FSMWPI q {q} {} {} {} Mapping.empty Mapping.empty" |
  "fsm_with_precomputations_impl_from_list q (t#ts) = (let ts' = set (t#ts)
                                   in FSMWPI (t_source t)
                                      ((image t_source ts') \<union> (image t_target ts'))
                                      (image t_input ts')
                                      (image t_output ts')
                                      (ts')
                                      (list_as_mapping (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) (t#ts)))
                                      (h_obs_impl_from_h (list_as_mapping (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) (t#ts)))))"

fun fsm_with_precomputations_impl_from_list' :: "'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a, 'b, 'c) fsm_with_precomputations_impl" where
  "fsm_with_precomputations_impl_from_list' q [] = FSMWPI q {q} {} {} {} Mapping.empty Mapping.empty" |
  "fsm_with_precomputations_impl_from_list' q (t#ts) = (let tsr = (remdups (t#ts));
                                                            h'  = (list_as_mapping (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) tsr))
                                   in FSMWPI (t_source t)
                                      (set (remdups ((map t_source tsr) @ (map t_target tsr))))
                                      (set (remdups (map t_input tsr)))
                                      (set (remdups (map t_output tsr)))
                                      (set tsr)
                                      h'
                                      (h_obs_impl_from_h h'))"



lemma fsm_impl_from_list_code[code] :
  "fsm_with_precomputations_impl_from_list q ts = fsm_with_precomputations_impl_from_list' q ts" 
proof (cases ts)
  case Nil
  then show ?thesis by auto
next
  case (Cons t ts)
  have **: "set (t#ts) = set (remdups (t#ts))"
    by auto
  have *: "set (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) (t#ts)) = set (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) (remdups (t#ts)))"
    by (metis remdups_map_remdups set_remdups)
  have "Mapping.lookup (list_as_mapping (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) (t#ts)))
             = Mapping.lookup (list_as_mapping (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) (remdups (t#ts))))"
    unfolding list_as_mapping_lookup * by simp
  then have ***: "list_as_mapping (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) (t#ts)) = list_as_mapping (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) (remdups (t#ts)))"
    by (simp add: mapping_eqI)

  have ****: "(set (map t_source (remdups (t # ts)) @ map t_target (remdups (t # ts)))) = (t_source ` set (t # ts) \<union> t_target ` set (t # ts))"
    by auto

  have *****: "\<And> f xs . set (map f (remdups xs)) = f ` set xs"
    by auto

  show ?thesis
    unfolding Cons fsm_with_precomputations_impl_from_list'.simps fsm_with_precomputations_impl_from_list.simps Let_def
    unfolding ** *** 
    unfolding set_remdups ****  ***** 
    unfolding remdups_map_remdups 
    by presburger
qed 



subsection \<open>Refined Datatype\<close>

text \<open>Well-formedness now also encompasses the new fields for  @{text "h"} and  @{text "h_obs"}.\<close>


fun well_formed_fsm_with_precomputations :: "('state, 'input, 'output) fsm_with_precomputations_impl \<Rightarrow> bool" where 
  "well_formed_fsm_with_precomputations M = (initial_wpi M \<in> states_wpi M
      \<and> finite (states_wpi M)
      \<and> finite (inputs_wpi M)
      \<and> finite (outputs_wpi M)
      \<and> finite (transitions_wpi M)
      \<and> (\<forall> t \<in> transitions_wpi M . t_source t \<in> states_wpi M \<and> 
                                t_input t \<in> inputs_wpi M \<and> 
                                t_target t \<in> states_wpi M \<and> 
                                t_output t \<in> outputs_wpi M)
      \<and> (\<forall> q x . (case (Mapping.lookup (h_wpi M) (q,x)) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}) = { (y,q') . (q,x,y,q') \<in> transitions_wpi M })
      \<and> (\<forall> q x y . h_obs_impl (h_wpi M) q x y = h_obs_lookup (h_obs_wpi M) q x y))"

lemma well_formed_h_set_as_mapping :
  assumes "h_wpi M = set_as_mapping_image (transitions_wpi M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))"
  shows "(case (Mapping.lookup (h_wpi M) (q,x)) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}) = { (y,q') . (q,x,y,q') \<in> transitions_wpi M }"
(is "?A q x = ?B q x")
proof -
  have *:"Mapping.lookup (h_wpi M) = (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y,q')) (transitions_wpi M)))"
    unfolding assms using set_as_mapping_image_ob
    by auto 
  have **: "(case Mapping.lookup (h_wpi M) (q, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts) = {a. case a of (y, q') \<Rightarrow> (q, x, y, q') \<in> (transitions_wpi M)}"
    unfolding *
    unfolding set_as_map_def by force

  show ?thesis
    unfolding  ** by force
qed

lemma well_formed_h_obs_impl_from_h :
  assumes "h_obs_wpi M = h_obs_impl_from_h (h_wpi M)"
  shows "h_obs_impl  (h_wpi M) q x y = (h_obs_lookup  (h_obs_wpi M) q x y)"
  unfolding assms h_obs_impl_from_h_invar by presburger


typedef ('state, 'input, 'output) fsm_with_precomputations = 
  "{ M :: ('state, 'input, 'output) fsm_with_precomputations_impl . well_formed_fsm_with_precomputations M}"
  morphisms fsm_with_precomputations_impl_of_fsm_with_precomputations Abs_fsm_with_precomputations
proof -
  obtain q :: 'state where "True" by blast
  define M :: "('state, 'input, 'output) fsm_with_precomputations_impl" where 
    M: "M = FSMWPI q {q} {} {} {} Mapping.empty Mapping.empty"
  
  have "(\<And> q x . (case (Mapping.lookup (h_wpi M) (q,x)) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}) = { (y,q') . (q,x,y,q') \<in> transitions_wpi M })"
  proof -
    fix q x 
    have "{ (y,q') . (q,x,y,q') \<in> transitions_wpi M } = {}"
      unfolding M by auto
    moreover have "(case (Mapping.lookup (h_wpi M) (q,x)) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}) = {}"
      unfolding M by (metis fsm_with_precomputations_impl.sel(6) lookup_default_def lookup_default_empty) 
    ultimately show "(case (Mapping.lookup (h_wpi M) (q,x)) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}) = { (y,q') . (q,x,y,q') \<in> transitions_wpi M }"
      by blast
  qed
  moreover have "(\<forall> q x y . h_obs_impl  (h_wpi M) q x y = (h_obs_lookup  (h_obs_wpi M) q x y))"
    unfolding h_obs_impl.simps Let_def
    unfolding calculation M
    by (simp add: Mapping.empty_def Mapping.lookup.abs_eq Set.filter_def) 
  ultimately have "well_formed_fsm_with_precomputations M"
    unfolding M by auto
  then show ?thesis 
    by blast
qed


setup_lifting type_definition_fsm_with_precomputations

lift_definition initial_wp :: "('state, 'input, 'output) fsm_with_precomputations \<Rightarrow> 'state" is FSM_Code_Datatype.initial_wpi done
lift_definition states_wp :: "('state, 'input, 'output) fsm_with_precomputations \<Rightarrow> 'state set" is FSM_Code_Datatype.states_wpi done
lift_definition inputs_wp :: "('state, 'input, 'output) fsm_with_precomputations \<Rightarrow> 'input set" is FSM_Code_Datatype.inputs_wpi done
lift_definition outputs_wp :: "('state, 'input, 'output) fsm_with_precomputations \<Rightarrow> 'output set" is FSM_Code_Datatype.outputs_wpi done
lift_definition transitions_wp :: 
  "('state, 'input, 'output) fsm_with_precomputations \<Rightarrow> ('state \<times> 'input \<times> 'output \<times> 'state) set" 
  is FSM_Code_Datatype.transitions_wpi done
lift_definition h_wp :: 
  "('state, 'input, 'output) fsm_with_precomputations \<Rightarrow> (('state \<times> 'input), ('output \<times> 'state) set) mapping" 
  is FSM_Code_Datatype.h_wpi done
lift_definition h_obs_wp :: 
  "('state, 'input, 'output) fsm_with_precomputations \<Rightarrow> (('state \<times> 'input), ('output, 'state) mapping) mapping" 
  is FSM_Code_Datatype.h_obs_wpi done


lemma fsm_with_precomputations_initial: "initial_wp M \<in> states_wp M" 
  by (transfer; auto)
lemma fsm_with_precomputations_states_finite: "finite (states_wp M)" 
  by (transfer; auto)
lemma fsm_with_precomputations_inputs_finite: "finite (inputs_wp M)" 
  by (transfer; auto)
lemma fsm_with_precomputations_outputs_finite: "finite (outputs_wp M)" 
  by (transfer; auto)
lemma fsm_with_precomputations_transitions_finite: "finite (transitions_wp M)" 
  by (transfer; auto)
lemma fsm_with_precomputations_transition_props: "t \<in> transitions_wp M \<Longrightarrow> t_source t \<in> states_wp M \<and> 
                                                                        t_input t \<in> inputs_wp M \<and> 
                                                                        t_target t \<in> states_wp M \<and> 
                                                                        t_output t \<in> outputs_wp M" 
  by (transfer; auto)
lemma fsm_with_precomputations_h_prop: "(case (Mapping.lookup (h_wp M) (q,x)) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}) = { (y,q') . (q,x,y,q') \<in> transitions_wp M }" 
  by (transfer; auto)


lemma fsm_with_precomputations_h_obs_prop: "(h_obs_lookup  (h_obs_wp M) q x y) = h_obs_impl  (h_wp M) q x y"
proof -
  define M' where "M' = fsm_with_precomputations_impl_of_fsm_with_precomputations M"
  then have "well_formed_fsm_with_precomputations M'"
    by (transfer;blast)
  then have *:"h_obs_impl  (fsm_with_precomputations_impl.h_wpi M') q x y = (h_obs_lookup (h_obs_wpi M') q x y)"
    unfolding well_formed_fsm_with_precomputations.simps by blast

  have **: "(h_obs_lookup (h_obs_wpi M') q x y) = h_obs_impl (fsm_with_precomputations_impl.h_wpi M') q x y"
    unfolding * by auto  
  have ***: "h_wp M = (fsm_with_precomputations_impl.h_wpi M')"
    unfolding M'_def apply transfer by presburger
  have ****: "h_obs_wp M = (fsm_with_precomputations_impl.h_obs_wpi M')"
    unfolding M'_def apply transfer by presburger

  show ?thesis
    using "**" "***" "****" by presburger 
qed

lemma map_values_empty : "Mapping.map_values f Mapping.empty = Mapping.empty"
  by (metis Mapping.keys_empty empty_iff keys_map_values mapping_eqI')

lift_definition fsm_with_precomputations_from_list :: "'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a, 'b, 'c) fsm_with_precomputations" 
  is fsm_with_precomputations_impl_from_list
proof -
  fix q  :: 'a 
  fix ts :: "('a \<times> 'b \<times> 'c \<times> 'a) list"

  define M where "M = fsm_with_precomputations_impl_from_list q ts"

  have base_props: "(initial_wpi M \<in> states_wpi M
      \<and> finite (states_wpi M)
      \<and> finite (inputs_wpi M)
      \<and> finite (outputs_wpi M)
      \<and> finite (transitions_wpi M))"
  proof (cases ts)
    case Nil
    show ?thesis 
      unfolding M_def Nil fsm_with_precomputations_impl_from_list.simps by auto
  next
    case (Cons t ts')
    show ?thesis 
      unfolding M_def Cons fsm_with_precomputations_impl_from_list.simps Let_def by force
  qed
  

  have transition_prop: "(\<forall> t \<in> transitions_wpi M . t_source t \<in> states_wpi M \<and> 
                                t_input t \<in> inputs_wpi M \<and> 
                                t_target t \<in> states_wpi M \<and> 
                                t_output t \<in> outputs_wpi M)"
  proof (cases ts)
    case Nil
    show ?thesis 
      unfolding M_def Nil fsm_with_precomputations_impl_from_list.simps by auto
  next
    case (Cons t ts')
    show ?thesis 
      unfolding M_def Cons fsm_with_precomputations_impl_from_list.simps Let_def by force
  qed


  have h_prop:"\<And> qa x .
        (case Mapping.lookup (h_wpi M) (qa, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts) =
        {a. case a of (y, q') \<Rightarrow> (qa, x, y, q') \<in> transitions_wpi M}"
  (is "\<And> qa x . ?P qa x")
  proof -
    fix qa x 
    show "?P qa x" unfolding M_def
    proof (induction ts)
      case Nil
      have "(case Mapping.lookup (h_wpi (fsm_with_precomputations_impl_from_list q [])) (qa, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts) = {}"
        by simp   
      moreover have "transitions_wpi (fsm_with_precomputations_impl_from_list q []) = {}"
        by auto
      ultimately show ?case
        by blast
    next
      case (Cons t ts)
      have *: "(h_wpi (fsm_with_precomputations_impl_from_list q (t#ts))) = (list_as_mapping (map (\<lambda>(q,x,y,q') . ((q,x),y,q')) (t#ts)))"
        unfolding fsm_with_precomputations_impl_from_list.simps Let_def by simp
      show ?case proof (cases "\<exists>z. ((qa, x), z) \<in> set (map (\<lambda>(q, x, y, q'). ((q, x), y, q')) (t # ts))")
        case True
        then have "(case Mapping.lookup (h_wpi (fsm_with_precomputations_impl_from_list q (t#ts))) (qa, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts) = {z. ((qa, x), z) \<in> set (map (\<lambda>(q, x, y, q'). ((q, x), y, q')) (t # ts))}"
          unfolding * list_as_mapping_lookup by auto
        also have "\<dots> = {a. case a of (y, q') \<Rightarrow> (qa, x, y, q') \<in> transitions_wpi (fsm_with_precomputations_impl_from_list q (t#ts))}"
          unfolding fsm_with_precomputations_impl_from_list.simps Let_def 
          by (induction ts; cases t; auto)
        finally show ?thesis .
      next
        case False
        then have "(case Mapping.lookup (h_wpi (fsm_with_precomputations_impl_from_list q (t#ts))) (qa, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts) = {}"
          unfolding * list_as_mapping_lookup by auto 
        also have "\<dots> = {a. case a of (y, q') \<Rightarrow> (qa, x, y, q') \<in> transitions_wpi (fsm_with_precomputations_impl_from_list q (t#ts))}"
          using False unfolding fsm_with_precomputations_impl_from_list.simps Let_def 
          by (induction ts; cases t; auto)
        finally show ?thesis .
      qed
    qed
  qed

  have h_obs_prop: "(\<forall> q x y . h_obs_impl  (h_wpi M) q x y = (h_obs_lookup  (h_obs_wpi M) q x y))"
  proof -
    have ***:"h_obs_wpi M = (h_obs_impl_from_h  (h_wpi M))"
    proof (cases ts)
      case Nil
      then have *:"h_wpi M = Mapping.empty" and **:"h_obs_wpi M = Mapping.empty"
        unfolding M_def by auto
      show ?thesis 
        unfolding * ** h_obs_impl_from_h.simps map_values_empty by simp
    next
      case (Cons t ts')
      show ?thesis 
        unfolding Cons M_def fsm_with_precomputations_impl_from_list.simps Let_def by simp
    qed
    then show ?thesis
      unfolding h_obs_impl_from_h_invar
      by simp
  qed

  show "well_formed_fsm_with_precomputations (fsm_with_precomputations_impl_from_list q ts)"  
    using base_props transition_prop h_prop h_obs_prop
    unfolding well_formed_fsm_with_precomputations.simps  M_def[symmetric]
    by blast
qed

lemma fsm_with_precomputations_from_list_Nil_simps :
  "initial_wp (fsm_with_precomputations_from_list q []) = q"
  "states_wp (fsm_with_precomputations_from_list q []) = {q}"
  "inputs_wp (fsm_with_precomputations_from_list q []) = {}"
  "outputs_wp (fsm_with_precomputations_from_list q []) = {}"
  "transitions_wp (fsm_with_precomputations_from_list q []) = {}"
  by (transfer; auto)+
  
lemma fsm_with_precomputations_from_list_Cons_simps :
  "initial_wp (fsm_with_precomputations_from_list q (t#ts)) = (t_source t)"
  "states_wp (fsm_with_precomputations_from_list q (t#ts)) = ((image t_source (set (t#ts))) \<union> (image t_target (set (t#ts))))"
  "inputs_wp (fsm_with_precomputations_from_list q (t#ts)) = (image t_input (set (t#ts)))"
  "outputs_wp (fsm_with_precomputations_from_list q (t#ts)) = (image t_output (set (t#ts)))"
  "transitions_wp (fsm_with_precomputations_from_list q (t#ts)) = (set (t#ts))"
  by (transfer; auto)+

definition Fsm_with_precomputations :: "('a,'b,'c) fsm_with_precomputations_impl \<Rightarrow> ('a,'b,'c) fsm_with_precomputations" where
  "Fsm_with_precomputations M = Abs_fsm_with_precomputations (if well_formed_fsm_with_precomputations M then M else FSMWPI undefined {undefined} {} {} {} Mapping.empty Mapping.empty)"

lemma fsm_with_precomputations_code_abstype [code abstype] :
  "Fsm_with_precomputations (fsm_with_precomputations_impl_of_fsm_with_precomputations M) = M"
proof -
  have "well_formed_fsm_with_precomputations (fsm_with_precomputations_impl_of_fsm_with_precomputations M)"
    using fsm_with_precomputations_impl_of_fsm_with_precomputations[of M] by blast
  then show ?thesis
    unfolding Fsm_with_precomputations_def
    using fsm_with_precomputations_impl_of_fsm_with_precomputations_inverse[of M] by presburger
qed

lemma fsm_with_precomputations_impl_of_fsm_with_precomputations_code [code] :
  "fsm_with_precomputations_impl_of_fsm_with_precomputations (fsm_with_precomputations_from_list q ts) = fsm_with_precomputations_impl_from_list q ts"
  by (fact fsm_with_precomputations_from_list.rep_eq)
                                


definition FSMWP :: "('state, 'input, 'output) fsm_with_precomputations \<Rightarrow> ('state, 'input, 'output) fsm_impl" where
  "FSMWP M = FSMI (initial_wp M)
             (states_wp M)
             (inputs_wp M)
             (outputs_wp M)
             (transitions_wp M)"

code_datatype FSMWP 


subsection \<open>Lifting\<close>


declare [[code drop: fsm_impl_from_list]]
lemma fsm_impl_from_list[code] :
  "fsm_impl_from_list q ts = FSMWP (fsm_with_precomputations_from_list q ts)"
proof (induction ts)
  case Nil
  show ?case unfolding fsm_impl_from_list.simps FSMWP_def fsm_with_precomputations_from_list_Nil_simps by simp
next
  case (Cons t ts)
  show ?case unfolding fsm_impl_from_list.simps FSMWP_def fsm_with_precomputations_from_list_Cons_simps Let_def by simp
qed


declare [[code drop: fsm_impl.initial fsm_impl.states fsm_impl.inputs fsm_impl.outputs fsm_impl.transitions]]
lemma fsm_impl_FSMWP_initial[code,simp] : "fsm_impl.initial (FSMWP M) = initial_wp M"
  by (simp add: FSMWP_def) 
lemma fsm_impl_FSMWP_states[code,simp] : "fsm_impl.states (FSMWP M) = states_wp M"
  by (simp add: FSMWP_def) 
lemma fsm_impl_FSMWP_inputs[code,simp] : "fsm_impl.inputs (FSMWP M) = inputs_wp M"
  by (simp add: FSMWP_def) 
lemma fsm_impl_FSMWP_outputs[code,simp] : "fsm_impl.outputs (FSMWP M) = outputs_wp M"
  by (simp add: FSMWP_def) 
lemma fsm_impl_FSMWP_transitions[code,simp] : "fsm_impl.transitions (FSMWP M) = transitions_wp M"
  by (simp add: FSMWP_def) 


lemma well_formed_FSMWP:  "well_formed_fsm (FSMWP M)"
proof -
  have *: "well_formed_fsm_with_precomputations (fsm_with_precomputations_impl_of_fsm_with_precomputations M)"
    using fsm_with_precomputations_impl_of_fsm_with_precomputations by blast
  then have "(initial_wp M \<in> states_wp M
      \<and> finite (states_wp M)
      \<and> finite (inputs_wp M)
      \<and> finite (outputs_wp M)
      \<and> finite (transitions_wp M)
      \<and> (\<forall> t \<in> transitions_wp M . t_source t \<in> states_wp M \<and> 
                                t_input t \<in> inputs_wp M \<and> 
                                t_target t \<in> states_wp M \<and> 
                                t_output t \<in> outputs_wp M))" 
    unfolding well_formed_fsm_with_precomputations.simps
    by (simp add: FSM_Code_Datatype.initial_wp.rep_eq FSM_Code_Datatype.inputs_wp.rep_eq FSM_Code_Datatype.outputs_wp.rep_eq FSM_Code_Datatype.states_wp.rep_eq FSM_Code_Datatype.transitions_wp.rep_eq)
  then show ?thesis
    unfolding FSMWP_def by simp
qed




declare [[code drop: FSM_Impl.h ]]
lemma h_with_precomputations_code [code] : "FSM_Impl.h ((FSMWP M)) = (\<lambda> (q,x) . case Mapping.lookup (h_wp M) (q,x) of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {})"
proof -
  have *: "\<And> q x . (case (Mapping.lookup (h_wp M) (q,x)) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}) = { (y,q') . (q,x,y,q') \<in> transitions_wp M }"
    by (transfer; auto)

  have **: "fsm_impl.transitions ((FSMWP M)) = transitions_wp M" 
    by (simp add: FSMWP_def)
      
  have "\<And> q x . FSM_Impl.h ((FSMWP M)) (q,x) = (\<lambda> (q,x) . case Mapping.lookup (h_wp M) (q,x) of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}) (q,x)"
    unfolding * FSM_Impl.h.simps case_prod_unfold fst_conv snd_conv ** by blast
  then show ?thesis
    by blast
qed

declare [[code drop: FSM_Impl.h_obs ]]
lemma h_obs_with_precomputations_code [code] : "FSM_Impl.h_obs ((FSMWP M)) q x y = (h_obs_lookup  (h_obs_wp M) q x y)"
  unfolding fsm_with_precomputations_h_obs_prop
  unfolding FSM_Impl.h_obs.simps
  unfolding h_obs_impl.simps
  unfolding Let_def
  unfolding FSM_Impl.h.simps[of "FSMWP M" q x]
  unfolding fsm_with_precomputations_h_prop[of M q x]
  by auto



fun filter_states_impl :: "('a,'b,'c) fsm_with_precomputations_impl \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm_with_precomputations_impl" where
  "filter_states_impl M P = (if P (initial_wpi M) 
                          then (let 
                                  h' = Mapping.filter (\<lambda> (q,x) yqs . P q) (h_wpi M);
                                  h'' = Mapping.map_values (\<lambda> _ yqs . Set.filter (\<lambda> (y,q') . P q') yqs) h'
                                in
                                   FSMWPI (initial_wpi M)
                                   (Set.filter P (states_wpi M))
                                   (inputs_wpi M)
                                   (outputs_wpi M)
                                   (Set.filter (\<lambda> t . P (t_source t) \<and> P (t_target t)) (transitions_wpi M))
                                   h''
                                   (h_obs_impl_from_h h''))   
                          else M)"

lift_definition filter_states :: "('a,'b,'c) fsm_with_precomputations \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm_with_precomputations"
  is filter_states_impl
proof -
  fix M :: "('a,'b,'c) fsm_with_precomputations_impl" 
  fix P :: "('a \<Rightarrow> bool)"

  let ?M = "(filter_states_impl M P)"

  show "well_formed_fsm_with_precomputations M \<Longrightarrow> well_formed_fsm_with_precomputations ?M"
  proof -
    assume assm: "well_formed_fsm_with_precomputations M"  
    show "well_formed_fsm_with_precomputations ?M"
    proof (cases "P (initial_wpi M)")
      case False
      then have "?M = M" by auto
      then show ?thesis using assm by presburger
    next
      case True

      have "initial_wpi ?M = initial_wpi M"
        unfolding filter_states_impl.simps Let_def by auto
      have "states_wpi ?M = Set.filter P (states_wpi M)"
        using True unfolding filter_states_impl.simps Let_def by auto
      have "inputs_wpi ?M = inputs_wpi M"
        unfolding filter_states_impl.simps Let_def by auto
      have "outputs_wpi ?M = outputs_wpi M"
        unfolding filter_states_impl.simps Let_def by auto
      have "transitions_wpi ?M = (Set.filter (\<lambda> t . P (t_source t) \<and> P (t_target t)) (transitions_wpi M))"
        using True unfolding filter_states_impl.simps Let_def by auto

      define h' where "h' = Mapping.filter (\<lambda> (q,x) yqs . P q) (h_wpi M)"
      define h'' where "h'' = Mapping.map_values (\<lambda> _ yqs . Set.filter (\<lambda> (y,q') . P q') yqs) h'"

      have "h_wpi ?M = h''"
        unfolding h''_def h'_def using True unfolding filter_states_impl.simps Let_def by auto
      then have "h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)"
        using True unfolding filter_states_impl.simps Let_def by auto

      have base_props: "(initial_wpi ?M \<in> states_wpi ?M
                          \<and> finite (states_wpi ?M)
                          \<and> finite (inputs_wpi ?M)
                          \<and> finite (outputs_wpi ?M)
                          \<and> finite (transitions_wpi ?M))"
        using assm True unfolding filter_states_impl.simps Let_def by auto
  

      have transition_prop: "(\<forall> t \<in> transitions_wpi ?M . t_source t \<in> states_wpi ?M \<and> 
                                      t_input t \<in> inputs_wpi ?M \<and> 
                                      t_target t \<in> states_wpi ?M \<and> 
                                      t_output t \<in> outputs_wpi ?M)"
        using assm True unfolding filter_states_impl.simps Let_def by auto

      
      have h_prop:"\<And> qa x .
            (case Mapping.lookup (h_wpi ?M) (qa, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts) =
            {a. case a of (y, q') \<Rightarrow> (qa, x, y, q') \<in> transitions_wpi ?M}"
      (is "\<And> qa x . ?A qa x = ?B qa x")
      proof -
        fix q x 
        show "?A q x = ?B q x"
        proof (cases "P q")
          case False
          then have "Mapping.lookup h' (q,x) = None"
            unfolding h'_def 
            unfolding Mapping.lookup_filter case_prod_conv
            by (metis (mono_tags) not_None_eq option.simps(4) option.simps(5)) 
          then have "?A q x = {}"
            unfolding \<open>h_wpi ?M = h''\<close> h''_def 
            unfolding Mapping.lookup_map_values
            by simp 
          moreover have "?B q x = {}"
            unfolding \<open>transitions_wpi ?M = (Set.filter (\<lambda> t . P (t_source t) \<and> P (t_target t)) (transitions_wpi M))\<close>
            using False by auto
          ultimately show ?thesis by blast
        next
          case True
          then have "Mapping.lookup h' (q,x) = Mapping.lookup (h_wpi M) (q,x)"
            unfolding h'_def 
            unfolding Mapping.lookup_filter case_prod_conv
            by (cases "Mapping.lookup (h_wpi M) (q, x)"; auto)
          have "?A q x = Set.filter (\<lambda> (y,q') . P q') (case Mapping.lookup (h_wpi M) (q, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts)"
            unfolding \<open>h_wpi ?M = h''\<close> h''_def 
            unfolding Mapping.lookup_map_values 
            unfolding \<open>Mapping.lookup h' (q,x) = Mapping.lookup (h_wpi M) (q,x)\<close> 
            by (cases "Mapping.lookup (h_wpi M) (q, x)"; auto)
          also have "\<dots> = ?B q x"
          proof -
            have *:"(case Mapping.lookup (h_wpi M) (q, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts) = {a. case a of (y, q') \<Rightarrow> (q, x, y, q') \<in> transitions_wpi M}"
              using assm by auto
            show ?thesis
              unfolding *
              unfolding \<open>transitions_wpi ?M = (Set.filter (\<lambda> t . P (t_source t) \<and> P (t_target t)) (transitions_wpi M))\<close>
              using True
              by auto
          qed
          finally show ?thesis .
        qed
      qed

      show ?thesis
        using base_props transition_prop h_prop well_formed_h_obs_impl_from_h[OF \<open>h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)\<close>]
        unfolding well_formed_fsm_with_precomputations.simps by blast
    qed
  qed
qed

lemma filter_states_simps:
  "initial_wp (filter_states M P) = initial_wp M"
  "states_wp (filter_states M P) = (if P (initial_wp M) then Set.filter P (states_wp M) else states_wp M)"
  "inputs_wp (filter_states M P) = inputs_wp M"
  "outputs_wp (filter_states M P) = outputs_wp M"
  "transitions_wp (filter_states M P) = (if P (initial_wp M) then (Set.filter (\<lambda> t . P (t_source t) \<and> P (t_target t)) (transitions_wp M)) else transitions_wp M)"
  by (transfer; simp add: Let_def)+



declare [[code drop: FSM_Impl.filter_states ]]
lemma filter_states_with_precomputations_code [code] : "FSM_Impl.filter_states ((FSMWP M)) P = FSMWP (filter_states M P)"
  unfolding FSM_Impl.filter_states.simps Let_def
  unfolding fsm_impl_FSMWP_initial fsm_impl_FSMWP_states fsm_impl_FSMWP_inputs fsm_impl_FSMWP_outputs fsm_impl_FSMWP_transitions
  using filter_states_simps[of M P]
  by (simp add: FSMWP_def) 

  


fun create_unconnected_fsm_from_fsets_impl :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'b fset \<Rightarrow> 'c fset \<Rightarrow> ('a,'b,'c) fsm_with_precomputations_impl" where
  "create_unconnected_fsm_from_fsets_impl q ns ins outs = FSMWPI q (insert q (fset ns)) (fset ins) (fset outs) {} Mapping.empty Mapping.empty"

lift_definition create_unconnected_fsm_from_fsets :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'b fset \<Rightarrow> 'c fset \<Rightarrow> ('a,'b,'c) fsm_with_precomputations" 
  is create_unconnected_fsm_from_fsets_impl
proof -
  fix q :: 'a 
  fix ns 
  fix ins :: "'b fset" 
  fix outs :: "'c fset"

  let ?M = "(create_unconnected_fsm_from_fsets_impl q ns ins outs)"

  show "well_formed_fsm_with_precomputations (create_unconnected_fsm_from_fsets_impl q ns ins outs)"
  proof -

    have base_props: "(initial_wpi ?M \<in> states_wpi ?M
                        \<and> finite (states_wpi ?M)
                        \<and> finite (inputs_wpi ?M)
                        \<and> finite (outputs_wpi ?M)
                        \<and> finite (transitions_wpi ?M))"
      by auto


    have transition_prop: "(\<forall> t \<in> transitions_wpi ?M . t_source t \<in> states_wpi ?M \<and> 
                                    t_input t \<in> inputs_wpi ?M \<and> 
                                    t_target t \<in> states_wpi ?M \<and> 
                                    t_output t \<in> outputs_wpi ?M)"
      by auto

    have *: "(h_wpi ?M) = Mapping.empty"
      by auto
    have **: "transitions_wpi ?M = {}"
      by auto
    have ***: "(h_obs_wpi ?M) = Mapping.empty"
      by auto

    have h_prop:"\<And> qa x .
          (case Mapping.lookup (h_wpi ?M) (qa, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts) =
          {a. case a of (y, q') \<Rightarrow> (qa, x, y, q') \<in> transitions_wpi ?M}"
      unfolding * ** Mapping.lookup_empty by auto

    have h_obs_prop: "\<And> q x y . h_obs_impl  (h_wpi ?M) q x y = h_obs_lookup  (h_obs_wpi ?M) q x y"
      unfolding h_obs_impl.simps Let_def
      unfolding * *** Mapping.lookup_empty
      by (simp add: Set.filter_def) 

    show ?thesis
      using base_props transition_prop h_prop h_obs_prop
      unfolding well_formed_fsm_with_precomputations.simps by blast
  qed
qed

lemma fsm_with_precomputations_impl_of_code [code] :
  "fsm_with_precomputations_impl_of_fsm_with_precomputations (create_unconnected_fsm_from_fsets q ns ins outs) = create_unconnected_fsm_from_fsets_impl q ns ins outs"
  by (fact create_unconnected_fsm_from_fsets.rep_eq)

lemma create_unconnected_fsm_from_fsets_simps:
  "initial_wp (create_unconnected_fsm_from_fsets q ns ins outs) = q"
  "states_wp (create_unconnected_fsm_from_fsets q ns ins outs) = (insert q (fset ns))"
  "inputs_wp (create_unconnected_fsm_from_fsets q ns ins outs) = fset ins"
  "outputs_wp (create_unconnected_fsm_from_fsets q ns ins outs) = fset outs"
  "transitions_wp (create_unconnected_fsm_from_fsets q ns ins outs) = {}"
  by (transfer; simp add: Let_def)+


declare [[code drop: FSM_Impl.create_unconnected_fsm_from_fsets ]]
lemma create_unconnected_fsm_with_precomputations_code [code] : "FSM_Impl.create_unconnected_fsm_from_fsets q ns ins outs = FSMWP (create_unconnected_fsm_from_fsets q ns ins outs)"
  unfolding FSM_Impl.create_unconnected_fsm_from_fsets.simps 
  unfolding FSMWP_def
  unfolding create_unconnected_fsm_from_fsets_simps
  by presburger 


fun add_transitions_impl :: "('a,'b,'c) fsm_with_precomputations_impl \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) set \<Rightarrow> ('a,'b,'c) fsm_with_precomputations_impl" where
  "add_transitions_impl M ts = (if (\<forall> t \<in> ts . t_source t \<in> states_wpi M \<and> t_input t \<in> inputs_wpi M \<and> t_output t \<in> outputs_wpi M \<and> t_target t \<in> states_wpi M)
    then (let ts' = ((transitions_wpi M) \<union> ts);
              h' = set_as_mapping_image ts' (\<lambda>(q,x,y,q') . ((q,x),y,q'))
          in FSMWPI
             (initial_wpi M)
             (states_wpi M)
             (inputs_wpi M)
             (outputs_wpi M)
             ts'
             h'
             (h_obs_impl_from_h h'))
    else M)"

(* TODO: consider using Mapping.combine in add_transitions to avoid recomputation of h on the already known transitions *)

lift_definition add_transitions :: "('a,'b,'c) fsm_with_precomputations \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) set \<Rightarrow> ('a,'b,'c) fsm_with_precomputations"
  is add_transitions_impl
proof -
  fix M :: "('a,'b,'c) fsm_with_precomputations_impl"
  fix ts 

  let ?M = "(add_transitions_impl M ts)"

  show "well_formed_fsm_with_precomputations M \<Longrightarrow> well_formed_fsm_with_precomputations ?M"
  proof -
    assume assm: "well_formed_fsm_with_precomputations M"

    show "well_formed_fsm_with_precomputations ?M"
    proof (cases "(\<forall> t \<in> ts . t_source t \<in> states_wpi M \<and> t_input t \<in> inputs_wpi M \<and> t_output t \<in> outputs_wpi M \<and> t_target t \<in> states_wpi M)")
      case False
      then have "?M = M" by auto
      then show ?thesis using assm by presburger
    next
      case True
      then have "ts \<subseteq> states_wpi M \<times> inputs_wpi M \<times> outputs_wpi M \<times> states_wpi M" 
        by fastforce
      moreover have "finite (states_wpi M \<times> inputs_wpi M \<times> outputs_wpi M \<times> states_wpi M)" 
        using assm unfolding well_formed_fsm_with_precomputations.simps by blast
      ultimately have "finite ts"
        using rev_finite_subset by auto 

      have "initial_wpi ?M = initial_wpi M"
        unfolding add_transitions_impl.simps Let_def by auto
      have "states_wpi ?M = states_wpi M"
        unfolding add_transitions_impl.simps Let_def by auto
      have "inputs_wpi ?M = inputs_wpi M"
        unfolding add_transitions_impl.simps Let_def by auto
      have "outputs_wpi ?M = outputs_wpi M"
        unfolding add_transitions_impl.simps Let_def by auto
      have "transitions_wpi ?M = (transitions_wpi M) \<union> ts"
        using True unfolding add_transitions_impl.simps Let_def by auto
    
      define ts' where "ts' = ((transitions_wpi M) \<union> ts)"
      define h' where "h' = set_as_mapping_image ts' (\<lambda>(q,x,y,q') . ((q,x),y,q'))"

      have "h_wpi ?M = set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))"
        unfolding h'_def ts'_def using True unfolding add_transitions_impl.simps Let_def by auto
      have "h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)"
        unfolding h'_def ts'_def using True unfolding add_transitions_impl.simps Let_def by auto

      have base_props: "(initial_wpi ?M \<in> states_wpi ?M
                          \<and> finite (states_wpi ?M)
                          \<and> finite (inputs_wpi ?M)
                          \<and> finite (outputs_wpi ?M)
                          \<and> finite (transitions_wpi ?M))"
        using assm True \<open>finite ts\<close> unfolding add_transitions_impl.simps Let_def by auto
  

      have transition_prop: "(\<forall> t \<in> transitions_wpi ?M . t_source t \<in> states_wpi ?M \<and> 
                                      t_input t \<in> inputs_wpi ?M \<and> 
                                      t_target t \<in> states_wpi ?M \<and> 
                                      t_output t \<in> outputs_wpi ?M)"
        using assm True unfolding add_transitions_impl.simps Let_def by auto

      
      have h_prop:"\<And> qa x .
            (case Mapping.lookup (h_wpi ?M) (qa, x) of None \<Rightarrow> {} | Some ts \<Rightarrow> ts) =
            {a. case a of (y, q') \<Rightarrow> (qa, x, y, q') \<in> transitions_wpi ?M}"
      (is "\<And> qa x . ?A qa x = ?B qa x")
      proof -
        fix q x 
        show "?A q x = ?B q x"
        proof -

          have *:"Mapping.lookup (h_wpi ?M) = (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y,q')) (transitions_wpi ?M)))"
            unfolding \<open>h_wpi ?M = set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))\<close> using set_as_mapping_image_ob
            by auto 

          have **: "\<And> z . ((q, x), z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y, q')) ` (transitions_wpi ?M) = ((q,x,z) \<in> (transitions_wpi ?M))"
            by force

          show ?thesis 
            unfolding * set_as_map_def ** by force
        qed
      qed

      show ?thesis
        using base_props transition_prop h_prop well_formed_h_obs_impl_from_h[OF \<open>h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)\<close>]
        unfolding well_formed_fsm_with_precomputations.simps by blast
    qed
  qed
qed

lemma add_transitions_simps:
  "initial_wp (add_transitions M ts) = initial_wp M"
  "states_wp (add_transitions M ts) = states_wp M"
  "inputs_wp (add_transitions M ts) = inputs_wp M"
  "outputs_wp (add_transitions M ts) = outputs_wp M"
  "transitions_wp (add_transitions M ts) = (if (\<forall> t \<in> ts . t_source t \<in> states_wp M \<and> t_input t \<in> inputs_wp M \<and> t_output t \<in> outputs_wp M \<and> t_target t \<in> states_wp M)
                                          then transitions_wp M \<union> ts else transitions_wp M)"
  by (transfer; simp add: Let_def)+


declare [[code drop: FSM_Impl.add_transitions ]]
lemma add_transitions_with_precomputations_code [code] : "FSM_Impl.add_transitions ((FSMWP M)) ts = FSMWP (add_transitions M ts)"
  unfolding FSM_Impl.add_transitions.simps 
  unfolding fsm_impl_FSMWP_initial fsm_impl_FSMWP_states fsm_impl_FSMWP_inputs fsm_impl_FSMWP_outputs fsm_impl_FSMWP_transitions
  unfolding FSMWP_def
  unfolding add_transitions_simps  
  by presburger 



fun rename_states_impl :: "('a,'b,'c) fsm_with_precomputations_impl \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('d,'b,'c) fsm_with_precomputations_impl" where
  "rename_states_impl M f = (let ts = ((\<lambda>t . (f (t_source t), t_input t, t_output t, f (t_target t))) ` transitions_wpi M);
                                 h' = set_as_mapping_image ts (\<lambda>(q,x,y,q') . ((q,x),y,q'))
                             in
                              FSMWPI (f (initial_wpi M))
                                     (f ` states_wpi M)
                                     (inputs_wpi M)
                                     (outputs_wpi M)
                                     ts
                                     h'
                                     (h_obs_impl_from_h h'))"

lift_definition rename_states :: "('a,'b,'c) fsm_with_precomputations \<Rightarrow>('a \<Rightarrow> 'd) \<Rightarrow> ('d,'b,'c) fsm_with_precomputations"
  is rename_states_impl
proof -
  fix M :: "('a,'b,'c) fsm_with_precomputations_impl"
  fix f :: "('a \<Rightarrow> 'd)"

  let ?M = "(rename_states_impl M f)"

  show "well_formed_fsm_with_precomputations M \<Longrightarrow> well_formed_fsm_with_precomputations ?M"
  proof -
    assume assm: "well_formed_fsm_with_precomputations M"

    show "well_formed_fsm_with_precomputations ?M"
    proof -

      have "initial_wpi ?M = f (initial_wpi M)"
        unfolding rename_states_impl.simps Let_def by auto
      have "states_wpi ?M = f ` states_wpi M"
        unfolding rename_states_impl.simps Let_def by auto
      have "inputs_wpi ?M = inputs_wpi M"
        unfolding rename_states_impl.simps Let_def by auto
      have "outputs_wpi ?M = outputs_wpi M"
        unfolding rename_states_impl.simps Let_def by auto
      have "transitions_wpi ?M = ((\<lambda>t . (f (t_source t), t_input t, t_output t, f (t_target t))) ` transitions_wpi M)"
        unfolding rename_states_impl.simps Let_def by auto

      define ts where "ts = ((\<lambda>t . (f (t_source t), t_input t, t_output t, f (t_target t))) ` transitions_wpi M)"
      define h' where "h' = set_as_mapping_image ts (\<lambda>(q,x,y,q') . ((q,x),y,q'))"

      have "transitions_wpi ?M = ts"
        unfolding ts_def rename_states_impl.simps Let_def by auto
      then have "h_wpi ?M = set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))"
        unfolding h'_def unfolding rename_states_impl.simps Let_def by auto
      then have "h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)"
        unfolding rename_states_impl.simps Let_def by auto

      have base_props: "(initial_wpi ?M \<in> states_wpi ?M
                          \<and> finite (states_wpi ?M)
                          \<and> finite (inputs_wpi ?M)
                          \<and> finite (outputs_wpi ?M)
                          \<and> finite (transitions_wpi ?M))"
        using assm  unfolding rename_states_impl.simps Let_def by auto
  

      have transition_prop: "(\<forall> t \<in> transitions_wpi ?M . t_source t \<in> states_wpi ?M \<and> 
                                      t_input t \<in> inputs_wpi ?M \<and> 
                                      t_target t \<in> states_wpi ?M \<and> 
                                      t_output t \<in> outputs_wpi ?M)"
        using assm unfolding rename_states_impl.simps Let_def by auto


      show ?thesis
        using base_props transition_prop 
              well_formed_h_set_as_mapping[OF \<open>h_wpi ?M = set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))\<close>] 
              well_formed_h_obs_impl_from_h[OF \<open>h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)\<close>]
        unfolding well_formed_fsm_with_precomputations.simps by blast
    qed
  qed
qed


lemma rename_states_simps:
  "initial_wp (rename_states M f) = f (initial_wp M)"
  "states_wp (rename_states M f) = f ` states_wp M"
  "inputs_wp (rename_states M f) = inputs_wp M"
  "outputs_wp (rename_states M f) = outputs_wp M"
  "transitions_wp (rename_states M f) = ((\<lambda>t . (f (t_source t), t_input t, t_output t, f (t_target t))) ` transitions_wp M)"
  by (transfer; simp add: Let_def)+

declare [[code drop: FSM_Impl.rename_states ]]
lemma rename_states_with_precomputations_code[code] : "FSM_Impl.rename_states ((FSMWP M)) f = FSMWP (rename_states M f)"
  unfolding FSM_Impl.rename_states.simps 
  unfolding fsm_impl_FSMWP_initial fsm_impl_FSMWP_states fsm_impl_FSMWP_inputs fsm_impl_FSMWP_outputs fsm_impl_FSMWP_transitions
  unfolding FSMWP_def
  unfolding rename_states_simps  
  by presburger 


fun filter_transitions_impl :: "('a,'b,'c) fsm_with_precomputations_impl \<Rightarrow> (('a \<times> 'b \<times> 'c \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm_with_precomputations_impl" where
  "filter_transitions_impl M P = (let ts = (Set.filter P (transitions_wpi M));
                                            h' = (set_as_mapping_image ts (\<lambda>(q,x,y,q') . ((q,x),y,q')))
                                  in FSMWPI (initial_wpi M)
                                            (states_wpi M)
                                            (inputs_wpi M)
                                            (outputs_wpi M)
                                            ts
                                            h'
                                            (h_obs_impl_from_h h'))"

lift_definition filter_transitions :: "('a,'b,'c) fsm_with_precomputations \<Rightarrow> (('a \<times> 'b \<times> 'c \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm_with_precomputations"
  is filter_transitions_impl
proof -
  fix M :: "('a,'b,'c) fsm_with_precomputations_impl"
  fix P :: "(('a \<times> 'b \<times> 'c \<times> 'a) \<Rightarrow> bool) "

  let ?M = "filter_transitions_impl M P"

  show "well_formed_fsm_with_precomputations M \<Longrightarrow> well_formed_fsm_with_precomputations ?M"
  proof -
    assume assm: "well_formed_fsm_with_precomputations M"

    show "well_formed_fsm_with_precomputations ?M"
    proof -

      have "initial_wpi ?M = initial_wpi M"
        unfolding filter_transitions_impl.simps Let_def by auto
      have "states_wpi ?M = states_wpi M"
        unfolding filter_transitions_impl.simps Let_def by auto
      have "inputs_wpi ?M = inputs_wpi M"
        unfolding filter_transitions_impl.simps Let_def by auto
      have "outputs_wpi ?M = outputs_wpi M"
        unfolding filter_transitions_impl.simps Let_def by auto
      have "transitions_wpi ?M = (Set.filter P (transitions_wpi M))"
        unfolding filter_transitions_impl.simps Let_def by auto

      have "h_wpi ?M = (set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q')))"
        unfolding filter_transitions_impl.simps Let_def by auto
      then have "h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)"
        unfolding filter_transitions_impl.simps Let_def by auto

      have base_props: "(initial_wpi ?M \<in> states_wpi ?M
                          \<and> finite (states_wpi ?M)
                          \<and> finite (inputs_wpi ?M)
                          \<and> finite (outputs_wpi ?M)
                          \<and> finite (transitions_wpi ?M))"
        using assm  unfolding filter_transitions_impl.simps Let_def by auto
  

      have transition_prop: "(\<forall> t \<in> transitions_wpi ?M . t_source t \<in> states_wpi ?M \<and> 
                                      t_input t \<in> inputs_wpi ?M \<and> 
                                      t_target t \<in> states_wpi ?M \<and> 
                                      t_output t \<in> outputs_wpi ?M)"
        using assm unfolding filter_transitions_impl.simps Let_def by auto


      show ?thesis
        using base_props transition_prop 
              well_formed_h_set_as_mapping[OF \<open>h_wpi ?M = set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))\<close>] 
              well_formed_h_obs_impl_from_h[OF \<open>h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)\<close>]
        unfolding well_formed_fsm_with_precomputations.simps by blast
    qed
  qed
qed

lemma filter_transitions_simps:
  "initial_wp (filter_transitions M P) = initial_wp M"
  "states_wp (filter_transitions M P) = states_wp M"
  "inputs_wp (filter_transitions M P) = inputs_wp M"
  "outputs_wp (filter_transitions M P) = outputs_wp M"
  "transitions_wp (filter_transitions M P) = Set.filter P (transitions_wp M)"
  by (transfer; simp add: Let_def)+

declare [[code drop: FSM_Impl.filter_transitions ]]
lemma filter_transitions_with_precomputations_code [code] : "FSM_Impl.filter_transitions ((FSMWP M)) P = FSMWP (filter_transitions M P)"
  unfolding FSM_Impl.filter_transitions.simps 
  unfolding fsm_impl_FSMWP_initial fsm_impl_FSMWP_states fsm_impl_FSMWP_inputs fsm_impl_FSMWP_outputs fsm_impl_FSMWP_transitions
  unfolding FSMWP_def
  unfolding filter_transitions_simps  
  by presburger 


fun initial_singleton_impl :: "('a,'b,'c) fsm_with_precomputations_impl \<Rightarrow> ('a,'b,'c) fsm_with_precomputations_impl" where
  "initial_singleton_impl M = FSMWPI (initial_wpi M)
                                     {initial_wpi M}
                                     (inputs_wpi M)
                                     (outputs_wpi M)
                                     {}
                                     Mapping.empty 
                                     Mapping.empty"

lemma set_as_mapping_empty :
  "set_as_mapping_image {} f = Mapping.empty"
proof -
  obtain m where "set_as_mapping_image {} f = m" and "Mapping.lookup m = set_as_map (f ` {})"
    using set_as_mapping_image_ob by blast
  then have "\<And> k . Mapping.lookup m k = None"
    unfolding set_as_map_def
    by simp 
  then show ?thesis
    unfolding \<open>set_as_mapping_image {} f = m\<close>
    by (simp add: mapping_eqI) 
qed

lemma h_obs_from_impl_h : "h_obs_impl_from_h Mapping.empty = Mapping.empty"
  unfolding h_obs_impl_from_h.simps
  by (simp add: map_values_empty)

lift_definition initial_singleton :: "('a,'b,'c) fsm_with_precomputations \<Rightarrow> ('a,'b,'c) fsm_with_precomputations"
  is initial_singleton_impl
proof -
  fix M :: "('a,'b,'c) fsm_with_precomputations_impl"

  let ?M = "initial_singleton_impl M"

  show "well_formed_fsm_with_precomputations M \<Longrightarrow> well_formed_fsm_with_precomputations ?M"
  proof -
    assume assm: "well_formed_fsm_with_precomputations M"

    show "well_formed_fsm_with_precomputations ?M"
    proof -

      have "transitions_wpi ?M = {}"
        unfolding filter_transitions_impl.simps Let_def by auto

      have "h_wpi ?M = Mapping.empty" and "h_obs_wpi ?M = Mapping.empty"
        unfolding filter_transitions_impl.simps Let_def by auto
      have "h_wpi ?M = (set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q')))"
        unfolding \<open>h_wpi ?M = Mapping.empty\<close> \<open>transitions_wpi ?M = {}\<close>
        unfolding set_as_mapping_empty by presburger
      have "h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)"
        unfolding \<open>h_wpi ?M = Mapping.empty\<close> \<open>h_obs_wpi ?M = Mapping.empty\<close>
        unfolding h_obs_from_impl_h by simp

      have base_props: "(initial_wpi ?M \<in> states_wpi ?M
                          \<and> finite (states_wpi ?M)
                          \<and> finite (inputs_wpi ?M)
                          \<and> finite (outputs_wpi ?M)
                          \<and> finite (transitions_wpi ?M))"
        using assm  unfolding filter_transitions_impl.simps Let_def by auto
  

      have transition_prop: "(\<forall> t \<in> transitions_wpi ?M . t_source t \<in> states_wpi ?M \<and> 
                                      t_input t \<in> inputs_wpi ?M \<and> 
                                      t_target t \<in> states_wpi ?M \<and> 
                                      t_output t \<in> outputs_wpi ?M)"
        using assm unfolding filter_transitions_impl.simps Let_def by auto


      show ?thesis
        using base_props transition_prop 
              well_formed_h_set_as_mapping[OF \<open>h_wpi ?M = set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))\<close>] 
              well_formed_h_obs_impl_from_h[OF \<open>h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)\<close>]
        unfolding well_formed_fsm_with_precomputations.simps by blast
    qed
  qed
qed

lemma initial_singleton_simps:
  "initial_wp (initial_singleton M) = initial_wp M"
  "states_wp (initial_singleton M) = {initial_wp M}"
  "inputs_wp (initial_singleton M) = inputs_wp M"
  "outputs_wp (initial_singleton M) = outputs_wp M"
  "transitions_wp (initial_singleton M) = {}"
  by (transfer; simp add: Let_def)+

declare [[code drop: FSM_Impl.initial_singleton]]
lemma initial_singleton_with_precomputations_code[code] : "FSM_Impl.initial_singleton ((FSMWP M)) = FSMWP (initial_singleton M)"
  unfolding FSM_Impl.initial_singleton.simps 
  unfolding fsm_impl_FSMWP_initial fsm_impl_FSMWP_states fsm_impl_FSMWP_inputs fsm_impl_FSMWP_outputs fsm_impl_FSMWP_transitions
  unfolding FSMWP_def
  unfolding initial_singleton_simps  
  by presburger 


fun canonical_separator'_impl :: "('a,'b,'c) fsm_with_precomputations_impl \<Rightarrow> (('a \<times> 'a),'b,'c) fsm_with_precomputations_impl \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b,'c) fsm_with_precomputations_impl" where
  "canonical_separator'_impl M P q1 q2 = (if initial_wpi P = (q1,q2) 
  then
    (let f'  = set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (transitions_wpi M));
         f   = (\<lambda>qx . (case f' qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}));
         shifted_transitions' = shifted_transitions (transitions_wpi P);
         distinguishing_transitions_lr = distinguishing_transitions f q1 q2 (states_wpi P) (inputs_wpi P);
         ts = shifted_transitions' \<union> distinguishing_transitions_lr;
         h' = set_as_mapping_image ts (\<lambda>(q,x,y,q') . ((q,x),y,q'))
     in 
  
      FSMWPI (Inl (q1,q2))
      ((image Inl (states_wpi P)) \<union> {Inr q1, Inr q2})
      (inputs_wpi M \<union> inputs_wpi P)
      (outputs_wpi M \<union> outputs_wpi P)
      ts
      h'
      (h_obs_impl_from_h h'))
  else FSMWPI (Inl (q1,q2)) {Inl (q1,q2)} {} {} {} Mapping.empty Mapping.empty)"

lemma canonical_separator'_impl_refined[code]:
  "canonical_separator'_impl M P q1 q2 = (if initial_wpi P = (q1,q2) 
  then
    (let f'  = set_as_mapping_image (transitions_wpi M) (\<lambda>(q,x,y,q') . ((q,x),y));
         f   = (\<lambda>qx . (case Mapping.lookup f' qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}));
         shifted_transitions' = shifted_transitions (transitions_wpi P);
         distinguishing_transitions_lr = distinguishing_transitions f q1 q2 (states_wpi P) (inputs_wpi P);
         ts = shifted_transitions' \<union> distinguishing_transitions_lr;
         h' = set_as_mapping_image ts (\<lambda>(q,x,y,q') . ((q,x),y,q'))
     in 
  
      FSMWPI (Inl (q1,q2))
      ((image Inl (states_wpi P)) \<union> {Inr q1, Inr q2})
      (inputs_wpi M \<union> inputs_wpi P)
      (outputs_wpi M \<union> outputs_wpi P)
      ts
      h'
      (h_obs_impl_from_h h'))
  else FSMWPI (Inl (q1,q2)) {Inl (q1,q2)} {} {} {} Mapping.empty Mapping.empty)"
  unfolding canonical_separator'_impl.simps 
  using set_as_mapping_image_ob[of "(transitions_wpi M)" "(\<lambda>(q,x,y,q') . ((q,x),y))"]
  by fastforce


lift_definition canonical_separator' :: "('a,'b,'c) fsm_with_precomputations \<Rightarrow> (('a \<times> 'a),'b,'c) fsm_with_precomputations \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b,'c) fsm_with_precomputations"
  is canonical_separator'_impl
proof -
  fix M :: "('a,'b,'c) fsm_with_precomputations_impl"
  fix P q1 q2
  show "well_formed_fsm_with_precomputations M \<Longrightarrow> well_formed_fsm_with_precomputations P \<Longrightarrow> well_formed_fsm_with_precomputations (canonical_separator'_impl M P q1 q2)"
  proof -
    assume a1: "well_formed_fsm_with_precomputations M"
    assume a2: "well_formed_fsm_with_precomputations P"

    let ?M = "canonical_separator'_impl M P q1 q2"

    show "well_formed_fsm_with_precomputations ?M"
    proof (cases "initial_wpi P = (q1,q2)")
      case False

      have "h_wpi ?M = Mapping.empty" and "h_obs_wpi ?M = Mapping.empty" and "transitions_wpi ?M = {}"
        using False unfolding canonical_separator'_impl.simps Let_def by auto
      have "h_wpi ?M = (set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q')))"
        unfolding \<open>h_wpi ?M = Mapping.empty\<close> \<open>transitions_wpi ?M = {}\<close>
        unfolding set_as_mapping_empty by presburger
      have "h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)"
        unfolding \<open>h_wpi ?M = Mapping.empty\<close> \<open>h_obs_wpi ?M = Mapping.empty\<close>
        unfolding h_obs_from_impl_h by simp

      have base_props: "(initial_wpi ?M \<in> states_wpi ?M
                          \<and> finite (states_wpi ?M)
                          \<and> finite (inputs_wpi ?M)
                          \<and> finite (outputs_wpi ?M)
                          \<and> finite (transitions_wpi ?M))"
        using a1 False unfolding canonical_separator'_impl.simps Let_def by auto
  

      have transition_prop: "(\<forall> t \<in> transitions_wpi ?M . t_source t \<in> states_wpi ?M \<and> 
                                      t_input t \<in> inputs_wpi ?M \<and> 
                                      t_target t \<in> states_wpi ?M \<and> 
                                      t_output t \<in> outputs_wpi ?M)"
        using a1 False unfolding canonical_separator'_impl.simps Let_def by auto


      show ?thesis
        using base_props transition_prop 
              well_formed_h_set_as_mapping[OF \<open>h_wpi ?M = set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))\<close>] 
              well_formed_h_obs_impl_from_h[OF \<open>h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)\<close>]
        unfolding well_formed_fsm_with_precomputations.simps by blast
    next
      case True

      let ?f = "(\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (transitions_wpi M))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  
      have "\<And> qx . (\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (transitions_wpi M))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {})) qx = (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` transitions_wpi M}) qx"
        by (metis (mono_tags, lifting) Collect_cong Collect_mem_eq set_as_map_containment set_as_map_elem)
      moreover have "\<And> qx . (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` transitions_wpi M}) qx = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> transitions_wpi M}) qx"
        by force
      ultimately have *:" ?f = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> transitions_wpi M})" 
        by blast
        
      let ?shifted_transitions' = "shifted_transitions (transitions_wpi P)"
      let ?distinguishing_transitions_lr = "distinguishing_transitions ?f q1 q2 (states_wpi P) (inputs_wpi P)"
      let ?ts = "?shifted_transitions' \<union> ?distinguishing_transitions_lr"
    
      have "states_wpi ?M = (image Inl (states_wpi P)) \<union> {Inr q1, Inr q2}"
      and  "transitions_wpi ?M = ?ts"
        unfolding canonical_separator'_impl.simps Let_def True by simp+
  
      have p2: "finite (states_wpi ?M)"
        unfolding \<open>states_wpi ?M = (image Inl (states_wpi P)) \<union> {Inr q1, Inr q2}\<close> using a2 by auto
    
      have "initial_wpi ?M = Inl (q1,q2)" by auto
      then have p1: "initial_wpi ?M \<in> states_wpi ?M" 
        using a1 a2 unfolding canonical_separator'.simps True by auto
      have p3: "finite (inputs_wpi ?M)"
        using a1 a2 by auto
      have p4: "finite (outputs_wpi ?M)"
        using a1 a2 by auto
  
      have "finite (states_wpi P \<times> inputs_wpi P)"
        using a2 by auto
      moreover have **: "\<And> x q1 . finite ({y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> transitions_wpi M})"
      proof - 
        fix x q1
        have "{y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> transitions_wpi M} = {t_output t | t . t \<in> transitions_wpi M \<and> t_source t = q1 \<and> t_input t = x}"
          by auto
        then have "{y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> transitions_wpi M} \<subseteq> image t_output (transitions_wpi M)"
          unfolding fst_conv snd_conv by blast
        moreover have "finite (image t_output (transitions_wpi M))"
          using a1 by auto
        ultimately show "finite ({y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> transitions_wpi M})"
          by (simp add: finite_subset)
      qed
      ultimately have "finite ?distinguishing_transitions_lr"
        unfolding * distinguishing_transitions_def by force
      moreover have "finite ?shifted_transitions'"
        unfolding shifted_transitions_def using a2 by auto
      ultimately have "finite ?ts" by blast
      then have p5: "finite (transitions_wpi ?M)"
        by simp
       
      have "inputs_wpi ?M = inputs_wpi M \<union> inputs_wpi P"
        using True by auto
      have "outputs_wpi ?M = outputs_wpi M \<union> outputs_wpi P "
        using True by auto
    
      have "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_source t \<in> states_wpi ?M \<and> t_target t \<in> states_wpi ?M"
        unfolding \<open>states_wpi ?M = (image Inl (states_wpi P)) \<union> {Inr q1, Inr q2}\<close> shifted_transitions_def 
        using a2 by auto
      moreover have "\<And> t . t \<in> ?distinguishing_transitions_lr \<Longrightarrow> t_source t \<in> states_wpi ?M \<and> t_target t \<in> states_wpi ?M"
        unfolding \<open>states_wpi ?M = (image Inl (states_wpi P)) \<union> {Inr q1, Inr q2}\<close> distinguishing_transitions_def * by force
      ultimately have "\<And> t . t \<in> ?ts \<Longrightarrow> t_source t \<in> states_wpi ?M \<and> t_target t \<in> states_wpi ?M"
        by blast
      moreover have "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_input t \<in> inputs_wpi ?M \<and> t_output t \<in> outputs_wpi ?M"
      proof -
        have "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_input t \<in> inputs_wpi P \<and> t_output t \<in> outputs_wpi P"
          unfolding shifted_transitions_def using a2 by auto
        then show "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_input t \<in> inputs_wpi ?M \<and> t_output t \<in> outputs_wpi ?M"
          unfolding \<open>inputs_wpi ?M = inputs_wpi M \<union> inputs_wpi P\<close>
                    \<open>outputs_wpi ?M = outputs_wpi M \<union> outputs_wpi P\<close> by blast
      qed
      moreover have "\<And> t . t \<in> ?distinguishing_transitions_lr \<Longrightarrow> t_input t \<in> inputs_wpi ?M \<and> t_output t \<in> outputs_wpi ?M"
        unfolding * distinguishing_transitions_def using a1 a2 True by auto
      ultimately have p6: "(\<forall>t\<in>transitions_wpi ?M.
                t_source t \<in> states_wpi ?M \<and>
                t_input t \<in> inputs_wpi ?M \<and> t_target t \<in> states_wpi ?M \<and>
                                                 t_output t \<in> outputs_wpi ?M)"
        unfolding \<open>transitions_wpi ?M = ?ts\<close> by blast
  
      have "h_wpi ?M = set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))"
       and "h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)"
        using True unfolding canonical_separator'_impl.simps Let_def by auto
  
      show "well_formed_fsm_with_precomputations ?M"
        using p1 p2 p3 p4 p5 p6 
        using well_formed_h_set_as_mapping[OF \<open>h_wpi ?M = set_as_mapping_image (transitions_wpi ?M) (\<lambda>(q,x,y,q') . ((q,x),y,q'))\<close>] 
              well_formed_h_obs_impl_from_h[OF \<open>h_obs_wpi ?M = h_obs_impl_from_h (h_wpi ?M)\<close>]
        unfolding well_formed_fsm_with_precomputations.simps by blast
    qed
  qed
qed

lemma canonical_separator'_simps :
        "initial_wp (canonical_separator' M P q1 q2) = Inl (q1,q2)"
        "states_wp (canonical_separator' M P q1 q2) = (if initial_wp P = (q1,q2) then (image Inl (states_wp P)) \<union> {Inr q1, Inr q2} else {Inl (q1,q2)})"
        "inputs_wp (canonical_separator' M P q1 q2) = (if initial_wp P = (q1,q2) then inputs_wp M \<union> inputs_wp P else {})"
        "outputs_wp (canonical_separator' M P q1 q2) = (if initial_wp P = (q1,q2) then outputs_wp M \<union> outputs_wp P else {})"
        "transitions_wp (canonical_separator' M P q1 q2) = (if initial_wp P = (q1,q2) then shifted_transitions (transitions_wp P) \<union> distinguishing_transitions (\<lambda> (q,x) . {y . \<exists> q' . (q,x,y,q') \<in> transitions_wp M}) q1 q2 (states_wp P) (inputs_wp P) else {})"
  unfolding h_out_impl_helper by (transfer; simp add: Let_def)+


declare [[code drop: FSM_Impl.canonical_separator']]
lemma canonical_separator_with_precomputations_code [code] : "FSM_Impl.canonical_separator' ((FSMWP M)) ((FSMWP P)) q1 q2 = FSMWP (canonical_separator' M P q1 q2)"
proof -

  have *:"\<And> M1 M2 . (M1 = M2) = (fsm_impl.initial M1 = fsm_impl.initial M2 
                                \<and> fsm_impl.states M1 = fsm_impl.states M2 
                                \<and> fsm_impl.inputs M1 = fsm_impl.inputs M2 
                                \<and> fsm_impl.outputs M1 = fsm_impl.outputs M2 
                                \<and> fsm_impl.transitions M1 = fsm_impl.transitions M2 )"
    by (meson fsm_impl.expand)

  show ?thesis
    unfolding *
    unfolding FSM_Impl.canonical_separator'_simps
    unfolding fsm_impl_FSMWP_initial fsm_impl_FSMWP_states fsm_impl_FSMWP_inputs fsm_impl_FSMWP_outputs fsm_impl_FSMWP_transitions
    unfolding canonical_separator'_simps  
    by blast
qed


fun product_impl :: "('a,'b,'c) fsm_with_precomputations_impl \<Rightarrow> ('d,'b,'c) fsm_with_precomputations_impl \<Rightarrow> ('a \<times> 'd,'b,'c) fsm_with_precomputations_impl" where
  "product_impl A B = (let ts = (image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) (Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions_wpi B)) (transitions_wpi A)))));
                           h' = set_as_mapping_image ts (\<lambda>(q,x,y,q') . ((q,x),y,q'))
                        in
                          FSMWPI ((initial_wpi A, initial_wpi B))
                                 ((states_wpi A) \<times> (states_wpi B))
                                 (inputs_wpi A \<union> inputs_wpi B)
                                 (outputs_wpi A \<union> outputs_wpi B)
                                 ts
                                 h'
                                 (h_obs_impl_from_h h'))"
                                       
lift_definition product :: "('a,'b,'c) fsm_with_precomputations \<Rightarrow> ('d,'b,'c) fsm_with_precomputations \<Rightarrow> ('a \<times> 'd,'b,'c) fsm_with_precomputations" is product_impl 
proof -
  fix A :: "('a,'b,'c) fsm_with_precomputations_impl"
  fix B :: "('d,'b,'c) fsm_with_precomputations_impl"
  assume a1: "well_formed_fsm_with_precomputations A" and a2: "well_formed_fsm_with_precomputations B"

  let ?P = "product_impl A B"

  have "(\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions_wpi B)) (transitions_wpi A))) = {(tA,tB) | tA tB . tA \<in> transitions_wpi A \<and> tB \<in> transitions_wpi B}"
    by auto
  then have "(Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions_wpi B)) (transitions_wpi A)))) = {((qA,x,y,qA'),(qB,x,y,qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions_wpi A \<and> (qB,x,y,qB') \<in> transitions_wpi B}"
    by auto
  then have "image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) (Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions_wpi B)) (transitions_wpi A)))) 
              = image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) {((qA,x,y,qA'),(qB,x,y,qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions_wpi A \<and> (qB,x,y,qB') \<in> transitions_wpi B}"
    by auto
  then have "transitions_wpi ?P = image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) {((qA,x,y,qA'),(qB,x,y,qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions_wpi A \<and> (qB,x,y,qB') \<in> transitions_wpi B}"
    by auto
  also have "\<dots> =  {((qA,qB),x,y,(qA',qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions_wpi A \<and> (qB,x,y,qB') \<in> transitions_wpi B}"
    by force
  finally have "transitions_wpi ?P = {((qA,qB),x,y,(qA',qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions_wpi A \<and> (qB,x,y,qB') \<in> transitions_wpi B}" .
  
  have "h_wpi ?P = set_as_mapping_image (transitions_wpi ?P) (\<lambda>(q,x,y,q') . ((q,x),y,q'))"
   and "h_obs_wpi ?P = h_obs_impl_from_h (h_wpi ?P)"
    unfolding canonical_separator'_impl.simps Let_def by auto
  
  have "initial_wpi ?P \<in> states_wpi ?P" 
    using a1 a2 by auto
  moreover have "finite (states_wpi ?P)"
    using a1 a2 by auto
  moreover have "finite (inputs_wpi ?P)"
    using a1 a2 by auto
  moreover have "finite (outputs_wpi ?P)"
    using a1 a2 by auto
  moreover have "finite (transitions_wpi ?P)"
    using a1 a2 unfolding product_code_naive by auto
  moreover have "(\<forall>t\<in>transitions_wpi ?P.
            t_source t \<in> states_wpi ?P \<and>
            t_input t \<in> inputs_wpi ?P \<and> t_target t \<in> states_wpi ?P \<and>
                                             t_output t \<in> outputs_wpi ?P)"
    using a1 a2 unfolding well_formed_fsm_with_precomputations.simps
    unfolding \<open>transitions_wpi ?P = {((qA,qB),x,y,(qA',qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions_wpi A \<and> (qB,x,y,qB') \<in> transitions_wpi B}\<close> 
    by fastforce
  ultimately show "well_formed_fsm_with_precomputations ?P"
    using well_formed_h_set_as_mapping[OF \<open>h_wpi ?P = set_as_mapping_image (transitions_wpi ?P) (\<lambda>(q,x,y,q') . ((q,x),y,q'))\<close>] 
          well_formed_h_obs_impl_from_h[OF \<open>h_obs_wpi ?P = h_obs_impl_from_h (h_wpi ?P)\<close>]
    unfolding well_formed_fsm_with_precomputations.simps by blast
qed

lemma product_simps:
  "initial_wp (product A B) = (initial_wp A, initial_wp B)"  
  "states_wp (product A B) = (states_wp A) \<times> (states_wp B)"
  "inputs_wp (product A B) = inputs_wp A \<union> inputs_wp B"
  "outputs_wp (product A B) = outputs_wp A \<union> outputs_wp B"  
  "transitions_wp (product A B) = (image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) (Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions_wp B)) (transitions_wp A)))))"
  by (transfer; simp)+

declare [[code drop: FSM_Impl.product]]
lemma product_with_precomputations_code [code] : "FSM_Impl.product ((FSMWP A)) ((FSMWP B)) = FSMWP (product A B)"
  unfolding FSM_Impl.product_code_naive 
  unfolding fsm_impl_FSMWP_initial fsm_impl_FSMWP_states fsm_impl_FSMWP_inputs fsm_impl_FSMWP_outputs fsm_impl_FSMWP_transitions
  unfolding FSMWP_def
  unfolding product_simps  
  by presburger 


fun from_FSMI_impl :: "('a,'b,'c) fsm_with_precomputations_impl \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) fsm_with_precomputations_impl" where
  "from_FSMI_impl M q = (if q \<in> states_wpi M then FSMWPI q (states_wpi M) (inputs_wpi M) (outputs_wpi M) (transitions_wpi M) (h_wpi M) (h_obs_wpi M) else M)"

lift_definition from_FSMI :: "('a,'b,'c) fsm_with_precomputations \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) fsm_with_precomputations" is from_FSMI_impl  
proof -
  fix M :: "('a,'b,'c) fsm_with_precomputations_impl"
  fix q
  assume "well_formed_fsm_with_precomputations M"
  then show "well_formed_fsm_with_precomputations (from_FSMI_impl M q)"
    by (cases "q \<in> states_wpi M"; auto)
qed

lemma from_FSMI_simps:
  "initial_wp (from_FSMI M q) = (if q \<in> states_wp M then q else initial_wp M)"
  "states_wp (from_FSMI M q) = states_wp M"
  "inputs_wp (from_FSMI M q) = inputs_wp M"
  "outputs_wp (from_FSMI M q) = outputs_wp M"
  "transitions_wp (from_FSMI M q) = transitions_wp M"
  by (transfer; simp add: Let_def)+

declare [[code drop: FSM_Impl.from_FSMI]]
lemma from_FSMI_with_precomputations_code [code] : "FSM_Impl.from_FSMI ((FSMWP M)) q = FSMWP (from_FSMI M q)"
  unfolding FSM_Impl.from_FSMI.simps 
  unfolding fsm_impl_FSMWP_initial fsm_impl_FSMWP_states fsm_impl_FSMWP_inputs fsm_impl_FSMWP_outputs fsm_impl_FSMWP_transitions
  unfolding FSMWP_def
  unfolding from_FSMI_simps  
  by presburger 

end