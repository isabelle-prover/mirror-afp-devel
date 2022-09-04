section \<open>Maximal Path Tries\<close>

text \<open>Drastically reduced implementation of tries that consider only maximum length sequences as elements.
      Inserting a sequence that is prefix of some already contained sequence does not alter the trie.
      Intended to store IO-sequences to apply in testing, as in this use-case proper prefixes need not be applied separately.\<close>

theory Maximal_Path_Trie
imports "../Util"
begin

subsection \<open>Utils for Updating Associative Lists\<close>

fun update_assoc_list_with_default :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "update_assoc_list_with_default k f d [] = [(k,f d)]" |
  "update_assoc_list_with_default k f d ((x,y)#xys) = (if k = x
    then ((x,f y)#xys)
    else (x,y) # (update_assoc_list_with_default k f d xys))"

lemma update_assoc_list_with_default_key_found :
  assumes "distinct (map fst xys)"
  and     "i < length xys"
  and     "fst (xys ! i) = k"
shows "update_assoc_list_with_default k f d xys =
        ((take i xys) @ [(k, f (snd (xys ! i)))] @ (drop (Suc i) xys))" 
using assms proof (induction xys arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons a xys)
  
  show ?case
  proof (cases i)
    case 0
    then have "fst a = k" using Cons.prems(3) by auto
    then have "update_assoc_list_with_default k f d (a#xys) = (k, f (snd a)) # xys"
      unfolding 0 by (metis prod.collapse update_assoc_list_with_default.simps(2)) 
    then show ?thesis unfolding 0 by auto
  next
    case (Suc j)
    then have "fst a \<noteq> k"
      using Cons.prems by auto 

    have "distinct (map fst xys)"
    and  "j < length xys"
    and  "fst (xys ! j) = k"
      using Cons.prems unfolding Suc by auto

    then have "update_assoc_list_with_default k f d xys = take j xys @ [(k, f (snd (xys ! j)))] @ drop (Suc j) xys"
      using Cons.IH[of j] by auto

    then show ?thesis unfolding Suc using \<open>fst a \<noteq> k\<close>
      by (metis append_Cons drop_Suc_Cons nth_Cons_Suc prod.collapse take_Suc_Cons update_assoc_list_with_default.simps(2)) 
  qed 
qed 

lemma update_assoc_list_with_default_key_not_found :
  assumes "distinct (map fst xys)"
  and     "k \<notin> set (map fst xys)"
shows "update_assoc_list_with_default k f d xys = xys @ [(k,f d)]"  
  using assms by (induction xys; auto)


lemma update_assoc_list_with_default_key_distinct :
  assumes "distinct (map fst xys)"
  shows "distinct (map fst (update_assoc_list_with_default k f d xys))"
proof (cases "k \<in> set (map fst xys)")
  case True
  then obtain i where "i < length xys" and "fst (xys ! i) = k"
    by (metis in_set_conv_nth length_map nth_map) 
  then have *: "(map fst (take i xys @ [(k, f (snd (xys ! i)))] @ drop (Suc i) xys)) = (map fst xys)"
  proof -
    have "xys ! i # drop (Suc i) xys = drop i xys"
      using Cons_nth_drop_Suc \<open>i < length xys\<close> by blast
    then show ?thesis
      by (metis (no_types) \<open>fst (xys ! i) = k\<close> append_Cons append_self_conv2 append_take_drop_id fst_conv list.simps(9) map_append)
  qed
  show ?thesis
    unfolding update_assoc_list_with_default_key_found[OF assms \<open>i < length xys\<close> \<open>fst (xys ! i) = k\<close>] * 
    using assms by assumption
next
  case False
  have *: "(map fst (xys @ [(k, f d)])) = (map fst xys)@[k]" by auto
  show ?thesis
    using assms False
    unfolding update_assoc_list_with_default_key_not_found[OF assms False] * by auto
qed






subsection \<open>Maximum Path Trie Implementation\<close>


datatype 'a mp_trie = MP_Trie "('a \<times> 'a mp_trie) list"

fun mp_trie_invar :: "'a mp_trie \<Rightarrow> bool" where
  "mp_trie_invar (MP_Trie ts) = (distinct (map fst ts) \<and> (\<forall> t \<in> set (map snd ts) . mp_trie_invar t))"



definition empty :: "'a mp_trie" where
  "empty = MP_Trie []"

lemma empty_invar : "mp_trie_invar empty" unfolding empty_def by auto



fun height :: "'a mp_trie \<Rightarrow> nat" where
  "height (MP_Trie []) = 0" |
  "height (MP_Trie (xt#xts)) = Suc (foldr (\<lambda> t m . max (height t) m) (map snd (xt#xts)) 0)"

lemma height_0 : 
  assumes "height t = 0" 
  shows "t = empty" 
proof (rule ccontr)
  assume "t \<noteq> empty"
  then obtain xt xts where "t = MP_Trie (xt#xts)"
    by (metis empty_def height.cases)
  have "height t > 0" 
    unfolding \<open>t = MP_Trie (xt#xts)\<close> height.simps
    by simp
  then show "False"
    using assms by simp
qed


lemma height_inc :
  assumes "t \<in> set (map snd ts)"
  shows "height t < height (MP_Trie ts)"
proof -
  obtain xt xts where "ts = xt#xts"
    using assms
    by (metis list.set_cases list_map_source_elem) 
  
  have "height t < Suc (foldr (\<lambda> t m . max (height t) m) (map snd (xt#xts)) 0)"
    using assms unfolding \<open>ts = xt#xts\<close> using max_by_foldr[of t "(map snd (xt#xts))" height] 
    by blast

  then show ?thesis unfolding \<open>ts = xt#xts\<close> by auto
qed


fun insert :: "'a list \<Rightarrow> 'a mp_trie \<Rightarrow> 'a mp_trie" where
  "insert [] t = t" |
  "insert (x#xs) (MP_Trie ts) = (MP_Trie (update_assoc_list_with_default x (\<lambda> t . insert xs t) empty ts))"


lemma insert_invar : "mp_trie_invar t \<Longrightarrow> mp_trie_invar (insert xs t)" 
proof (induction xs arbitrary: t)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)

  obtain ts where "t = MP_Trie ts"
    using mp_trie_invar.cases by auto

  then have "distinct (map fst ts)"
       and  "\<And> t . t \<in> set (map snd ts) \<Longrightarrow> mp_trie_invar t"
    using Cons.prems by auto
    
  
  show ?case proof (cases "x \<in> set (map fst ts)")
    case True
    then obtain i where "i < length ts" and "fst (ts ! i) = x"
      by (metis in_set_conv_nth length_map nth_map) 
    have "insert (x#xs) (MP_Trie ts) = (MP_Trie (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts))"
      unfolding insert.simps empty_def
      unfolding update_assoc_list_with_default_key_found[OF \<open>distinct (map fst ts)\<close> \<open>i < length ts\<close> \<open>fst (ts ! i) = x\<close>
                                                        ,of "(\<lambda> t . insert xs t)" "(MP_Trie [])"] 
      by simp
    
    have "\<And> t . t \<in> set (map snd (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts)) \<Longrightarrow> mp_trie_invar t"
    proof - 
      fix t assume "t \<in> set (map snd (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts))"
      then consider (a) "t \<in> set (map snd (take i ts @ drop (Suc i) ts))" |
                    (b) "t = insert xs (snd (ts ! i))" 
        by auto
      then show "mp_trie_invar t" proof cases
        case a
        then have "t \<in> set (map snd ts)"
          by (metis drop_map in_set_dropD in_set_takeD list_concat_non_elem map_append take_map) 
        then show ?thesis using \<open>\<And> t . t \<in> set (map snd ts) \<Longrightarrow> mp_trie_invar t\<close> by blast
      next
        case b
        have "(snd (ts ! i)) \<in> set (map snd ts)"
          using \<open>i < length ts\<close> by auto
        then have "mp_trie_invar (snd (ts ! i))" using \<open>\<And> t . t \<in> set (map snd ts) \<Longrightarrow> mp_trie_invar t\<close> by blast 
        then show ?thesis using Cons.IH unfolding b by blast
      qed 
    qed
    moreover have "distinct (map fst (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts))"
      using update_assoc_list_with_default_key_distinct[OF \<open>distinct (map fst ts)\<close>]
      by (metis \<open>distinct (map fst ts)\<close> \<open>fst (ts ! i) = x\<close> \<open>i < length ts\<close> update_assoc_list_with_default_key_found)
    
    ultimately show ?thesis 
      unfolding \<open>t = MP_Trie ts\<close> \<open>insert (x#xs) (MP_Trie ts) = (MP_Trie (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts))\<close>
      by auto
  next
    case False

    have "mp_trie_invar (insert xs empty)"
      by (simp add: empty_invar Cons.IH) 

    then show ?thesis
      using Cons.prems update_assoc_list_with_default_key_distinct[OF \<open>distinct (map fst ts)\<close>, of x "(insert xs)" "(MP_Trie [])"]
      unfolding \<open>t = MP_Trie ts\<close> insert.simps
      unfolding update_assoc_list_with_default_key_not_found[OF \<open>distinct (map fst ts)\<close> False] 
      by auto
  qed
qed 




fun paths :: "'a mp_trie \<Rightarrow> 'a list list" where
  "paths (MP_Trie []) = [[]]" |
  "paths (MP_Trie (t#ts)) = concat (map (\<lambda> (x,t) . map ((#) x) (paths t)) (t#ts))"



lemma paths_empty :
  assumes "[] \<in> set (paths t)"
  shows "t = empty"
proof (rule ccontr)
  assume "t \<noteq> empty"
  then obtain xt xts where "t = MP_Trie (xt#xts)"
    by (metis empty_def height.cases)
  then have "[] \<in> set (concat (map (\<lambda> (x,t) . map ((#) x) (paths t)) (xt#xts)))"
    using assms by auto
  then show "False" by auto
qed

lemma paths_nonempty :
  assumes "[] \<notin> set (paths t)"
  shows "set (paths t) \<noteq> {}"
using assms proof (induction t rule: mp_trie_invar.induct)
  case (1 ts)
  have "ts \<noteq> []" using "1.prems" by auto
  then obtain x t xts where "ts = ((x,t)#xts)"
    using linear_order_from_list_position'.cases
    by (metis old.prod.exhaust) 
  
  then have "t \<in> set (map snd ts)" by auto
    
  show ?case 
  proof (cases "[] \<in> set (paths t)")
    case True
    then show ?thesis  
      unfolding \<open>ts = ((x,t)#xts)\<close> paths.simps by auto
  next
    case False
    show ?thesis 
      using "1.IH"[OF \<open>t \<in> set (map snd ts)\<close> False]  
      unfolding \<open>ts = ((x,t)#xts)\<close> paths.simps by auto
  qed
qed


lemma paths_maximal: "mp_trie_invar t \<Longrightarrow> xs' \<in> set (paths t) \<Longrightarrow> \<not> (\<exists> xs'' . xs'' \<noteq> [] \<and> xs'@xs'' \<in> set (paths t))"
proof (induction xs' arbitrary: t)
  case Nil
  then have "t = empty"
    using paths_empty by blast
  then have "paths t = [[]]"
    by (simp add: empty_def)
  then show ?case by auto
next
  case (Cons x xs')

  then have "t \<noteq> empty" unfolding empty_def by auto
  then obtain xt xts where "t = MP_Trie (xt#xts)"
    by (metis empty_def height.cases)

  obtain t' where "(x,t') \<in> set (xt#xts)"
            and   "xs' \<in> set (paths t')"
    using Cons.prems(2) 
    unfolding \<open>t = MP_Trie (xt#xts)\<close> paths.simps 
    by force

  have "mp_trie_invar t'"
    using Cons.prems(1) \<open>(x,t') \<in> set (xt#xts)\<close> unfolding \<open>t = MP_Trie (xt#xts)\<close> by auto

  show ?case 
  proof 
    assume "\<exists>xs''. xs'' \<noteq> [] \<and> (x # xs') @ xs'' \<in> set (paths t)"
    then obtain xs'' where "xs'' \<noteq> []" and "(x # (xs' @ xs'')) \<in> set (paths (MP_Trie (xt # xts)))"
      unfolding \<open>t = MP_Trie (xt#xts)\<close> by force


    obtain t'' where "(x,t'') \<in> set (xt#xts)"
               and   "(xs' @ xs'') \<in> set (paths t'')"
      using \<open>(x # (xs' @ xs'')) \<in> set (paths (MP_Trie (xt # xts)))\<close>
      unfolding \<open>t = MP_Trie (xt#xts)\<close> paths.simps 
      by force

    have "distinct (map fst (xt#xts))"
      using Cons.prems(1) unfolding \<open>t = MP_Trie (xt#xts)\<close> by simp
    then have "t'' = t'"
      using \<open>(x,t') \<in> set (xt#xts)\<close> \<open>(x,t'') \<in> set (xt#xts)\<close>
      by (meson eq_key_imp_eq_value)  
    then have "xs'@xs'' \<in> set (paths t')"
      using \<open>(xs' @ xs'') \<in> set (paths t'')\<close> by auto
    then show "False"
      using \<open>xs'' \<noteq> []\<close> Cons.IH[OF \<open>mp_trie_invar t'\<close> \<open>xs' \<in> set (paths t')\<close>] by blast
  qed
qed
            


lemma paths_insert_empty : 
  "paths (insert xs empty) = [xs]"
proof (induction xs)
  case Nil
  then show ?case unfolding empty_def by auto
next
  case (Cons x xs)
  then show ?case unfolding empty_def insert.simps by auto
qed

lemma paths_order :
  assumes "set ts = set ts'"
  and     "length ts = length ts'" (* length requirement not actually necessary *)
shows "set (paths (MP_Trie ts)) = set (paths (MP_Trie ts'))"
  using assms(2,1) proof (induction ts ts' rule: list_induct2)
  case Nil
  then show ?case by auto
next
  case (Cons x xs y ys)

  have scheme: "\<And> f xs ys . set xs = set ys \<Longrightarrow> set (concat (map f xs)) = set (concat (map f ys))"
    by auto

  show ?case 
    using scheme[OF Cons.prems(1), of "(\<lambda>(x, t). map ((#) x) (paths t))"] by simp
qed


lemma paths_insert_maximal :
  assumes "mp_trie_invar t" 
  shows "set (paths (insert xs t)) = (if (\<exists> xs' . xs@xs' \<in> set (paths t))
                                         then set (paths t)
                                         else Set.insert xs (set (paths t) - {xs' . \<exists> xs'' . xs'@xs'' = xs}))" 
using assms proof (induction xs arbitrary: t)
  case Nil
  then show ?case
    using paths_nonempty by force    
next
  case (Cons x xs)
  show ?case proof (cases "t = empty")
    case True
    show ?thesis 
      unfolding True
      unfolding paths_insert_empty  
      unfolding empty_def paths.simps by auto
  next
    case False
    
    then obtain xt xts where "t = MP_Trie (xt#xts)"
      by (metis empty_def height.cases)
    then have "t = MP_Trie ((fst xt, snd xt)#xts)" 
      by auto

    have "distinct (map fst (xt#xts))"
      using Cons.prems \<open>t = MP_Trie (xt#xts)\<close> by auto

     have "(paths t) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))"
      unfolding \<open>t = MP_Trie ((fst xt, snd xt)#xts)\<close> by simp
    then have "set (paths t) = {x#xs | x xs t . (x,t) \<in> set (xt#xts) \<and> xs \<in> set (paths t)}"
      by auto
    then have "Set.insert (x#xs) (set (paths t)) = Set.insert (x#xs) {x#xs | x xs t . (x,t) \<in> set (xt#xts) \<and> xs \<in> set (paths t)}"
      by blast

    show ?thesis proof (cases "x \<in> set (map fst (xt#xts))")
      case True
      case True
      then obtain i where "i < length (xt#xts)" and "fst ((xt#xts) ! i) = x"
        by (metis in_set_conv_nth list_map_source_elem)
      then have "((xt#xts) ! i) = (x,snd ((xt#xts) ! i))" by auto

      have "mp_trie_invar (snd ((xt # xts) ! i))"
        using Cons.prems \<open>i < length (xt#xts)\<close> unfolding \<open>t = MP_Trie (xt#xts)\<close>
        by (metis \<open>(xt # xts) ! i = (x, snd ((xt # xts) ! i))\<close> in_set_zipE mp_trie_invar.simps nth_mem zip_map_fst_snd) 


      have "insert (x#xs) t = MP_Trie (take i (xt # xts) @ [(x, insert xs (snd ((xt # xts) ! i)))] @ drop (Suc i) (xt # xts))"
        unfolding \<open>t = MP_Trie (xt#xts)\<close> insert.simps
        unfolding update_assoc_list_with_default_key_found[OF \<open>distinct (map fst (xt#xts))\<close> \<open>i < length (xt#xts)\<close> \<open>fst ((xt#xts) ! i) = x\<close>]
        by simp
      
      then have "set (paths (insert (x#xs) t)) 
                 = set (paths (MP_Trie (take i (xt # xts) @ [(x, insert xs (snd ((xt # xts) ! i)))] @ drop (Suc i) (xt # xts))))"
        by simp
      also have "... = set (paths (MP_Trie ((x, insert xs (snd ((xt # xts) ! i))) # (take i (xt # xts) @ drop (Suc i) (xt # xts)))))"
        using paths_order[of "(take i (xt # xts) @ [(x, insert xs (snd ((xt # xts) ! i)))] @ drop (Suc i) (xt # xts))" 
                             "((x, insert xs (snd ((xt # xts) ! i))) # (take i (xt # xts) @ drop (Suc i) (xt # xts)))"]
        by force
      also have "... = set ((map ((#) x) (paths (insert xs (snd ((xt # xts) ! i))))) @ (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))))"
        unfolding paths.simps by force
      finally have "set (paths (insert (x#xs) t)) = 
                      set (map ((#) x) (paths (insert xs (snd ((xt # xts) ! i))))) 
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by force
      also have "\<dots> = (image ((#) x) (set (paths (insert xs (snd ((xt # xts) ! i))))))
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by auto
      finally have pi1: "set (paths (insert (x#xs) t)) = 
                      image ((#) x) (if \<exists>xs'. xs @ xs' \<in> set (paths (snd ((xt # xts) ! i))) then set (paths (snd ((xt # xts) ! i)))
                                                                                            else Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))
                       \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        unfolding Cons.IH[OF \<open>mp_trie_invar (snd ((xt # xts) ! i))\<close>] by blast



      have po1: "set (xt#xts) = set ((x,snd ((xt#xts) ! i)) # ((take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        using list_index_split_set[OF \<open>i < length (xt#xts)\<close>] 
        unfolding \<open>((xt#xts) ! i) = (x,snd ((xt#xts) ! i))\<close>[symmetric] by assumption
      have po2: "length (xt#xts) = length ((x,snd ((xt#xts) ! i)) # ((take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        using \<open>i < length (xt#xts)\<close> by auto


      have "set (paths t) = set (paths (MP_Trie ((x,snd ((xt#xts) ! i)) # ((take i (xt # xts) @ drop (Suc i) (xt # xts))))))"
        unfolding \<open>t = MP_Trie (xt#xts)\<close> 
        using paths_order[OF po1 po2] by assumption
      also have "\<dots> = set ((map ((#) x) (paths (snd ((xt # xts) ! i)))) @ (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))))"
        unfolding paths.simps by auto
      finally have "set (paths t) = 
                      set (map ((#) x) (paths (snd ((xt # xts) ! i)))) 
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by force

      then have pi2: "set (paths t) = (image ((#) x) (set (paths (snd ((xt # xts) ! i))))) 
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by auto


      show ?thesis proof (cases "\<exists>xs'. xs @ xs' \<in> set (paths (snd ((xt # xts) ! i)))")
        case True
        then have pi1': "set (paths (insert (x#xs) t)) = image ((#) x) (set (paths (snd ((xt # xts) ! i))))
                                                         \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
          using pi1 by auto

        have "set (paths (insert (x # xs) t)) = set (paths t)"
          unfolding pi1' pi2 by simp
        moreover have "\<exists>xs'. (x # xs) @ xs' \<in> set (paths t)"
          using True unfolding pi2 by force
        ultimately show ?thesis by simp
      next
        case False
        then have pi1': "set (paths (insert (x#xs) t)) = image ((#) x) (Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))
                                                         \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
          using pi1 by auto

        have x1: "((#) x ` Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))  
              = Set.insert (x # xs) ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})" 
        proof -
          have "\<And> a . a \<in> ((#) x ` Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs})) \<Longrightarrow>
                       a \<in> Set.insert (x # xs) ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})"
            by fastforce
          moreover have "\<And> a . a \<in> Set.insert (x # xs) ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs}) \<Longrightarrow>
                                a \<in> ((#) x ` Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))"
          proof -
            fix a assume "a \<in> Set.insert (x # xs) ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})"
            then consider (a) "a = (x#xs)" |
                          (b) "a \<in> ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})" by blast
            then show "a \<in> ((#) x ` Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))" 
            proof cases
              case a
              then show ?thesis by blast
            next
              case b
              then show ?thesis by force
            qed 
          qed
          ultimately show ?thesis by blast
        qed

        have x2: "set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))) 
                      = (set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})" 
        and  x3: "\<not>(\<exists>xs'. (x # xs) @ xs' \<in> set (paths t))"
        proof -
          

          have "\<And> j . j < length (xt#xts) \<Longrightarrow> j \<noteq> i \<Longrightarrow> fst ((xt#xts) ! j) \<noteq> x"
            using \<open>i < length (xt#xts)\<close> \<open>fst ((xt#xts) ! i) = x\<close> \<open>distinct (map fst (xt#xts))\<close>
            by (metis (no_types, lifting) length_map nth_eq_iff_index_eq nth_map)  

          have "\<And> xt' . xt' \<in> set (take i (xt # xts) @ drop (Suc i) (xt # xts)) \<Longrightarrow> fst xt' \<noteq> x"
          proof -
            fix xt' assume "xt' \<in> set (take i (xt # xts) @ drop (Suc i) (xt # xts))"
            then consider (a) "xt' \<in> set (take i (xt # xts))" |
                          (b) "xt' \<in> set (drop (Suc i) (xt # xts))"
              by auto
            then show "fst xt' \<noteq> x" proof cases
              case a
              then obtain j where "j < length (take i (xt#xts))" "(take i (xt#xts)) ! j = xt'"
                by (meson in_set_conv_nth)
                
              have "j < length (xt#xts)" and "j < i"
                using \<open>j < length (take i (xt#xts))\<close> by auto
              moreover have "(xt#xts) ! j = xt'"
                using \<open>(take i (xt#xts)) ! j = xt'\<close> \<open>j < i\<close> by auto 
              ultimately show ?thesis using \<open>\<And> j . j < length (xt#xts) \<Longrightarrow> j \<noteq> i \<Longrightarrow> fst ((xt#xts) ! j) \<noteq> x\<close> by blast
            next
              case b
              then obtain j where "j < length (drop (Suc i) (xt#xts))" "(drop (Suc i) (xt#xts)) ! j = xt'"
                by (meson in_set_conv_nth)

              have "(Suc i) + j < length (xt#xts)" and "(Suc i) + j > i"
                using \<open>j < length (drop (Suc i) (xt#xts))\<close> by auto
              moreover have "(xt#xts) ! ((Suc i) + j) = xt'"
                using \<open>(drop (Suc i) (xt#xts)) ! j = xt'\<close>
                using \<open>i < length (xt # xts)\<close> by auto  
              ultimately show ?thesis using \<open>\<And> j . j < length (xt#xts) \<Longrightarrow> j \<noteq> i \<Longrightarrow> fst ((xt#xts) ! j) \<noteq> x\<close>[of "(Suc i) + j"] 
                by auto
            qed
          qed
          then show "set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))) 
                      = (set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})" 
            by force

          show "\<not>(\<exists>xs'. (x # xs) @ xs' \<in> set (paths t))"
          proof 
            assume "\<exists>xs'. (x # xs) @ xs' \<in> set (paths t)"
            then obtain xs' where "(x # (xs @ xs')) \<in> ((#) x ` set (paths (snd ((xt # xts) ! i)))) \<union>
                                                          set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))" 
              unfolding pi2 by force
            then consider (a) "(x # (xs @ xs')) \<in> ((#) x ` set (paths (snd ((xt # xts) ! i))))" |
                          (b) "(x # (xs @ xs')) \<in> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
              by blast
            then show False proof cases
              case a
              then show ?thesis using False by force
            next
              case b
              then show ?thesis using \<open>\<And> xt' . xt' \<in> set (take i (xt # xts) @ drop (Suc i) (xt # xts)) \<Longrightarrow> fst xt' \<noteq> x\<close> by force
            qed          
          qed
        qed

        have *: "Set.insert (x # xs) ((#) x ` set (paths (snd ((xt # xts) ! i))) \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})
                  = Set.insert (x # xs) (((#) x ` set (paths (snd ((xt # xts) ! i)))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs}) \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))" 
          using x2 by blast
          

        have "set (paths (insert (x # xs) t)) = Set.insert (x # xs) (set (paths t) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})"
          unfolding pi1' pi2 x1 * by blast
        then show ?thesis
          using x3 by simp 
      qed
    next
      case False
      have "insert (x#xs) t = MP_Trie (xt # (xts @ [(x, insert xs empty)]))"
        unfolding \<open>t = MP_Trie (xt#xts)\<close> insert.simps
        unfolding update_assoc_list_with_default_key_not_found[OF \<open>distinct (map fst (xt#xts))\<close> False]
        by simp
      
      have "(paths (MP_Trie (xt # (xts @ [(x, insert xs empty)])))) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts @ [(x, insert xs empty)]))"
        unfolding paths.simps empty_def by simp
      also have "... = (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))) @ (map ((#) x) (paths (insert xs empty))) "
        by auto
      finally have "paths (insert (x#xs) t) = (paths t) @ [x#xs]"
        unfolding \<open>insert (x#xs) t = MP_Trie (xt # (xts @ [(x, insert xs empty)]))\<close>
                  \<open>(paths t) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))\<close>[symmetric]
                  paths_insert_empty 
        by auto
      then have "set (paths (insert (x#xs) t)) = Set.insert (x#xs) (set (paths t))"
        by force
        
        
      have "\<And> p . p \<in> set (paths t) \<Longrightarrow> p \<noteq> [] \<and> hd p \<noteq> x"
        using False
        unfolding \<open>(paths t) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))\<close> by force
      then have "\<And> xs' . xs' \<in> set (paths t) \<Longrightarrow> \<not>(\<exists> xs'' . xs'@xs'' = x#xs)"
        by (metis hd_append2 list.sel(1))
      then have "set (paths t) = (set (paths t) - {xs' . \<exists> xs'' . xs'@xs'' = x#xs})"
        by blast
      then show ?thesis 
        unfolding \<open>set (paths (insert (x#xs) t)) = Set.insert (x#xs) (set (paths t))\<close>
        using \<open>\<And>p. p \<in> set (paths t) \<Longrightarrow> p \<noteq> [] \<and> hd p \<noteq> x\<close> by force
    qed
  qed
qed




fun from_list :: "'a list list \<Rightarrow> 'a mp_trie" where
  "from_list seqs = foldr insert seqs empty"

lemma from_list_invar : "mp_trie_invar (from_list xs)"
  using empty_invar insert_invar by (induction xs; auto)

lemma from_list_paths :
  "set (paths (from_list (x#xs))) = {y. y \<in> set (x#xs) \<and> \<not>(\<exists> y' . y' \<noteq> [] \<and> y@y' \<in> set (x#xs))}"
proof (induction xs arbitrary: x)
  case Nil
  have *: "paths (from_list [x]) = paths (insert x empty)" by auto
  
  show ?case 
    unfolding *
    unfolding paths_insert_maximal[OF empty_invar, of "x"]
    unfolding empty_def  
    by (cases x ; auto)
next
  case (Cons x' xs)

  have "from_list (x#x'#xs) = insert x (insert x' (from_list xs))" by auto
  have "from_list (x#x'#xs) = insert x (from_list (x'#xs))" by auto

  have "mp_trie_invar (insert x' (from_list xs))"
    using from_list_invar insert_invar by metis
  have "(insert x' (from_list xs)) = from_list (x'#xs)" by auto


  thm paths_insert_maximal[OF \<open>mp_trie_invar (insert x' (from_list xs))\<close>, of x]

  show ?case proof (cases "\<exists>xs'. x @ xs' \<in> set (paths (insert x' (from_list xs)))")
    case True
    then have "set (paths (insert x (insert x' (from_list xs)))) = set (paths (insert x' (from_list xs)))"
      using paths_insert_maximal[OF \<open>mp_trie_invar (insert x' (from_list xs))\<close>, of x] by simp
    then have "set (paths (insert x (from_list (x' # xs)))) = set (paths (from_list (x' # xs)))"
      unfolding \<open>(insert x' (from_list xs)) = from_list (x'#xs)\<close> 
      by assumption
    then have "set (paths (from_list (x#x'#xs))) = {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}"
      unfolding Cons \<open>from_list (x#x'#xs) = insert x (from_list (x'#xs))\<close>
      by assumption

    show ?thesis proof (cases "x \<in> set (paths (insert x' (from_list xs)))")
      case True
      then have "x \<in> set (x'#xs)"
        using \<open>set (paths (insert x (insert x' (from_list xs)))) = set (paths (insert x' (from_list xs)))\<close> \<open>set (paths (from_list (x # x' # xs))) = {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}\<close> by auto
      then show ?thesis 
        unfolding \<open>set (paths (from_list (x#x'#xs))) = {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}\<close> by auto
    next
      case False
      
      have "{y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)} = {y \<in> set (x # x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)}" 
      proof -
        obtain xs' where "xs' \<noteq> []" and "x @ xs' \<in>  {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}"
          using True False
          by (metis \<open>from_list (x # x' # xs) = insert x (insert x' (from_list xs))\<close> \<open>set (paths (insert x (insert x' (from_list xs)))) = set (paths (insert x' (from_list xs)))\<close> \<open>set (paths (from_list (x # x' # xs))) = {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}\<close> append_Nil2) 
        then have s1: "{y \<in> set (x # x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)} = {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)}"
          by auto 
            
        have "\<And> y . (\<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)) \<Longrightarrow> (\<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs))"
        proof -
          fix y assume "(\<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs))"
          
          show "(\<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs))"
          proof 
            assume "\<exists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)"
            then have "\<exists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs) - set (x' # xs)"
              using \<open>(\<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs))\<close> by auto
            then have "\<exists>y' . y' \<noteq> [] \<and> y @ y' = x"
              by auto
            then show "False"
              by (metis (no_types, lifting) Nil_is_append_conv \<open>\<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)\<close> \<open>x @ xs' \<in> {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}\<close> append.assoc mem_Collect_eq) 
          qed
        qed
        then have s2: "{y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)} = {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)}"
          by auto

        show ?thesis 
          unfolding s1 s2 by simp
      qed
      then show ?thesis
        using \<open>set (paths (from_list (x # x' # xs))) = {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}\<close> by auto 
    qed
      
  next
    case False
    

    then have *: "set (paths (insert x (insert x' (from_list xs)))) 
                = Set.insert x (set (paths (insert x' (from_list xs))) - {xs'. \<exists>xs''. xs' @ xs'' = x})"
      using paths_insert_maximal[OF \<open>mp_trie_invar (insert x' (from_list xs))\<close>, of x] by simp

    have f: "\<nexists>xs'. x @ xs' \<in> {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}"
      using False
      unfolding \<open>(insert x' (from_list xs)) = from_list (x'#xs)\<close> Cons
      by assumption
    then have "x \<notin> {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}"
      by (metis (no_types, lifting) append_Nil2)

    have "x \<notin> set (x' # xs)"
    proof
      assume "x \<in> set (x' # xs)"
      then have "\<exists>y'. y' \<noteq> [] \<and> x @ y' \<in> set (x' # xs)"
        using \<open>x \<notin> {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}\<close> by auto

      let ?xms = "{xs' . xs' \<noteq> [] \<and> x @ xs' \<in> set (x' # xs)}"
      have "?xms \<noteq> {}"
        using \<open>\<exists>y'. y' \<noteq> [] \<and> x @ y' \<in> set (x' # xs)\<close>
        by simp 
      moreover have "finite ?xms"
      proof -
        have "?xms \<subseteq> image (drop (length x)) (set (x'#xs))" by force
        then show ?thesis by (meson List.finite_set finite_surj) 
      qed
      ultimately have "\<exists> xs' \<in> ?xms . \<forall> xs'' \<in> ?xms . length xs'' \<le> length xs'"
        by (meson max_length_elem not_le_imp_less) 
      then obtain xs' where "xs' \<noteq> []"
                      and   "x@xs' \<in> set (x'#xs)"
                      and   "\<And> xs'' . xs'' \<noteq> [] \<Longrightarrow> x@xs'' \<in> set (x'#xs) \<Longrightarrow> length xs'' \<le> length xs'"
        by blast
      
      have "\<nexists>y'. y' \<noteq> [] \<and> (x@xs') @ y' \<in> set (x' # xs)"
      proof 
        assume "\<exists>y'. y' \<noteq> [] \<and> (x @ xs') @ y' \<in> set (x' # xs)"
        then obtain xs'' where "xs'' \<noteq> []" and "(x @ xs') @ xs'' \<in> set (x' # xs)"
          by blast
        then have "xs'@xs'' \<noteq> []" and "x @ (xs' @ xs'') \<in> set (x' # xs)"
          by auto
        then have "length (xs'@xs'') \<le> length xs'"
          using \<open>\<And> xs'' . xs'' \<noteq> [] \<Longrightarrow> x@xs'' \<in> set (x'#xs) \<Longrightarrow> length xs'' \<le> length xs'\<close> by blast
        then show "False"
          using \<open>xs'' \<noteq> []\<close> by auto
      qed
        
      then have "x @ xs' \<in> {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}" 
        using \<open>x@xs' \<in> set (x'#xs)\<close> by blast
      then show "False" using \<open>\<nexists>xs'. x @ xs' \<in> {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}\<close>
        by blast
    qed
    
    have "\<nexists>y'. y' \<noteq> [] \<and> x @ y' \<in> set (x # x' # xs)"
    proof 
      assume "\<exists>y'. y' \<noteq> [] \<and> x @ y' \<in> set (x # x' # xs)"
      then obtain y' where "y' \<noteq> []" and "x@y' \<in> set (x#x'#xs)"
        by blast
      then have "x@y' \<in> set (x'#xs)"
        by auto

      let ?xms = "{xs' . xs' \<noteq> [] \<and> x @ xs' \<in> set (x # x' # xs)}"
      have "?xms \<noteq> {}"
        using \<open>\<exists>y'. y' \<noteq> [] \<and> x @ y' \<in> set (x # x' # xs)\<close>
        by simp 
      moreover have "finite ?xms"
      proof -
        have "?xms \<subseteq> image (drop (length x)) (set (x'#xs))" by force
        then show ?thesis by (meson List.finite_set finite_surj) 
      qed
      ultimately have "\<exists> xs' \<in> ?xms . \<forall> xs'' \<in> ?xms . length xs'' \<le> length xs'"
        by (meson max_length_elem not_le_imp_less) 
      then obtain xs' where "xs' \<noteq> []"
                      and   "x@xs' \<in> set (x#x'#xs)"
                      and   "\<And> xs'' . xs'' \<noteq> [] \<Longrightarrow> x@xs'' \<in> set (x#x'#xs) \<Longrightarrow> length xs'' \<le> length xs'"
        by blast
      


      have "\<nexists>y'. y' \<noteq> [] \<and> (x@xs') @ y' \<in> set (x # x' # xs)"
      proof 
        assume "\<exists>y'. y' \<noteq> [] \<and> (x @ xs') @ y' \<in> set (x # x' # xs)"
        then obtain xs'' where "xs'' \<noteq> []" and "(x @ xs') @ xs'' \<in> set (x # x' # xs)"
          by blast
        then have "xs'@xs'' \<noteq> []" and "x @ (xs' @ xs'') \<in> set (x # x' # xs)"
          by auto
        then have "length (xs'@xs'') \<le> length xs'"
          using \<open>\<And> xs'' . xs'' \<noteq> [] \<Longrightarrow> x@xs'' \<in> set (x#x'#xs) \<Longrightarrow> length xs'' \<le> length xs'\<close> by blast
        then show "False"
          using \<open>xs'' \<noteq> []\<close> by auto
      qed
        
      then have "x @ xs' \<in> {y \<in> set (x # x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)}" 
        using \<open>x@xs' \<in> set (x # x'#xs)\<close> by blast
      then have "x @ xs' \<in> set (x' # xs)" and "\<nexists>y'. y' \<noteq> [] \<and> (x@xs') @ y' \<in> set (x' # xs)"
        using \<open>xs' \<noteq> []\<close> by auto
      then have "x @ xs' \<in> {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}" 
        by blast
      then show "False" using \<open>\<nexists>xs'. x @ xs' \<in> {y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)}\<close>
        by blast
    qed


    have "Set.insert x ({y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)} - {xs'. \<exists>xs''. xs' @ xs'' = x})
              = {y \<in> set (x # x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)}" 
    proof -
      have "\<And> y . y \<in> Set.insert x ({y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)} - {xs'. \<exists>xs''. xs' @ xs'' = x}) \<Longrightarrow> y \<in> {y \<in> set (x # x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)}"
      proof -
        fix y assume "y \<in> Set.insert x ({y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)} - {xs'. \<exists>xs''. xs' @ xs'' = x})"
        then consider (a) "y = x" |
                      (b) "y \<in> ({y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)} - {xs'. \<exists>xs''. xs' @ xs'' = x})"
          by blast
        then show "y \<in> {y \<in> set (x # x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)}"
        proof cases
          case a
          show ?thesis
            using \<open>\<nexists>y'. y' \<noteq> [] \<and> x @ y' \<in> set (x # x' # xs)\<close> unfolding a by auto
        next
          case b
          then have "y \<in> set (x' # xs)" and "\<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)" and "\<not>(\<exists>xs''. y @ xs'' = x)"
            by blast+

          have "y \<in> set (x#x'#xs)"
            using \<open>y \<in> set (x' # xs)\<close> by auto
          moreover have "\<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)"
            using \<open>\<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)\<close> \<open>\<not>(\<exists>xs''. y @ xs'' = x)\<close>
            by auto 
          ultimately show ?thesis by blast
        qed
      qed

      moreover have "\<And> y .y \<in> {y \<in> set (x # x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x # x' # xs)} \<Longrightarrow>  y \<in> Set.insert x ({y \<in> set (x' # xs). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> set (x' # xs)} - {xs'. \<exists>xs''. xs' @ xs'' = x})"
        by auto
      ultimately show ?thesis by blast
    qed
    then show ?thesis
      using "*" Cons.IH by auto 
  qed
qed



subsubsection \<open>New Code Generation for @{text "remove_proper_prefixes"}\<close>

declare [[code drop: remove_proper_prefixes]]

lemma remove_proper_prefixes_code_trie[code] :
  "remove_proper_prefixes (set xs) = (case xs of [] \<Rightarrow> {} | (x#xs') \<Rightarrow> set (paths (from_list (x#xs'))))"
  unfolding from_list_paths remove_proper_prefixes_def by (cases xs; auto)


end 