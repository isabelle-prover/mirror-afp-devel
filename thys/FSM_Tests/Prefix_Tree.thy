section \<open>Prefix Tree\<close>

text \<open>This theory introduces a tree to efficiently store prefix-complete sets of lists.
      Several functions to lookup or merge subtrees are provided.\<close>


theory Prefix_Tree
imports Util "HOL-Library.Mapping" "HOL-Library.List_Lexorder" 
begin

datatype 'a prefix_tree = PT "'a \<rightharpoonup> 'a prefix_tree"

definition empty :: "'a prefix_tree" where
  "empty = PT Map.empty"

fun isin :: "'a prefix_tree \<Rightarrow> 'a list \<Rightarrow> bool" where
  "isin t [] = True" |
  "isin (PT m) (x # xs) = (case m x of None \<Rightarrow> False | Some t \<Rightarrow> isin t xs)"

lemma isin_prefix :
  assumes "isin t (xs@xs')"
  shows "isin t xs"
proof -
  obtain m where "t = PT m"
    by (metis prefix_tree.exhaust)

  show ?thesis using assms unfolding \<open>t = PT m\<close>
  proof (induction xs arbitrary: m)
    case Nil
    then show ?case by auto
  next
    case (Cons x xs)
    then have "isin (PT m) (x # (xs @ xs'))"
      by auto
    then obtain m' where "m x = Some (PT m')"
                     and "isin (PT m') (xs@xs')"
      unfolding isin.simps
      by (metis option.exhaust option.simps(4) option.simps(5) prefix_tree.exhaust) 
    then show ?case 
      using Cons.IH[of m'] by auto
  qed
qed


fun set :: "'a prefix_tree \<Rightarrow> 'a list set" where
  "set t = {xs . isin t xs}"

lemma set_empty : "set empty = ({[]} :: 'a list set)"
proof 
  show "set empty \<subseteq> ({[]} :: 'a list set)"
  proof 
    fix xs :: "'a list"
    assume "xs \<in> set empty"
    then have "isin empty xs"
      by auto
    
    have "xs = []"
    proof (rule ccontr)
      assume "xs \<noteq> []"
      then obtain x xs' where "xs = x#xs'"
        using list.exhaust by auto 
      then have "Map.empty x \<noteq> None"
        using \<open>isin empty xs\<close> unfolding empty_def
        by simp 
      then show "False"
        by auto
    qed
    then show "xs \<in> {[]}" 
      by blast 
  qed
  show "({[]} :: 'a list set) \<subseteq> set empty"
    unfolding set.simps empty_def
    by simp 
qed

lemma set_Nil : "[] \<in> set t" 
  by auto


fun insert :: "'a prefix_tree \<Rightarrow> 'a list \<Rightarrow> 'a prefix_tree" where
  "insert t [] = t" |
  "insert (PT m) (x#xs) = PT (m(x \<mapsto> insert (case m x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') xs))"


lemma insert_isin_prefix : "isin (insert t (xs@xs')) xs"
proof (induction xs arbitrary: t)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  moreover obtain m where "t = PT m"
    using prefix_tree.exhaust by auto 
  ultimately obtain t' where "(m(x \<mapsto> insert (case m x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') xs)) x = Some t'"
    by simp
  then have "isin (insert t ((x#xs)@xs')) (x#xs) = isin (insert (case m x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') (xs@xs')) xs"
    unfolding \<open>t = PT m\<close>
    by simp 
  then show ?case 
    using Cons.IH by auto
qed

  

lemma insert_isin_other : 
  assumes "isin t xs"
shows "isin (insert t xs') xs"
proof (cases "xs = xs'")
  case True
  then show ?thesis using insert_isin_prefix[of t xs "[]"] by simp
next
  case False
  
  have *: "\<And> i xs xs' . take i xs = take i xs' \<Longrightarrow> take (Suc i) xs \<noteq> take (Suc i) xs' \<Longrightarrow> isin t xs \<Longrightarrow> isin (insert t xs') xs"
  proof -
    fix i xs xs' assume "take i xs = take i xs'"
                    and "take (Suc i) xs \<noteq> take (Suc i) xs'"
                    and "isin t xs"
    then show "isin (insert t xs') xs"
    proof (induction i arbitrary: xs xs' t)
      case 0
      then consider (a) "xs = [] \<and> xs' \<noteq> []" |
                    (b) "xs' = [] \<and> xs \<noteq> []" |
                    (c) "xs \<noteq> [] \<and> xs' \<noteq> [] \<and> hd xs \<noteq> hd xs'"
        by (metis take_Suc take_eq_Nil)
      then show ?case proof cases
        case a
        then show ?thesis by auto 
      next
        case b
        then show ?thesis
          by (simp add: "0.prems"(3)) 
      next
        case c
        then obtain b bs c cs where "xs = b#bs" and "xs' = c#cs" and "b \<noteq> c"
          using list.exhaust_sel by blast
        obtain m where "t = PT m"
          using prefix_tree.exhaust by auto 
        have "isin (Prefix_Tree.insert t xs') xs = isin t xs" 
          unfolding \<open>t = PT m\<close> \<open>xs = b#bs\<close> \<open>xs' = c#cs\<close> insert.simps isin.simps using \<open>b \<noteq> c\<close>
          by simp 
        then show ?thesis 
          using \<open>isin t xs\<close> by simp
      qed
    next
      case (Suc i) 

      define hxs where hxs: "hxs = hd xs"
      define txs where txs: "txs = tl xs"
      define txs' where txs': "txs' = tl xs'"

      have "xs = hxs#txs"
        unfolding hxs txs
        using \<open>take (Suc i) xs = take (Suc i) xs'\<close> \<open>take (Suc (Suc i)) xs \<noteq> take (Suc (Suc i)) xs'\<close>
        by (metis Zero_not_Suc hd_Cons_tl take_eq_Nil) 
      moreover have "xs' = hxs#txs'"
        unfolding hxs txs txs'
        using \<open>take (Suc i) xs = take (Suc i) xs'\<close> \<open>take (Suc (Suc i)) xs \<noteq> take (Suc (Suc i)) xs'\<close>
        by (metis hd_Cons_tl hd_take take_Nil take_Suc_Cons take_tl zero_less_Suc)
      ultimately have "take (Suc i) txs \<noteq> take (Suc i) txs'"
         using \<open>take (Suc (Suc i)) xs \<noteq> take (Suc (Suc i)) xs'\<close>
         by (metis take_Suc_Cons) 
      moreover have "take i txs = take i txs'"
        using \<open>take (Suc i) xs = take (Suc i) xs'\<close> unfolding txs txs'
        by (simp add: take_tl) 
      ultimately have "\<And> t . isin t txs \<Longrightarrow> isin (Prefix_Tree.insert t txs') txs" 
        using Suc.IH by blast

      obtain m where "t = PT m"
        using prefix_tree.exhaust by auto 
      
      obtain t' where "m hxs = Some t'"
                  and "isin t' txs"
        using case_optionE by (metis Suc.prems(3) \<open>t = PT m\<close> \<open>xs = hxs # txs\<close> isin.simps(2)) 

      have "isin (Prefix_Tree.insert t xs') xs = isin (Prefix_Tree.insert t' txs') txs"
        using \<open>m hxs = Some t'\<close> unfolding \<open>t = PT m\<close> \<open>xs = hxs#txs\<close> \<open>xs' = hxs#txs'\<close> by auto
      then show ?case
        using \<open>\<And> t . isin t txs \<Longrightarrow> isin (Prefix_Tree.insert t txs') txs\<close> \<open>isin t' txs\<close> 
        by simp
    qed
  qed

  show ?thesis 
    using different_lists_shared_prefix[OF False] *[OF _ _ assms] by blast
qed


lemma insert_isin_rev : 
  assumes "isin (insert t xs') xs"
shows "isin t xs \<or> (\<exists> xs'' . xs' = xs@xs'')" 
proof (cases "xs = xs'")
  case True
  then show ?thesis using insert_isin_prefix[of t xs "[]"] by simp
next
  case False

  have *: "\<And> i xs xs' . take i xs = take i xs' \<Longrightarrow> take (Suc i) xs \<noteq> take (Suc i) xs' \<Longrightarrow> isin (insert t xs') xs \<Longrightarrow> isin t xs \<or> (\<exists> xs'' . xs' = xs@xs'')"
  proof -
    fix i xs xs' assume "take i xs = take i xs'"
                    and "take (Suc i) xs \<noteq> take (Suc i) xs'"
                    and "isin (insert t xs') xs"
    then show "isin t xs \<or> (\<exists> xs'' . xs' = xs@xs'')"
    proof (induction i arbitrary: xs xs' t)
      case 0
      then consider (a) "xs = [] \<and> xs' \<noteq> []" |
                    (b) "xs' = [] \<and> xs \<noteq> []" |
                    (c) "xs \<noteq> [] \<and> xs' \<noteq> [] \<and> hd xs \<noteq> hd xs'"
        by (metis take_Suc take_eq_Nil)
      then show ?case proof cases
        case a
        then show ?thesis
          by (metis isin.simps(1) ) 
      next
        case b
        then show ?thesis
          using "0.prems"(3) by auto
      next
        case c
        then obtain b bs c cs where "xs = b#bs" and "xs' = c#cs" and "b \<noteq> c"
          using list.exhaust_sel by blast
        obtain m where "t = PT m"
          using prefix_tree.exhaust by auto 
        have "isin (Prefix_Tree.insert t xs') xs = isin t xs" 
          unfolding \<open>t = PT m\<close> \<open>xs = b#bs\<close> \<open>xs' = c#cs\<close> insert.simps isin.simps using \<open>b \<noteq> c\<close>
          by simp 
        then show ?thesis 
          using \<open>isin (insert t xs') xs\<close> by simp
      qed
    next
      case (Suc i) 

      define hxs where hxs: "hxs = hd xs"
      define txs where txs: "txs = tl xs"
      define txs' where txs': "txs' = tl xs'"

      have "xs = hxs#txs"
        unfolding hxs txs
        using \<open>take (Suc i) xs = take (Suc i) xs'\<close> \<open>take (Suc (Suc i)) xs \<noteq> take (Suc (Suc i)) xs'\<close>
        by (metis Zero_not_Suc hd_Cons_tl take_eq_Nil) 
      moreover have "xs' = hxs#txs'"
        unfolding hxs txs txs'
        using \<open>take (Suc i) xs = take (Suc i) xs'\<close> \<open>take (Suc (Suc i)) xs \<noteq> take (Suc (Suc i)) xs'\<close>
        by (metis hd_Cons_tl hd_take take_Nil take_Suc_Cons take_tl zero_less_Suc)
      ultimately have "take (Suc i) txs \<noteq> take (Suc i) txs'"
         using \<open>take (Suc (Suc i)) xs \<noteq> take (Suc (Suc i)) xs'\<close>
         by (metis take_Suc_Cons) 
      moreover have "take i txs = take i txs'"
        using \<open>take (Suc i) xs = take (Suc i) xs'\<close> unfolding txs txs'
        by (simp add: take_tl) 
      ultimately have "\<And> t . isin (Prefix_Tree.insert t txs') txs \<Longrightarrow> isin t txs \<or> (\<exists>xs''. txs' = txs @ xs'')" 
        using Suc.IH by blast

      
      obtain m where "t = PT m"
        using prefix_tree.exhaust by auto 
      
      obtain t' where "(m(hxs \<mapsto> insert (case m hxs of None \<Rightarrow> empty | Some t' \<Rightarrow> t') txs')) hxs = Some t'"
                  and "isin t' txs"
        using case_optionE \<open>isin (Prefix_Tree.insert t xs') xs\<close>
        unfolding \<open>t = PT m\<close> \<open>xs = hxs#txs\<close> \<open>xs' = hxs#txs'\<close> insert.simps isin.simps by blast
      then have "t' = insert (case m hxs of None \<Rightarrow> empty | Some t' \<Rightarrow> t') txs'"
        by auto
      then have *: "isin (case m hxs of None \<Rightarrow> empty | Some t' \<Rightarrow> t') txs \<or> (\<exists>xs''. txs' = txs @ xs'')"
        using \<open>\<And> t . isin (Prefix_Tree.insert t txs') txs \<Longrightarrow> isin t txs \<or> (\<exists>xs''. txs' = txs @ xs'')\<close>
              \<open>isin t' txs\<close>
        by auto

      show ?case proof (cases "m hxs")
        case None
        then have "isin empty txs \<or> (\<exists>xs''. txs' = txs @ xs'')"
          using * by auto
        then have "txs = [] \<or> (\<exists>xs''. txs' = txs @ xs'')"
          by (metis Prefix_Tree.empty_def case_optionE isin.elims(2) option.discI prefix_tree.inject)
        then have "(\<exists>xs''. txs' = txs @ xs'')"
          by auto
        then show ?thesis 
          unfolding \<open>xs = hxs#txs\<close> \<open>xs' = hxs#txs'\<close> by auto
      next
        case (Some t'')
        then consider "isin t'' txs" | "(\<exists>xs''. txs' = txs @ xs'')"
          using * by auto
        then show ?thesis proof cases
          case 1
          moreover have "isin t xs = isin t'' txs"
            unfolding \<open>t = PT m\<close> \<open>xs = hxs#txs\<close> \<open>xs' = hxs#txs'\<close> using Some by auto
          ultimately show ?thesis by simp
        next
          case 2
          then show ?thesis 
            unfolding \<open>xs = hxs#txs\<close> \<open>xs' = hxs#txs'\<close> by auto
        qed
      qed
    qed
  qed

  show ?thesis 
    using different_lists_shared_prefix[OF False] *[OF _ _ assms] by blast
qed



lemma insert_set : "set (insert t xs) = set t \<union> {xs' . \<exists> xs'' . xs = xs'@xs''}"
proof -
  have "set t \<subseteq> set (insert t xs)"
    using insert_isin_other by auto
  moreover have "{xs' . \<exists> xs'' . xs = xs'@xs''} \<subseteq> set (insert t xs)"
    using insert_isin_prefix
    by auto
  moreover have "set (insert t xs) \<subseteq> set t \<union> {xs' . \<exists> xs'' . xs = xs'@xs''}"
    using insert_isin_rev[of t xs] unfolding set.simps by blast
  ultimately show ?thesis
    by blast
qed

lemma insert_isin : "xs \<in> set (insert t xs)"
  unfolding insert_set by auto

lemma set_prefix :  
  assumes "xs@ys \<in> set T"
  shows "xs \<in> set T"
  using assms isin_prefix by auto


fun after :: "'a prefix_tree \<Rightarrow> 'a list \<Rightarrow> 'a prefix_tree" where
  "after t [] = t" |
  "after (PT m) (x # xs) = (case m x of None \<Rightarrow> empty | Some t \<Rightarrow> after t xs)"

lemma after_set : "set (after t xs) = Set.insert [] {xs' . xs@xs' \<in> set t}"
  (is "?A t xs = ?B t xs")
proof 
  show "?A t xs \<subseteq> ?B t xs"
  proof 
    fix xs' assume "xs' \<in> ?A t xs"
    then show "xs' \<in> ?B t xs"
    proof (induction xs arbitrary: t)
      case Nil
      then show ?case by auto
    next
      case (Cons x xs)
      obtain m where "t = PT m"
        using prefix_tree.exhaust by auto 
      show ?case proof (cases "m x")
        case None
        then have "after t (x#xs) = empty"
          unfolding \<open>t = PT m\<close> by auto
        then have "xs' = []"
          using Cons.prems set_empty by auto
        then show ?thesis by blast
      next
        case (Some t')
        then have "after t (x#xs) = after t' xs"
          unfolding \<open>t = PT m\<close> by auto
        then have "xs' \<in> set (after t' xs)"
          using Cons.prems by simp
        then have "xs' \<in> ?B t' xs"
          using Cons.IH by auto

        show ?thesis proof (cases "xs' = []")
          case True
          then show ?thesis by auto
        next
          case False
          then have "isin t' (xs@xs')"
            using \<open>xs' \<in> ?B t' xs\<close> by auto
          then have "isin t (x#(xs@xs'))"
            unfolding \<open>t = PT m\<close> using Some by auto
          then show ?thesis by auto
        qed
      qed
    qed
  qed
    
  show "?B t xs \<subseteq> ?A t xs"
  proof 
    fix xs' assume "xs' \<in> ?B t xs"
    then show "xs' \<in> ?A t xs"
    proof (induction xs arbitrary: t)
      case Nil
      then show ?case by (cases xs'; auto)
    next
      case (Cons x xs)
      obtain m where "t = PT m"
        using prefix_tree.exhaust by auto 

      show ?case proof (cases "xs' = []")
        case True
        then show ?thesis by (cases xs'; auto)
      next
        case False
        then have "x # (xs @ xs') \<in> set t"
          using Cons.prems by auto
        then have "isin t (x # (xs @ xs'))"
          by auto
        then obtain t' where "m x = Some t'"
                         and "isin t' (xs@xs')"
          unfolding \<open>t = PT m\<close>
          by (metis case_optionE isin.simps(2)) 
        then have "xs' \<in> ?B t' xs"
          by auto 
        then have "xs' \<in> ?A t' xs"
          using Cons.IH by blast
        moreover have "after t (x#xs) = after t' xs"
          using \<open>m x = Some t'\<close> unfolding \<open>t = PT m\<close> by auto
        ultimately show ?thesis
          by simp  
      qed
    qed
  qed
qed

lemma after_set_Cons :
  assumes "\<gamma> \<in> set (after T \<alpha>)"
  and     "\<gamma> \<noteq> []"
shows "\<alpha> \<in> set T"
  using assms unfolding after_set
  by (metis insertE isin_prefix mem_Collect_eq set.simps)


function (domintros) combine :: "'a prefix_tree \<Rightarrow> 'a prefix_tree \<Rightarrow> 'a prefix_tree" where
  "combine (PT m1) (PT m2) = (PT (\<lambda> x . case m1 x of
    None \<Rightarrow> m2 x |
    Some t1 \<Rightarrow> (case m2 x of
      None \<Rightarrow> Some t1 |
      Some t2 \<Rightarrow> Some (combine t1 t2))))"
  by pat_completeness auto
termination 
proof -
  {
    fix a b :: "'a prefix_tree"   

    have "combine_dom (a,b)" 
    proof (induction a arbitrary: b)
      case (PT m1)
  
      obtain m2 where "b = PT m2"
        by (metis prefix_tree.exhaust)
  
      have "(\<And>x a' b'. m1 x = Some a' \<Longrightarrow> m2 x = Some b' \<Longrightarrow> combine_dom (a', b'))"
      proof -
        fix x a' b' assume "m1 x = Some a'" and "m2 x = Some b'"
  
        have "Some a' \<in> range m1"
          by (metis \<open>m1 x = Some a'\<close> range_eqI) 
        
        show "combine_dom (a', b')"
          using PT(1)[OF \<open>Some a' \<in> range m1\<close>, of a']
          by simp 
      qed
  
      then show ?case
        using combine.domintros unfolding \<open>b = PT m2\<close> by blast
    qed
  } note t = this

  then show ?thesis by auto
qed

lemma combine_alt_def : 
  "combine (PT m1) (PT m2) = PT (\<lambda>x . combine_options combine (m1 x) (m2 x))"  
  unfolding combine.simps
  by (simp add: combine_options_def)


lemma combine_set :
  "set (combine t1 t2) = set t1 \<union> set t2"
proof 

  show "set (combine t1 t2) \<subseteq> set t1 \<union> set t2"
  proof 
    fix xs assume "xs \<in> set (combine t1 t2)"
    then show "xs \<in> set t1 \<union> set t2"
    proof (induction xs arbitrary: t1 t2)
      case Nil
      show ?case 
        using set_Nil by auto 
    next
      case (Cons x xs)

      obtain m1 m2 where "t1 = PT m1" and "t2 = PT m2"
        by (meson prefix_tree.exhaust)  

      obtain t' where "combine_options combine (m1 x) (m2 x) = Some t'"
                  and "isin t' xs"
        using Cons.prems unfolding \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> combine_alt_def set.simps
        by (metis (no_types, lifting) case_optionE isin.simps(2) mem_Collect_eq) 

      show ?case proof (cases "m1 x")
        case None
        show ?thesis proof (cases "m2 x")
          case None
          then have False
            using \<open>m1 x = None\<close> \<open>combine_options combine (m1 x) (m2 x) = Some t'\<close>
            by simp  
          then show ?thesis 
            by simp
        next
          case (Some t'')
          then have "m2 x = Some t'"
            using \<open>m1 x = None\<close> \<open>combine_options combine (m1 x) (m2 x) = Some t'\<close>
            by simp 
          then have "isin t2 (x#xs)"
            using \<open>isin t' xs\<close> unfolding \<open>t2 = PT m2\<close> by auto
          then show ?thesis
            by simp            
        qed
      next
        case (Some t1')
        show ?thesis proof (cases "m2 x")
          case None
          then have "m1 x = Some t'"
            using \<open>m1 x = Some t1'\<close> \<open>combine_options combine (m1 x) (m2 x) = Some t'\<close>
            by simp 
          then have "isin t1 (x#xs)"
            using \<open>isin t' xs\<close> unfolding \<open>t1 = PT m1\<close> by auto
          then show ?thesis
            by simp 
        next
          case (Some t2')
          then have "t' = combine t1' t2'"
            using \<open>m1 x = Some t1'\<close> \<open>combine_options combine (m1 x) (m2 x) = Some t'\<close>
            by simp  
          then have "xs \<in> Prefix_Tree.set (combine t1' t2')"
            using \<open>isin t' xs\<close>
            by simp 
          then have "xs \<in> Prefix_Tree.set t1' \<union> Prefix_Tree.set t2'"
            using Cons.IH by blast
          then have "isin t1' xs \<or> isin t2' xs"
            by simp
          then have "isin t1 (x#xs) \<or> isin t2 (x#xs)"
            using \<open>m1 x = Some t1'\<close> \<open>m2 x = Some t2'\<close> unfolding \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> by auto
          then show ?thesis 
            by simp
        qed
      qed
    qed
  qed
  
  show "(set t1 \<union> set t2) \<subseteq> set (combine t1 t2)"
  proof -
    have "set t1 \<subseteq> set (combine t1 t2)"
    proof 
      fix xs assume "xs \<in> set t1"
      then have "isin t1 xs"
        by auto
      then show "xs \<in> set (combine t1 t2)"
      proof (induction xs arbitrary: t1 t2)
        case Nil
        then show ?case using set_Nil by auto
      next
        case (Cons x xs)

        obtain m1 m2 where "t1 = PT m1" and "t2 = PT m2"
          by (meson prefix_tree.exhaust)
        
        obtain t1' where "m1 x = Some t1'"
                     and "isin t1' xs"
          using Cons.prems unfolding \<open>t1 = PT m1\<close> isin.simps
          using case_optionE by blast 

        show ?case proof (cases "m2 x")
          case None
          then have "combine_options combine (m1 x) (m2 x) = Some t1'"
            by (simp add: \<open>m1 x = Some t1'\<close>)
          then have "isin (combine t1 t2) (x#xs)"
            using combine_alt_def
            by (metis (no_types, lifting) Cons.prems \<open>m1 x = Some t1'\<close> \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> isin.simps(2)) 
          then show ?thesis 
            by simp
        next
          case (Some t2')
          then have "combine_options combine (m1 x) (m2 x) = Some (combine t1' t2')"
            by (simp add: \<open>m1 x = Some t1'\<close>)
          moreover have "isin (combine t1' t2') xs"
            using Cons.IH[OF \<open>isin t1' xs\<close>]
            by simp
          ultimately have "isin (combine t1 t2) (x#xs)"
            unfolding \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> using isin.simps(2)[of _ x xs]
            by (metis (no_types, lifting) combine_alt_def option.simps(5))
          then show ?thesis by simp
        qed
      qed
    qed
    moreover have "set t2 \<subseteq> set (combine t1 t2)"
    proof 
      fix xs assume "xs \<in> set t2"
      then have "isin t2 xs"
        by auto
      then show "xs \<in> set (combine t1 t2)"
      proof (induction xs arbitrary: t1 t2)
        case Nil
        then show ?case using set_Nil by auto
      next
        case (Cons x xs)

        obtain m1 m2 where "t1 = PT m1" and "t2 = PT m2"
          by (meson prefix_tree.exhaust)
        
        obtain t2' where "m2 x = Some t2'"
                     and "isin t2' xs"
          using Cons.prems unfolding \<open>t2 = PT m2\<close> isin.simps
          using case_optionE by blast 

        show ?case proof (cases "m1 x")
          case None
          then have "combine_options combine (m1 x) (m2 x) = Some t2'"
            by (simp add: \<open>m2 x = Some t2'\<close>)
          then have "isin (combine t1 t2) (x#xs)"
            using combine_alt_def
            by (metis (no_types, lifting) Cons.prems \<open>m2 x = Some t2'\<close> \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> isin.simps(2)) 
          then show ?thesis 
            by simp
        next
          case (Some t1')
          then have "combine_options combine (m1 x) (m2 x) = Some (combine t1' t2')"
            by (simp add: \<open>m2 x = Some t2'\<close>)
          moreover have "isin (combine t1' t2') xs"
            using Cons.IH[OF \<open>isin t2' xs\<close>]
            by simp
          ultimately have "isin (combine t1 t2) (x#xs)"
            unfolding \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> using isin.simps(2)[of _ x xs]
            by (metis (no_types, lifting) combine_alt_def option.simps(5))
          then show ?thesis by simp
        qed
      qed
    qed
    ultimately show ?thesis 
      by blast
  qed
qed




fun combine_after :: "'a prefix_tree \<Rightarrow> 'a list \<Rightarrow> 'a prefix_tree \<Rightarrow> 'a prefix_tree" where
  "combine_after t1 [] t2 = combine t1 t2" |
  "combine_after (PT m) (x#xs) t2 = PT (m(x \<mapsto> combine_after (case m x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') xs t2))"

lemma combine_after_set : "set (combine_after t1 xs t2) = set t1 \<union> {xs' . \<exists> xs'' . xs = xs'@xs''} \<union> {xs@xs' | xs' . xs' \<in> set t2}"
proof 
  show "set (combine_after t1 xs t2) \<subseteq> set t1 \<union> {xs' . \<exists> xs'' . xs = xs'@xs''} \<union> {xs@xs' | xs' . xs' \<in> set t2}"
  proof 
    fix ys assume "ys \<in> set (combine_after t1 xs t2)"
    then show "ys \<in> set t1 \<union> {xs' . \<exists> xs'' . xs = xs'@xs''} \<union> {xs@xs' | xs' . xs' \<in> set t2}"
    proof (induction ys arbitrary: xs t1)
      case Nil
      show ?case using set_Nil by auto
    next
      case (Cons y ys)

      obtain m1 where "t1 = PT m1"
        by (meson prefix_tree.exhaust)  
      
      show ?case proof (cases xs)
        case Nil
        then show ?thesis using combine_set Cons.prems by auto
      next
        case (Cons x xs')

        show ?thesis proof (cases "x = y")
          case True
          then have "isin (combine_after t1 (x#xs') t2) (x#ys)"
            using Cons Cons.prems by auto
          then have "isin (combine_after (case m1 x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') xs' t2) ys"
            unfolding \<open>t1 = PT m1\<close> by auto
          then consider "ys \<in> set (case m1 x of None \<Rightarrow> empty | Some t' \<Rightarrow> t')" | "ys \<in> {xs'' . \<exists> xs''' . xs' = xs''@xs'''}" | "ys \<in> {xs' @ xs'' |xs''. xs'' \<in> set t2}"
            using Cons.IH by auto
          then show ?thesis proof cases
            case 1
            then show ?thesis proof (cases "m1 x")
              case None
              then have "ys = []"
                using 1 set_empty by auto
              then show ?thesis unfolding True Cons by auto
            next
              case (Some t')
              then have "isin t' ys"
                using 1 by auto
              then have "y # ys \<in> Prefix_Tree.set (PT m1)"
                using Some by (simp add: True)  
              then show ?thesis unfolding \<open>t1 = PT m1\<close> by auto 
            qed
          next
            case 2
            then show ?thesis unfolding True \<open>t1 = PT m1\<close> Cons by auto
          next
            case 3
            then show ?thesis unfolding True \<open>t1 = PT m1\<close> Cons by auto
          qed 
        next
          case False
          then have "(m1(x \<mapsto> combine_after (case m1 x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') xs' t2)) y = m1 y"
            by auto
          then have "isin t1 (y#ys)"
            using Cons Cons.prems unfolding \<open>t1 = PT m1\<close>
            by simp 
          then show ?thesis by auto
        qed
      qed
    qed 
  qed

  show "set t1 \<union> {xs' . \<exists> xs'' . xs = xs'@xs''} \<union> {xs@xs' | xs' . xs' \<in> set t2} \<subseteq> set (combine_after t1 xs t2)"
  proof -
    have "set t1 \<subseteq> set (combine_after t1 xs t2)"
    proof
      fix ys assume "ys \<in> set t1"
      then show "ys \<in> set (combine_after t1 xs t2)"
      proof (induction ys arbitrary: t1 xs)
        case Nil
        then show ?case using set_Nil by auto
      next
        case (Cons y ys)
        then have "isin t1 (y#ys)"
          by auto
        
        show ?case proof (cases "xs")
          case Nil
          then show ?thesis using Cons.prems combine_set by auto
        next
          case (Cons x xs')

          obtain m1 where "t1 = PT m1"
            by (meson prefix_tree.exhaust) 
          obtain t' where "m1 y = Some t'"
                      and "isin t' ys"
            using \<open>isin t1 (y#ys)\<close> unfolding \<open>t1 = PT m1\<close> isin.simps
            using case_optionE by blast 
          then have "ys \<in> set t'"
            by auto
          then have "isin (combine_after t' xs' t2) ys"
            using Cons.IH by auto

          show ?thesis proof (cases "x=y")
            case True
            show ?thesis 
              using \<open>isin (combine_after t' xs' t2) ys\<close> \<open>m1 y = Some t'\<close>
              unfolding Cons True \<open>t1 = PT m1\<close> by auto
          next
            case False
            then have "isin (combine_after (PT m1) (x # xs') t2) (y#ys) = isin (PT m1) (y#ys)"
              unfolding combine_after.simps by auto
            then show ?thesis 
              using \<open>y # ys \<in> Prefix_Tree.set t1\<close>
              unfolding Cons \<open>t1 = PT m1\<close> 
              by auto
          qed
        qed
      qed
    qed
    moreover have "{xs' . \<exists> xs'' . xs = xs'@xs''} \<union> {xs@xs' | xs' . xs' \<in> set t2} \<subseteq> set (combine_after t1 xs t2)"
    proof -
      have "{xs@xs' | xs' . xs' \<in> set t2} \<subseteq> set (combine_after t1 xs t2) \<Longrightarrow> {xs' . \<exists> xs'' . xs = xs'@xs''} \<subseteq> set (combine_after t1 xs t2)"
      proof 
        fix ys assume *:"{xs@xs' | xs' . xs' \<in> set t2} \<subseteq> set (combine_after t1 xs t2)"
                  and "ys \<in> {xs' . \<exists> xs'' . xs = xs'@xs''}"   
        then obtain xs' where "xs = ys@xs'"
          by blast
        then have **: "isin (combine_after t1 xs t2) (ys@xs')"
          using * set_Nil[of t2] by force
        show "ys \<in> set (combine_after t1 xs t2)"
          using  isin_prefix[OF **] by auto
      qed
      moreover have "{xs@xs' | xs' . xs' \<in> set t2} \<subseteq> set (combine_after t1 xs t2)"
      proof 
        fix ys assume "ys \<in> {xs@xs' | xs' . xs' \<in> set t2}"
        then obtain xs' where "ys = xs@xs'" and "xs' \<in> set t2"
          by auto

        

        show "ys \<in> set (combine_after t1 xs t2)" 
          unfolding \<open>ys = xs@xs'\<close>
        proof (induction xs arbitrary: t1)
          case Nil 
          then show ?case using combine_set \<open>xs' \<in> set t2\<close> by auto
        next
          case (Cons x xs)

          obtain m1 where "t1 = PT m1"
            by (meson prefix_tree.exhaust) 

          have "isin (combine_after t1 (x # xs) t2) ((x # xs) @ xs') = isin (combine_after (case m1 x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') xs t2) (xs @ xs')"
            unfolding \<open>t1 = PT m1\<close> by auto
          then have *:"(x # xs) @ xs' \<in> Prefix_Tree.set (combine_after t1 (x # xs) t2) = isin (combine_after (case m1 x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') xs t2) (xs @ xs')"
            by auto

          show ?case 
            using \<open>xs' \<in> set t2\<close> Cons 
            unfolding * 
            by (cases "m1 x"; simp)
        qed
      qed
      ultimately show ?thesis
        by blast
    qed
    ultimately show ?thesis
      by blast
  qed
qed


fun from_list :: "'a list list \<Rightarrow> 'a prefix_tree" where
  "from_list xs = foldr (\<lambda> x t . insert t x) xs empty"

lemma from_list_set : "set (from_list xs) = Set.insert [] {xs'' . \<exists> xs' xs''' . xs' \<in> list.set xs \<and> xs' = xs''@xs'''}"
proof (induction xs)
  case Nil
  have "from_list [] = empty"
    by auto
  then have "set (from_list []) = {[]}"
    using set_empty by auto
  moreover have "Set.insert [] {xs'' . \<exists> xs' xs''' . xs' \<in> list.set [] \<and> xs' = xs''@xs'''} = {[]}"
    by auto
  ultimately show ?case 
    by blast
next
  case (Cons x xs)

  have "from_list (x#xs) = insert (from_list xs) x"
    by auto
  then have "set (from_list (x#xs)) = set (from_list xs) \<union> {xs'. \<exists>xs''. x = xs' @ xs''}"
    using insert_set by auto
  then show ?case
    unfolding Cons by force
qed

lemma from_list_subset : "list.set xs \<subseteq> set (from_list xs)"
  unfolding from_list_set by auto

lemma from_list_set_elem :
  assumes "x \<in> list.set xs"
  shows "x \<in> set (from_list xs)"
  using assms unfolding from_list_set by force

function (domintros) finite_tree :: "'a prefix_tree \<Rightarrow> bool" where
  "finite_tree (PT m) = (finite (dom m) \<and> (\<forall> t \<in> ran m . finite_tree t))"
  by pat_completeness auto
termination
proof -
  { fix a :: "'a prefix_tree"   

    have "finite_tree_dom a" 
    proof (induction a)
      case (PT m)
  
      have "(\<And>x. x \<in> ran m \<Longrightarrow> finite_tree_dom x)"
      proof -
        fix x :: "'a prefix_tree"
        assume "x \<in> ran m"
        then have "\<exists>a. m a = Some x"
          by (simp add: ran_def)
        then show "finite_tree_dom x"
          using PT.IH by blast
      qed  
      then show ?case
        using finite_tree.domintros
        by blast 
    qed
  }
  then show ?thesis by auto
qed

lemma combine_after_after_subset :
  "set T2 \<subseteq> set (after (combine_after T1 xs T2) xs)"
  unfolding combine_after_set after_set
  by auto

lemma subset_after_subset :
  "set T2 \<subseteq> set T1 \<Longrightarrow> set (after T2 xs) \<subseteq> set (after T1 xs)"
  unfolding after_set by auto

lemma set_alt_def :
  "set (PT m) = Set.insert [] (\<Union> x \<in> dom m . (Cons x) ` (set (the (m x))))"
  (is "?A m = ?B m")
proof 
  show "?A m \<subseteq> ?B m" 
  proof
    fix xs assume "xs \<in> ?A m"
    then have "isin (PT m) xs"
      by auto
    then show "xs \<in> ?B m"
    proof (induction xs arbitrary: m)
      case Nil
      then show ?case by auto
    next
      case (Cons x xs)
      then obtain t where "m x = Some t"
                      and "isin t xs"
        by (metis (no_types, lifting) case_optionE isin.simps(2)) 
      
      obtain m' where "t = PT m'"
        using prefix_tree.exhaust by blast
      then have "xs \<in> ?B m'"
        using \<open>isin t xs\<close> Cons.IH by blast
      moreover have "x \<in> dom m"
        using \<open>m x = Some t\<close>
        by auto
      ultimately show ?case 
        using \<open>m x = Some t\<close>
        using \<open>isin t xs\<close> \<open>t = PT m'\<close> 
        by fastforce  
    qed
  qed

  show "?B m \<subseteq> ?A m"
  proof
    fix xs assume "xs \<in> ?B m"
    then show "xs \<in> ?A m"
    proof (induction xs arbitrary: m)
      case Nil
      show ?case 
        by auto
    next
      case (Cons x xs)
      then have "x#xs \<in> (\<Union> x \<in> dom m . (Cons x) ` (set (the (m x))))"
        by auto
      then have "x \<in> dom m"
            and "xs \<in> (set (the (m x)))"
        by auto
      then obtain t where "m x = Some t" and "isin t xs"
        unfolding keys_is_none_rep
        by auto
      then show ?case
        by auto
    qed
  qed
qed



lemma finite_tree_iff :
  "finite_tree t = finite (set t)"
  (is "?P1 = ?P2")
proof 
  show "?P1 \<Longrightarrow> ?P2"
  proof induction
    case (PT m)
  
    have "set (PT m) = Set.insert [] (\<Union>x\<in>dom m. (#) x ` set (the (m x)))"
      unfolding set_alt_def by simp
    moreover have "finite (dom m)"
      using PT.prems by auto
    moreover have "\<And> x . x \<in> dom m \<Longrightarrow> finite ((#) x ` set (the (m x)))"
    proof -
      fix x assume "x \<in> dom m"
      then obtain y where "m x = Some y"
        by auto
      then have "y \<in> ran m"
        by (meson ranI)
      then have "finite_tree y"
        using PT.prems by auto
      then have "finite (set y)"
        using PT.IH[of "Some y" y] \<open>m x = Some y\<close>
        by (metis option.set_intros rangeI) 
      moreover have "(the (m x)) = y"
        using \<open>m x = Some y\<close> by auto
      ultimately show "finite ((#) x ` set (the (m x)))"
        by blast
    qed
    ultimately show ?case
      by simp 
  qed

  show "?P2 \<Longrightarrow> ?P1"
  proof (induction t)
    case (PT m)
  
    have "finite (dom m)"
    proof -
      have "\<And> x . x \<in> dom m \<Longrightarrow> [x] \<in> set (PT m)"
        using image_eqI by auto
      then have "(\<lambda>x . [x]) ` dom m \<subseteq> set (PT m)"
        by auto
      have "inj (\<lambda>x . [x])"
        by (meson inj_onI list.inject)    
      show ?thesis
        by (meson PT.prems UNIV_I \<open>(\<lambda>x. [x]) ` dom m \<subseteq> Prefix_Tree.set (PT m)\<close> \<open>inj (\<lambda>x. [x])\<close> inj_on_finite inj_on_subset subsetI)  
    qed
    moreover have "\<And> t . t \<in> ran m \<Longrightarrow> finite_tree t"
    proof -
      fix t assume "t \<in> ran m"
      then obtain x where "m x = Some t"
        unfolding ran_def by blast
      then have "(#) x ` set t \<subseteq> set (PT m)"
        unfolding set_alt_def
        by auto 
      then have "finite ((#) x ` set t)"
        using PT.prems
        by (simp add: finite_subset) 
      moreover have "inj ((#) x)"
        by auto 
      ultimately have "finite (set t)"
        by (simp add: finite_image_iff)
      then show "finite_tree t"
        using PT.IH[of "Some t" t] \<open>m x = Some t\<close>
        by (metis option.set_intros rangeI) 
    qed
    ultimately show ?case
      by simp 
  qed
qed
  
lemma empty_finite_tree : 
  "finite_tree empty"
  unfolding finite_tree_iff set_empty by auto

lemma insert_finite_tree : 
  assumes "finite_tree t"
  shows "finite_tree (insert t xs)"
proof -
  have "{xs'. \<exists>xs''. xs = xs' @ xs''} = list.set (prefixes xs)"
    unfolding prefixes_set by blast
  then have "finite {xs'. \<exists>xs''. xs = xs' @ xs''}" 
    using List.finite_set by simp
  then show ?thesis
    using assms unfolding finite_tree_iff insert_set 
    by blast
qed

lemma from_list_finite_tree : 
  "finite_tree (from_list xs)"
  using insert_finite_tree empty_finite_tree by (induction xs; auto)

lemma combine_after_finite_tree :
  assumes "finite_tree t1"
  and     "finite_tree t2"
shows "finite_tree (combine_after t1 \<alpha> t2)"
proof -
  have "finite (Prefix_Tree.set t2)" and "finite (Prefix_Tree.set t1)"
    using assms unfolding finite_tree_iff by auto
  then have "finite (Prefix_Tree.set (Prefix_Tree.insert t1 \<alpha>) \<union> {\<alpha> @ as |as. as \<in> Prefix_Tree.set t2})"
    using finite_tree_iff insert_finite_tree by fastforce
  then show ?thesis
    unfolding finite_tree_iff combine_after_set
    by (metis insert_set)
qed

lemma combine_finite_tree :
  assumes "finite_tree t1"
  and     "finite_tree t2"
shows "finite_tree (combine t1 t2)"
  using assms unfolding finite_tree_iff combine_set
  by blast


function (domintros) sorted_list_of_maximal_sequences_in_tree :: "('a :: linorder) prefix_tree \<Rightarrow> 'a list list" where
  "sorted_list_of_maximal_sequences_in_tree (PT m) = 
    (if dom m = {}
      then [[]]
      else concat (map (\<lambda>k . map ((#) k) (sorted_list_of_maximal_sequences_in_tree (the (m k)))) (sorted_list_of_set (dom m))))"
  by pat_completeness auto
termination 
proof -
  { fix a :: "'a prefix_tree"   

    have "sorted_list_of_maximal_sequences_in_tree_dom a" 
    proof (induction a)
      case (PT m)
      then show ?case
        by (metis List.set_empty domIff empty_iff option.set_sel range_eqI set_sorted_list_of_set sorted_list_of_maximal_sequences_in_tree.domintros sorted_list_of_set.fold_insort_key.infinite)
    qed
  }
  then show ?thesis by auto
qed


lemma sorted_list_of_maximal_sequences_in_tree_Nil :
  assumes "[] \<in> list.set (sorted_list_of_maximal_sequences_in_tree t)" 
shows "t = empty"
proof -
  obtain m where "t = PT m"
    using prefix_tree.exhaust by blast

  show ?thesis proof (cases "dom m = {}")
    case True
    then have "m = Map.empty"
      using True by blast
    then show ?thesis
      unfolding \<open>t = PT m\<close>
      by (simp add: Prefix_Tree.empty_def)
  next
    case False
    then have "[] \<in> list.set (concat (map (\<lambda>k . map ((#) k) (sorted_list_of_maximal_sequences_in_tree (the (m k)))) (sorted_list_of_set (dom m))))"
      using assms unfolding \<open>t = PT m\<close> by auto
    then show ?thesis
      by auto 
  qed
qed

lemma sorted_list_of_maximal_sequences_in_tree_set :
  assumes "finite_tree t"
  shows "list.set (sorted_list_of_maximal_sequences_in_tree t) = {y. y \<in> set t \<and> \<not>(\<exists> y' . y' \<noteq> [] \<and> y@y' \<in> set t)}"
    (is "?S1 = ?S2")
proof 
  show "?S1 \<subseteq> ?S2"
  proof 
    fix xs assume "xs \<in> ?S1"
    then show "xs \<in> ?S2"
    proof (induction xs arbitrary: t)
      case Nil
      then have "t = empty"
        using sorted_list_of_maximal_sequences_in_tree_Nil by auto
      then show ?case 
        using set_empty by auto
    next
      case (Cons x xs)

      obtain m where "t = PT m"
        using prefix_tree.exhaust by blast
      have "x#xs \<in> list.set (concat (map (\<lambda>k . map ((#) k) (sorted_list_of_maximal_sequences_in_tree (the (m k)))) (sorted_list_of_set (dom m))))"
        by (metis (no_types) Cons.prems(1) \<open>t = PT m\<close> empty_iff list.set(1) list.simps(3) set_ConsD sorted_list_of_maximal_sequences_in_tree.simps)
      then have "x \<in> list.set (sorted_list_of_set (dom m))"
            and "xs \<in> list.set (sorted_list_of_maximal_sequences_in_tree (the (m x)))"
        by auto

      have "x \<in> dom m"
        using \<open>x \<in> list.set (sorted_list_of_set (dom m))\<close> unfolding \<open>t = PT m\<close>
        by (metis equals0D list.set(1) sorted_list_of_set.fold_insort_key.infinite sorted_list_of_set.set_sorted_key_list_of_set)
      then obtain t' where "m x = Some t'"
        by auto
      then have "xs \<in> list.set (sorted_list_of_maximal_sequences_in_tree t')"
        using \<open>xs \<in> list.set (sorted_list_of_maximal_sequences_in_tree (the (m x)))\<close> 
        by auto
      then have "xs \<in> set t'" and "\<not>(\<exists> y' . y' \<noteq> [] \<and> xs@y' \<in> set t')"
        using Cons.IH by blast+

      have "x#xs \<in> set t"
        unfolding \<open>t = PT m\<close> using \<open>xs \<in> set t'\<close> \<open>m x = Some t'\<close> by auto
      moreover have "\<not>(\<exists> y' . y' \<noteq> [] \<and> (x#xs)@y' \<in> set t)"
      proof 
        assume "\<exists>y'. y' \<noteq> [] \<and> (x # xs) @ y' \<in> Prefix_Tree.set t"
        then obtain y' where "y' \<noteq> []" and "(x # xs) @ y' \<in> Prefix_Tree.set t"
          by blast
        then have "isin (PT m) (x # (xs @ y'))"
          unfolding \<open>t = PT m\<close> by auto
        then have "isin t' (xs @ y')"
          using \<open>m x = Some t'\<close> by auto
        then have "\<exists> y' . y' \<noteq> [] \<and> xs@y' \<in> set t'"
          using \<open>y' \<noteq> []\<close> by auto
        then show False
          using \<open>\<not>(\<exists> y' . y' \<noteq> [] \<and> xs@y' \<in> set t')\<close> by simp
      qed
      ultimately show ?case by blast
    qed
  qed

  show "?S2 \<subseteq> ?S1"
  proof 
    fix xs assume "xs \<in> ?S2"
    then show "xs \<in> ?S1"
    using assms proof (induction xs arbitrary: t)
      case Nil
      then have "set t = {[]}"
        by auto
      moreover obtain m where "t = PT m"
        using prefix_tree.exhaust by blast
      ultimately have "\<And> x . \<not> isin (PT m) [x]"
        by force
      moreover have "\<And> x . x \<in> dom m \<Longrightarrow> isin (PT m) [x]"
        by auto
      ultimately have "dom m = {}"
        by blast
      then show ?case
        unfolding \<open>t = PT m\<close> by auto
    next
      case (Cons x xs)

      obtain m where "t = PT m"
        using prefix_tree.exhaust by blast
      then have "isin (PT m) (x#xs)"
        using Cons.prems(1) by auto
      then obtain t' where "m x = Some t'"
                       and "isin t' xs"
        by (metis case_optionE isin.simps(2))
      then have "x \<in> dom m"
        by auto
      then have "dom m \<noteq> {}"
        by auto

      have "finite_tree t'"
        using \<open>finite_tree t\<close> \<open>m x = Some t'\<close> unfolding \<open>t = PT m\<close>
        by (meson finite_tree.simps ranI) 
      moreover have "xs \<in> {y \<in> Prefix_Tree.set t'. \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> Prefix_Tree.set t'}"
      proof -
        have "xs \<in> set t'"
          using \<open>isin t' xs\<close> by auto
        moreover have "(\<nexists>y'. y' \<noteq> [] \<and> xs @ y' \<in> Prefix_Tree.set t')"
        proof 
          assume "\<exists>y'. y' \<noteq> [] \<and> xs @ y' \<in> Prefix_Tree.set t'"
          then obtain y' where "y' \<noteq> []" and "xs @ y' \<in> Prefix_Tree.set t'"
            by blast
          then have "isin t' (xs@y')"
            by auto
          then have "isin (PT m) (x#(xs@y'))"
            using \<open>m x = Some t'\<close> by auto
          then show False
            using Cons.prems(1) \<open>y' \<noteq> []\<close> unfolding \<open>t = PT m\<close> by auto
        qed
        ultimately show ?thesis
          by blast
      qed
      ultimately have "xs \<in> list.set (sorted_list_of_maximal_sequences_in_tree t')"
        using Cons.IH by blast
      moreover have "x \<in> list.set (sorted_list_of_set (dom m))"
        using \<open>x \<in> dom m\<close> \<open>finite_tree t\<close> unfolding \<open>t = PT m\<close>
        by simp
      ultimately show ?case
        using \<open>finite_tree t\<close> \<open>dom m \<noteq> {}\<close> \<open>m x = Some t'\<close> unfolding \<open>t = PT m\<close> 
        by force
    qed
  qed
qed


lemma sorted_list_of_maximal_sequences_in_tree_ob :
  assumes "finite_tree T"
  and     "xs \<in> set T"
obtains xs' where "xs@xs' \<in> list.set (sorted_list_of_maximal_sequences_in_tree T)"
proof -
  let ?xs = "{xs@xs' | xs' . xs@xs' \<in> set T}"

  let ?xs' = "arg_max_on length ?xs"

  have "xs \<in> ?xs"
    using assms(2) by auto
  then have "?xs \<noteq> {}"
    by blast
  moreover have "finite ?xs"
    using finite_subset[of ?xs "set T"]
    using assms(1) unfolding finite_tree_iff 
    by blast
  ultimately obtain xs' where "xs' \<in> ?xs" and "\<And> xs'' . xs'' \<in> ?xs \<Longrightarrow> length xs'' \<le> length xs'"
    using max_length_elem[of ?xs]
    by force

  obtain xs'' where "xs' = xs@xs''" and "xs@xs'' \<in> set T"
    using \<open>xs' \<in> ?xs\<close> by auto
  have "\<And> xs''' . xs@xs''' \<in> set T \<Longrightarrow> length xs''' \<le> length xs''"
  proof -
    fix xs''' assume "xs@xs''' \<in> set T"
    then have "xs@xs''' \<in> ?xs"
      by auto
    then have "length (xs@xs''')  \<le> length xs'"
      using \<open>\<And> xs'' . xs'' \<in> ?xs \<Longrightarrow> length xs'' \<le> length xs'\<close> 
      by blast
    then show "length xs''' \<le> length xs''"
      unfolding \<open>xs' = xs@xs''\<close> by auto
  qed
  then have "\<not>(\<exists> y' . y' \<noteq> [] \<and> (xs@xs'')@y' \<in> set T)"
    by fastforce
  then have "xs@xs'' \<in> list.set (sorted_list_of_maximal_sequences_in_tree T)"
    using \<open>xs@xs'' \<in> set T\<close>
    unfolding sorted_list_of_maximal_sequences_in_tree_set[OF assms(1)]
    by blast
  then show ?thesis using that by blast
qed


function (domintros) sorted_list_of_sequences_in_tree :: "('a :: linorder) prefix_tree \<Rightarrow> 'a list list" where
  "sorted_list_of_sequences_in_tree (PT m) = 
    (if dom m = {}
      then [[]]
      else [] # concat (map (\<lambda>k . map ((#) k) (sorted_list_of_sequences_in_tree (the (m k)))) (sorted_list_of_set (dom m))))"
  by pat_completeness auto
termination 
proof -
  {
    fix a :: "'a prefix_tree"   
  
    have "sorted_list_of_sequences_in_tree_dom a" 
    proof (induction a)
      case (PT m)
      then show ?case
        by (metis List.set_empty domIff emptyE option.set_sel rangeI sorted_list_of_sequences_in_tree.domintros sorted_list_of_set.fold_insort_key.infinite sorted_list_of_set.set_sorted_key_list_of_set)
    qed
  }
  then show ?thesis by auto
qed

lemma sorted_list_of_sequences_in_tree_set :
  assumes "finite_tree t"
  shows "list.set (sorted_list_of_sequences_in_tree t) = set t"
    (is "?S1 = ?S2")
proof 
  show "?S1 \<subseteq> ?S2"
  proof 
    fix xs assume "xs \<in> ?S1"
    then show "xs \<in> ?S2"
    proof (induction xs arbitrary: t)
      case Nil
      then show ?case 
        using set_empty by auto
    next
      case (Cons x xs)

      obtain m where "t = PT m"
        using prefix_tree.exhaust by blast
      have "x#xs \<in> list.set (concat (map (\<lambda>k . map ((#) k) (sorted_list_of_sequences_in_tree (the (m k)))) (sorted_list_of_set (dom m))))"
        by (metis (no_types) Cons.prems(1) \<open>t = PT m\<close> empty_iff list.set(1) list.simps(3) set_ConsD sorted_list_of_sequences_in_tree.simps)
      then have "x \<in> list.set (sorted_list_of_set (dom m))"
            and "xs \<in> list.set (sorted_list_of_sequences_in_tree (the (m x)))"
        by auto

      have "x \<in> dom m"
        using \<open>x \<in> list.set (sorted_list_of_set (dom m))\<close> unfolding \<open>t = PT m\<close>
        by (metis emptyE empty_set sorted_list_of_set.fold_insort_key.infinite sorted_list_of_set.set_sorted_key_list_of_set)
      then obtain t' where "m x = Some t'"
        by auto
      then have "xs \<in> list.set (sorted_list_of_sequences_in_tree t')"
        using \<open>xs \<in> list.set (sorted_list_of_sequences_in_tree (the (m x)))\<close> 
        by auto
      then have "xs \<in> set t'" 
        using Cons.IH by blast+

      show "x#xs \<in> set t"
        unfolding \<open>t = PT m\<close> using \<open>xs \<in> set t'\<close> \<open>m x = Some t'\<close> by auto
    qed
  qed

  show "?S2 \<subseteq> ?S1"
  proof 
    fix xs assume "xs \<in> ?S2"
    then show "xs \<in> ?S1"
    using assms proof (induction xs arbitrary: t)
      case Nil
      obtain m where "t = PT m"
        using prefix_tree.exhaust by blast
      then show ?case 
        by auto
    next
      case (Cons x xs)

      obtain m where "t = PT m"
        using prefix_tree.exhaust by blast
      then have "isin (PT m) (x#xs)"
        using Cons.prems(1) by auto
      then obtain t' where "m x = Some t'"
                       and "isin t' xs"
        by (metis case_optionE isin.simps(2))
      then have "x \<in> dom m"
        by auto
      then have "dom m \<noteq> {}"
        by auto

      have "finite_tree t'"
        using \<open>finite_tree t\<close> \<open>m x = Some t'\<close> unfolding \<open>t = PT m\<close>
        by (meson finite_tree.simps ranI) 
      moreover have "xs \<in> set t'"
        using \<open>isin t' xs\<close> by auto
      ultimately have "xs \<in> list.set (sorted_list_of_sequences_in_tree t')"
        using Cons.IH by blast
      moreover have "x \<in> list.set (sorted_list_of_set (dom m))"
        using \<open>x \<in> dom m\<close> \<open>finite_tree t\<close> unfolding \<open>t = PT m\<close>
        by simp
      ultimately show ?case
        using \<open>finite_tree t\<close> \<open>dom m \<noteq> {}\<close> \<open>m x = Some t'\<close> unfolding \<open>t = PT m\<close> 
        by force
    qed
  qed
qed





fun difference_list :: "('a::linorder) prefix_tree \<Rightarrow> 'a prefix_tree \<Rightarrow> 'a list list" where
  "difference_list t1 t2 = filter (\<lambda> xs . \<not> isin t2 xs) (sorted_list_of_sequences_in_tree t1)"

lemma difference_list_set :
  assumes "finite_tree t1"
shows "List.set (difference_list t1 t2) = (set t1 - set t2)"
  unfolding difference_list.simps 
            filter_set[symmetric]
            sorted_list_of_sequences_in_tree_set[OF assms]
            set.simps
  by fastforce

fun is_leaf :: "'a prefix_tree \<Rightarrow> bool" where
  "is_leaf t = (t = empty)"

fun is_maximal_in :: "'a prefix_tree \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_maximal_in T \<alpha> = (isin T \<alpha> \<and> is_leaf (after T \<alpha>))"

function (domintros) height :: "'a prefix_tree \<Rightarrow> nat" where
  "height (PT m) = (if (is_leaf (PT m)) then 0 else 1 + Max (height ` ran m))"
  by pat_completeness auto
termination 
proof -
  { fix a :: "'a prefix_tree"   

    have "height_dom a" 
    proof (induction a)
      case (PT m)
  
      have "(\<And>x. x \<in> ran m \<Longrightarrow> height_dom x)"
      proof -
        fix x :: "'a prefix_tree"
        assume "x \<in> ran m"
        then have "\<exists>a. m a = Some x"
          by (simp add: ran_def)
        then show "height_dom x"
          using PT.IH by blast
      qed  
      then show ?case
        using height.domintros
        by blast 
    qed
  }
  then show ?thesis by auto
qed

function (domintros) height_over :: "'a list \<Rightarrow> 'a prefix_tree \<Rightarrow> nat" where
  "height_over xs (PT m) = 1 + foldr (\<lambda> x maxH . case m x of Some t' \<Rightarrow> max (height_over xs t') maxH | None \<Rightarrow> maxH) xs 0"
  by pat_completeness auto
termination 
proof -
  {
    fix a :: "'a prefix_tree"   
    fix xs :: "'a list"
  
    have "height_over_dom (xs, a)" 
    proof (induction a)
      case (PT m)
  
      have "(\<And>x. x \<in> ran m \<Longrightarrow> height_over_dom (xs, x))"
      proof -
        fix x :: "'a prefix_tree"
        assume "x \<in> ran m"
        then have "\<exists>a. m a = Some x"
          by (simp add: ran_def)
        then show "height_over_dom (xs, x)"
          using PT.IH by blast
      qed  
      then show ?case
        using height_over.domintros
        by (simp add: height_over.domintros ranI)
    qed
  }
  then show ?thesis by auto
qed

lemma height_over_empty :
  "height_over xs empty = 1"
proof -
  define xs' where "xs' = xs"
  have "foldr (\<lambda> x maxH . case Map.empty x of Some t' \<Rightarrow> max (height_over xs' t') maxH | None \<Rightarrow> maxH) xs 0 = 0"
    by (induction xs; auto)
  then show ?thesis
    unfolding xs'_def empty_def 
    by auto
qed


lemma height_over_subtree_less :
  assumes "m x = Some t'"
  and     "x \<in> list.set xs"
shows "height_over xs t' < height_over xs (PT m)"
proof -

  define xs' where "xs' = xs"

  have "height_over xs' t' \<le> foldr (\<lambda> x maxH . case m x of Some t' \<Rightarrow> max (height_over xs' t') maxH | None \<Rightarrow> maxH) xs 0"
    using assms(2) proof (induction xs)
    case Nil
    then show ?case by auto
  next
    case (Cons x' xs)

    define f where "f = foldr (\<lambda> x maxH . case m x of Some t' \<Rightarrow> max (height_over xs' t') maxH | None \<Rightarrow> maxH) xs 0"

    have *: "foldr (\<lambda> x maxH . case m x of Some t' \<Rightarrow> max (height_over xs' t') maxH | None \<Rightarrow> maxH) (x'#xs) 0
              = (case m x' of Some t' \<Rightarrow> max (height_over xs' t') f | None \<Rightarrow> f)"
      unfolding f_def by auto

    show ?case proof (cases "x=x'")
      case True
      show ?thesis 
        using \<open>m x = Some t'\<close>
        unfolding * True by auto
    next
      case False
      then have "x \<in> list.set xs"
        using Cons.prems(1) by auto
      show ?thesis
        using Cons.IH[OF \<open>x \<in> list.set xs\<close>]
        unfolding * f_def[symmetric] 
        by (cases "m x'"; auto)
    qed
  qed
  then show ?thesis
    unfolding xs'_def by auto
qed


fun maximum_prefix :: "'a prefix_tree \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "maximum_prefix t [] = []" |
  "maximum_prefix (PT m) (x # xs) = (case m x of None \<Rightarrow> [] | Some t \<Rightarrow> x # maximum_prefix t xs)"

lemma maximum_prefix_isin :
  "isin t (maximum_prefix t xs)"
proof (induction xs arbitrary: t)
  case Nil
  show ?case 
    by auto
next
  case (Cons x xs)

  obtain m where *:"t = PT m"
    using finite_tree.cases by blast

  show ?case proof (cases "m x")
    case None
    then have "maximum_prefix t (x#xs) = []"
      unfolding * by auto
    then show ?thesis 
      by auto
  next
    case (Some t')
    then have "maximum_prefix t (x#xs) = x # maximum_prefix t' xs"
      unfolding * by auto
    moreover have "isin t' (maximum_prefix t' xs)"
      using Cons.IH by auto
    ultimately show ?thesis
      by (simp add: "*" Some)
  qed
qed


lemma maximum_prefix_maximal :
  "maximum_prefix t xs = xs 
    \<or> (\<exists> x' xs' . xs = (maximum_prefix t xs)@[x']@xs' \<and> \<not> isin t ((maximum_prefix t xs)@[x']))"
proof (induction xs arbitrary: t)
  case Nil
  show ?case by auto
next
  case (Cons x xs)
  obtain m where *:"t = PT m"
    using finite_tree.cases by blast

  show ?case proof (cases "m x")
    case None
    then have "maximum_prefix t (x#xs) = []"
      unfolding * by auto
    moreover have "\<not> isin t ([]@[x]@xs)"
      using isin_prefix[of t "[x]" xs]
      by (simp add: "*" None)
    ultimately show ?thesis
      by (simp add: "*" None)
  next
    case (Some t')
    then have "maximum_prefix t (x#xs) = x # maximum_prefix t' xs"
      unfolding * by auto
    moreover note Cons.IH[of t']
    ultimately show ?thesis
      by (simp add: "*" Some) 
  qed
qed





(* collects for sequence xs all sequences ys in the tree such that ys is maximal in the tree and 
   (map fst ys) is a prefix of (map fst xs) *)
fun maximum_fst_prefixes :: "('a\<times>'b) prefix_tree \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a\<times>'b) list list" where
  "maximum_fst_prefixes t [] ys = (if is_leaf t then [[]] else [])" |
  "maximum_fst_prefixes (PT m) (x # xs) ys = (if is_leaf (PT m) then [[]] else concat (map (\<lambda> y . map ((#) (x,y)) (maximum_fst_prefixes (the (m (x,y))) xs ys)) (filter (\<lambda> y . (m (x,y) \<noteq> None)) ys)))"

lemma maximum_fst_prefixes_set :
  "list.set (maximum_fst_prefixes t xs ys) \<subseteq> set t"
proof (induction xs arbitrary: t)
  case Nil
  show ?case 
    by auto
next
  case (Cons x xs)

  obtain m where *:"t = PT m"
    using finite_tree.cases by blast

  show "list.set (maximum_fst_prefixes t (x # xs) ys) \<subseteq> set t"
  proof 
    fix p assume "p \<in> list.set (maximum_fst_prefixes t (x # xs) ys)"

    show "p \<in> set t" proof (cases "is_leaf (PT m)")
      case True
      then have "p = []"
        using \<open>p \<in> list.set (maximum_fst_prefixes t (x # xs) ys)\<close>  unfolding * maximum_fst_prefixes.simps by force
      then show ?thesis 
        using set_Nil[of t] 
        by blast
    next
      case False
      then obtain y where "y \<in> list.set (filter (\<lambda> y . (m (x,y) \<noteq> None)) ys)"
                    and "p \<in> list.set (map ((#) (x,y)) (maximum_fst_prefixes (the (m (x,y))) xs ys))"
        using \<open>p \<in> list.set (maximum_fst_prefixes t (x # xs) ys)\<close>
        unfolding * by auto

      then have "m (x,y) \<noteq> None"
        by auto
      then obtain t' where "m (x,y) = Some t'"
        by auto
      moreover obtain p' where "p = (x,y)#p'" and "p' \<in> list.set (maximum_fst_prefixes (the (m (x,y))) xs ys)"
        using \<open>p \<in> list.set (map ((#) (x,y)) (maximum_fst_prefixes (the (m (x,y))) xs ys))\<close>
        by auto
      ultimately have "isin t' p'"
        using Cons.IH
        by auto 
      then have "isin t p"
        unfolding * \<open>p = (x,y)#p'\<close> using \<open>m (x,y) = Some t'\<close> by auto
      then show "p \<in> set t"
        by auto
    qed
  qed
qed

lemma maximum_fst_prefixes_are_prefixes :
  assumes "xys \<in> list.set (maximum_fst_prefixes t xs ys)"
  shows "map fst xys = take (length xys) xs"
using assms proof (induction xys arbitrary: t xs)
  case Nil
  then show ?case by auto
next
  case (Cons xy xys)
  then have "xs \<noteq> []"
    by auto
  then obtain x xs' where "xs = x#xs'"
    using list.exhaust by auto
    
  obtain m where *:"t = PT m"
    using finite_tree.cases by blast
  have "is_leaf (PT m) = False"
    using Cons.prems unfolding * \<open>xs = x#xs'\<close>
    by auto
  have "(xy#xys) \<in> list.set (concat (map (\<lambda> y . map ((#) (x,y)) (maximum_fst_prefixes (the (m (x,y))) xs' ys)) (filter (\<lambda> y . (m (x,y) \<noteq> None)) ys)))"
    using Cons.prems unfolding * \<open>xs = x#xs'\<close> \<open>is_leaf (PT m) = False\<close> maximum_fst_prefixes.simps by auto
  then obtain y where "y \<in> list.set (filter (\<lambda> y . (m (x,y) \<noteq> None)) ys)"
                  and "(xy#xys) \<in> list.set (map ((#) (x,y)) (maximum_fst_prefixes (the (m (x,y))) xs' ys))"
    by auto
  then have "xy = (x,y)" and "xys \<in> list.set (maximum_fst_prefixes (the (m (x,y))) xs' ys)"
    by auto

  have **: "take (length ((x, y) # xys)) (x # xs') = x # (take (length xys) xs')"
    by auto

  show ?case
    using Cons.IH[OF \<open>xys \<in> list.set (maximum_fst_prefixes (the (m (x,y))) xs' ys)\<close>]
    unfolding \<open>xy = (x,y)\<close> \<open>xs = x#xs'\<close> ** by auto
qed



lemma finite_tree_set_eq : 
  assumes "set t1 = set t2"
  and     "finite_tree t1"
  shows "t1 = t2"
using assms proof (induction "height t1" arbitrary: t1 t2 rule: less_induct)
  case less

  obtain m1 m2 where "t1 = PT m1" and "t2 = PT m2"
    by (metis finite_tree.cases) 

  show ?case proof (cases "height t1")
    case 0
    
    have "t1 = empty"
      using 0
      unfolding \<open>t1 = PT m1\<close> height.simps is_leaf.simps
      by (metis add_is_0 zero_neq_one) 
    then have "set t2 = {[]}"
      using less Prefix_Tree.set_empty by auto 
    have "m2 = Map.empty" 
    proof 
      show "\<And>x. m2 x = None"
      proof -
        fix x show "m2 x = None"
        proof (rule ccontr) 
          assume "m2 x \<noteq> None"
          then obtain t' where "m2 x = Some t'"
            by blast 
          then have "[x] \<in> set t2" 
            unfolding \<open>t2 = PT m2\<close> set.simps by auto
          then show False
            using \<open>set t2 = {[]}\<close> by auto
        qed
      qed
    qed
    then show ?thesis 
      unfolding \<open>t1 = empty\<close> \<open>t2 = PT m2\<close> empty_def by simp
  next
    case (Suc k)

    
    show ?thesis proof (rule ccontr)
      assume "t1 \<noteq> t2"

      then have "m1 \<noteq> m2"
        using \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> by auto
      then obtain x where "m1 x \<noteq> m2 x"
        by (meson ext)

      then consider "m1 x \<noteq> None \<and> m2 x \<noteq> None" | "m1 x = None \<longleftrightarrow> m2 x \<noteq> None"
        by fastforce
      then show False proof cases
        case 1
        then obtain t1' t2' where "m1 x = Some t1'" and "m2 x = Some t2'"
          by auto
        then have "t1' \<noteq> t2'"
          using \<open>m1 x \<noteq> m2 x\<close> by auto
        moreover have "set t1' = set t2'" 
        proof -
          have "\<And> io . isin t1' io = isin t1 (x#io)"
            unfolding \<open>t1 = PT m1\<close> using \<open>m1 x = Some t1'\<close> by auto
          moreover have "\<And> io . isin t2' io = isin t2 (x#io)"
            unfolding \<open>t2 = PT m2\<close> using \<open>m2 x = Some t2'\<close> by auto
          ultimately show ?thesis
            using less.prems(1)
            by (metis Collect_cong mem_Collect_eq set.simps) 
        qed
        moreover have "height t1' < height t1"
        proof -
          have "height t1 = 1 + Max (height ` ran m1)"
            using Suc 
            unfolding \<open>t1 = PT m1\<close> height.simps 
            by (meson Zero_not_Suc) 
          moreover have "height t1' \<in> height ` ran m1"
            using \<open>m1 x = Some t1'\<close>
            by (meson image_eqI ranI) 
          moreover have "finite (ran m1)"
            using less.prems(2) 
            unfolding \<open>t1 = PT m1\<close> finite_tree.simps
            by (simp add: finite_ran) 
          ultimately have "height t1 \<ge> 1 + height t1'"
            by simp
          then show ?thesis by auto
        qed
        moreover have "finite_tree t1'"
          using less.prems(2) 
          unfolding \<open>t1 = PT m1\<close> finite_tree.simps
          by (meson \<open>m1 x = Some t1'\<close> ranI)  
        ultimately show False 
          using less.hyps[of t1' t2']
          by blast
      next
        case 2
        then have "isin t1 [x] \<noteq> isin t2 [x]"
          unfolding \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> by auto
        then show False using less.prems(1) by auto
      qed   
    qed
  qed
qed




(* obtain all trees after an input trace *)
fun after_fst :: "('a \<times> 'b) prefix_tree \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) prefix_tree" where
  "after_fst t [] ys = t" |
  "after_fst (PT m) (x # xs) ys = foldr (\<lambda> y t . case m (x,y) of None \<Rightarrow> t | Some t' \<Rightarrow> combine t (after_fst t' xs ys)) ys empty"



subsection \<open>Alternative characterization for code generation\<close>

text \<open>In order to generate code for the prefix trees, we represent the map inside each prefix tree
      by Mapping.\<close>

definition MPT :: "('a,'a prefix_tree) mapping \<Rightarrow> 'a prefix_tree" where
  "MPT m = PT (Mapping.lookup m)"

code_datatype MPT

lemma equals_MPT[code]: "equal_class.equal (MPT m1) (MPT m2) = (m1 = m2)" 
proof -
  have "equal_class.equal (MPT m1) (MPT m2) = equal_class.equal (PT (Mapping.lookup m1)) (PT (Mapping.lookup m2))"
    unfolding MPT_def by simp
  also have "\<dots> = ((Mapping.lookup m1) = (Mapping.lookup m2))"
    using prefix_tree.eq.simps by auto
  also have "\<dots> = (m1 = m2)"
    by (simp add: Mapping.lookup.rep_eq rep_inject)
  finally show ?thesis .
qed

lemma empty_MPT[code] :
  "empty = MPT Mapping.empty"
  unfolding MPT_def empty_def
  by (metis lookup_empty) 

lemma insert_MPT[code] :
  "insert (MPT m) xs = (case xs of
    [] \<Rightarrow> (MPT m) |
    (x#xs) \<Rightarrow> MPT (Mapping.update x (insert (case Mapping.lookup m x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') xs) m))"
  apply (cases xs; simp)
  by (simp add: MPT_def lookup.rep_eq update.rep_eq)  

lemma isin_MPT[code] :
  "isin (MPT m) xs = (case xs of
    [] \<Rightarrow> True |
    (x#xs) \<Rightarrow> (case Mapping.lookup m x of None \<Rightarrow> False | Some t \<Rightarrow> isin t xs))"
  unfolding MPT_def by (cases xs; auto)

lemma after_MPT[code] :
  "after (MPT m) xs = (case xs of
    [] \<Rightarrow> MPT m |
    (x#xs) \<Rightarrow> (case Mapping.lookup m x of None \<Rightarrow> empty | Some t \<Rightarrow> after t xs))"
  unfolding MPT_def by (cases xs; auto)

lemma PT_Mapping_ob : 
  fixes t :: "'a prefix_tree"
  obtains m where "t = MPT m"
proof -
  obtain m' where "t = PT m'"
    using prefix_tree.exhaust by blast 
  then have "t = MPT (Mapping m')" 
    unfolding MPT_def
    by (simp add: Mapping_inverse lookup.rep_eq) 
  then show ?thesis using that by blast
qed


lemma set_MPT[code] :
  "set (MPT m) = Set.insert [] (\<Union> x \<in> Mapping.keys m . (Cons x) ` (set (the (Mapping.lookup m x))))"
  unfolding MPT_def set_alt_def keys_dom_lookup by simp


lemma combine_MPT[code] : 
  "combine (MPT m1) (MPT m2) = MPT (Mapping.combine combine m1 m2)"  
proof -
  have "combine (MPT m1) (MPT m2) = combine (PT (Mapping.lookup m1)) (PT (Mapping.lookup m2))"
    unfolding MPT_def by simp
  also have "\<dots> = PT (\<lambda>x . combine_options combine ((Mapping.lookup m1) x) ((Mapping.lookup m2) x))"
    unfolding combine.simps
    by (simp add: combine_options_def)
  ultimately show ?thesis
    by (metis MPT_def combine.abs_eq lookup.abs_eq rep_inverse) 
qed


lemma combine_after_MPT[code] :
  "combine_after (MPT m) xs t = (case xs of
    [] \<Rightarrow> combine (MPT m) t |
    (x#xs) \<Rightarrow> MPT (Mapping.update x (combine_after (case Mapping.lookup m x of None \<Rightarrow> empty | Some t' \<Rightarrow> t') xs t) m))"
  apply (cases xs; simp)
  by (simp add: MPT_def lookup.rep_eq update.rep_eq)  


lemma finite_tree_MPT[code] :
  "finite_tree (MPT m) = (finite (Mapping.keys m) \<and> (\<forall> x \<in> Mapping.keys m . finite_tree (the (Mapping.lookup m x))))"
  unfolding MPT_def finite_tree.simps keys_dom_lookup ran_dom_the_eq[symmetric] by blast


lemma sorted_list_of_maximal_sequences_in_tree_MPT[code] :
  "sorted_list_of_maximal_sequences_in_tree (MPT m) = 
    (if Mapping.keys m = {}
      then [[]]
      else concat (map (\<lambda>k . map ((#) k) (sorted_list_of_maximal_sequences_in_tree (the (Mapping.lookup m k)))) (sorted_list_of_set (Mapping.keys m))))"
  unfolding MPT_def sorted_list_of_maximal_sequences_in_tree.simps keys_dom_lookup by simp

lemma is_leaf_MPT[code]:
  "is_leaf (MPT m) = (Mapping.is_empty m)"
  by (simp add: MPT_def Mapping.is_empty_def Prefix_Tree.empty_def keys_dom_lookup)

lemma height_MPT[code] :
  "height (MPT m) = (if (is_leaf (MPT m)) then 0 else 1 + Max ((height \<circ> the \<circ> Mapping.lookup m) ` Mapping.keys m))"
proof -
  have "height (MPT m) = (if (is_leaf (MPT m)) then 0 else 1 + Max (height ` ((\<lambda>k . the (Mapping.lookup m k)) ` Mapping.keys m)))"
    by (simp add: MPT_def keys_dom_lookup ran_dom_the_eq)
  moreover have "(height ` ((\<lambda>k . the (Mapping.lookup m k)) ` Mapping.keys m)) = ((height \<circ> the \<circ> Mapping.lookup m) ` Mapping.keys m)"
    by auto
  ultimately show ?thesis 
    by auto
qed


lemma maximum_prefix_MPT[code]:
  "maximum_prefix (MPT m) xs = (case xs of
    [] \<Rightarrow> [] |
    (x#xs) \<Rightarrow> (case Mapping.lookup m x of None \<Rightarrow> [] | Some t \<Rightarrow> x # maximum_prefix t xs))"
  apply (cases xs; simp)
  by (simp add: MPT_def lookup.rep_eq)  

lemma sorted_list_of_in_tree_MPT[code] :
  "sorted_list_of_sequences_in_tree (MPT m) = 
    (if Mapping.keys m = {}
      then [[]]
      else [] # concat (map (\<lambda>k . map ((#) k) (sorted_list_of_sequences_in_tree (the (Mapping.lookup m k)))) (sorted_list_of_set (Mapping.keys m))))"
  unfolding MPT_def sorted_list_of_sequences_in_tree.simps keys_dom_lookup by simp

lemma maximum_fst_prefixes_leaf: 
  fixes xs :: "'a list" and ys :: "'b list"
shows "maximum_fst_prefixes empty xs ys  = [[]]"
proof -
  have "is_leaf (empty :: ('a\<times>'b)prefix_tree)" by auto
  
  obtain m where "(empty :: ('a\<times>'b)prefix_tree) = PT m"
    using prefix_tree.exhaust by blast 

  show ?thesis proof (cases xs)
    case Nil
    then show ?thesis by auto
  next
    case (Cons x xs)
    show ?thesis 
      using \<open>is_leaf (empty :: ('a\<times>'b)prefix_tree) \<close>
      unfolding \<open>(empty :: ('a\<times>'b)prefix_tree) = PT m\<close>  Cons maximum_fst_prefixes.simps by force
  qed
qed

lemma maximum_fst_prefixes_MPT[code]:
  "maximum_fst_prefixes (MPT m) xs ys = (case xs of
    [] \<Rightarrow> (if is_leaf (MPT m) then [[]] else []) |
    (x # xs) \<Rightarrow> (if is_leaf (MPT m) then [[]] else concat (map (\<lambda> y . map ((#) (x,y)) (maximum_fst_prefixes (the (Mapping.lookup m (x,y))) xs ys)) (filter (\<lambda> y . (Mapping.lookup m (x,y) \<noteq> None)) ys))))"
  using maximum_fst_prefixes_leaf
  apply (cases xs) 
    apply auto[1]
  by (simp add: MPT_def lookup.rep_eq)  









(* The following function computes the maximum prefix xs' of xs such that there exists
   a sequence ys in the tree with (map fst xs' = map fst ys).
   Requires theory Polynomials.OAlist.
   
fun maximum_fst_prefix :: "('a\<times>'b) prefix_tree \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a\<times>'b) list" where
  "maximum_fst_prefix t [] ys = []" |
  "maximum_fst_prefix (PT m) (x # xs) ys = 
    (case (map (\<lambda> y . (x,y) # maximum_fst_prefix (the (m (x,y))) xs ys) (filter (\<lambda> y . (m (x,y) \<noteq> None)) ys)) of
      [] \<Rightarrow> [] |
      (p'#ps) \<Rightarrow> min_list_param (\<lambda> a b . length a > length b) (p'#ps))"

lemma maximum_fst_prefix_isin :
  "isin t (maximum_fst_prefix t xs ys)"
proof (induction xs arbitrary: t)
  case Nil
  show ?case 
    by auto
next
  case (Cons x xs)

  obtain m where *:"t = PT m"
    using finite_tree.cases by blast

  show ?case proof (cases "(map (\<lambda> y . (x,y) # maximum_fst_prefix (the (m (x,y))) xs ys) (filter (\<lambda> y . (m (x,y) \<noteq> None)) ys))")
    case Nil
    then show ?thesis  unfolding * by auto
  next
    case (Cons p' ps)

    then have "maximum_fst_prefix t (x # xs) ys = min_list_param (\<lambda> a b . length a > length b) (p'#ps)"
      unfolding * by auto
    then have "maximum_fst_prefix t (x # xs) ys \<in> list.set (p'#ps)"
      by (metis list.simps(3) min_list_param_in)
    then have "maximum_fst_prefix t (x # xs) ys \<in> list.set (map (\<lambda> y . (x,y) # maximum_fst_prefix (the (m (x,y))) xs ys) (filter (\<lambda> y . (m (x,y) \<noteq> None)) ys))"
      unfolding Cons .
    then obtain y where "y \<in> list.set (filter (\<lambda> y . (m (x,y) \<noteq> None)) ys)"
                    and "maximum_fst_prefix t (x # xs) ys = (x,y) # maximum_fst_prefix (the (m (x,y))) xs ys"
      by auto
    then have "m (x,y) \<noteq> None"
      by auto
    then obtain t' where "m (x,y) = Some t'"
      by auto
    then have "maximum_fst_prefix t (x # xs) ys = (x,y) # maximum_fst_prefix t' xs ys"
      using \<open>maximum_fst_prefix t (x # xs) ys = (x,y) # maximum_fst_prefix (the (m (x,y))) xs ys\<close>
      by auto
    
    have "isin t' (maximum_fst_prefix t' xs ys)"
      using Cons.IH by blast
    then show ?thesis
      using \<open>m (x,y) = Some t'\<close>
      unfolding \<open>maximum_fst_prefix t (x # xs) ys = (x,y) # maximum_fst_prefix t' xs ys\<close>
      unfolding *
      by auto
  qed
qed

lemma maximum_fst_prefix_MPT[code]:
  "maximum_fst_prefix (MPT m) xs ys = (case xs of
    [] \<Rightarrow> [] |
    (x#xs) \<Rightarrow> (case (map (\<lambda> y . (x,y) # maximum_fst_prefix (the (Mapping.lookup m (x,y))) xs ys) (filter (\<lambda> y . (Mapping.lookup m (x,y) \<noteq> None)) ys)) of
      [] \<Rightarrow> [] |
      (p'#ps) \<Rightarrow> min_list_param (\<lambda> a b . length a > length b) (p'#ps)))"
  apply (cases xs; auto)
  by (simp add: MPT_def lookup.rep_eq)  
*)


end 