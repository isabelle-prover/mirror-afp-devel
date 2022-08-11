section \<open>Test Suites for Language Equivalence\<close>

text \<open>This file introduces a type for test suites represented as a prefix tree in which
      each IO-pair is additionally labeled by a boolean value representing whether 
      the IO-pair should be exhibited by the SUT in order to pass the test suite.\<close>


theory Test_Suite_Representations
imports "../Minimisation" "../Prefix_Tree"
begin


type_synonym ('b,'c) test_suite = "(('b \<times> 'c) \<times> bool) prefix_tree"

(* also reduces the test suite by dropping suffixes after the first element not in LS M q *)
function (domintros) test_suite_from_io_tree :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) prefix_tree \<Rightarrow> ('b,'c) test_suite" where
  "test_suite_from_io_tree M q (PT m) = PT (\<lambda> ((x,y),b) . case m (x,y) of
    None \<Rightarrow> None |
    Some t \<Rightarrow> (case h_obs M q x y of
      None \<Rightarrow> (if b then None else Some empty) |
      Some q' \<Rightarrow> (if b then Some (test_suite_from_io_tree M q' t) else None)))"
  by pat_completeness auto
termination 
proof -
  {
    fix M :: "('a,'b,'c) fsm"
    fix q t
  
    have "test_suite_from_io_tree_dom (M,q,t)" 
    proof (induction t arbitrary: M q)
      case (PT m)
      then have "\<And>x y t q'. m (x, y) = Some t \<Longrightarrow> test_suite_from_io_tree_dom (M, q', t)"
        by blast 
      then show ?case 
        using test_suite_from_io_tree.domintros[of m q M] by auto
    qed
  }
  then show ?thesis by auto
qed

subsection \<open>Transforming an IO-prefix-tree to a test suite\<close>

lemma test_suite_from_io_tree_set :
  assumes "observable M"
      and "q \<in> states M"
    shows "(set (test_suite_from_io_tree M q t)) = ((\<lambda> xs . map (\<lambda> x . (x,True)) xs) ` (set t \<inter> LS M q)) 
                                                    \<union> ((\<lambda> xs . (map (\<lambda> x . (x,True)) (butlast xs))@[(last xs,False)]) ` {xs@[x] | xs x . xs \<in> set t \<inter> LS M q \<and> xs@[x] \<in> set t - LS M q})"
    (is "?S1 q t = ?S2 q t")
proof 
  show "?S1 q t \<subseteq> ?S2 q t"
  proof 
    fix xs assume "xs \<in> ?S1 q t"
    then have "isin (test_suite_from_io_tree M q t) xs"
      by auto
    then show "xs \<in> ?S2 q t"
      using \<open>q \<in> states M\<close>
    proof (induction xs arbitrary: q t)
      case Nil

      have "[] \<in> set t"
        using Nil.prems(1) set_Nil by auto 
      moreover have "[] \<in> LS M q"
        using Nil.prems(2) by auto
      ultimately show ?case
        by auto 
    next
      case (Cons x' xs)
      moreover obtain x y b where "x' = ((x,y),b)"
        by (metis surj_pair)
      moreover obtain m where "t = PT m"
        by (meson prefix_tree.exhaust)
      ultimately have "isin (test_suite_from_io_tree M q (PT m)) (((x,y),b) # xs)"
        by auto

      let ?fi = "\<lambda> t . (case h_obs M q x y of
                    None \<Rightarrow> (if b then None else Some empty) |
                    Some q' \<Rightarrow> (if b then Some (test_suite_from_io_tree M q' t) else None))"
      let ?fo = "case m (x,y) of
                  None \<Rightarrow> None |
                  Some t \<Rightarrow> ?fi t"
      
      obtain tst where "?fo = Some tst"
        using \<open>isin (test_suite_from_io_tree M q (PT m)) (((x,y),b) # xs)\<close>
        unfolding test_suite_from_io_tree.simps isin.simps by force
      then have "isin tst xs"
        using \<open>isin (test_suite_from_io_tree M q (PT m)) (((x,y),b) # xs)\<close>
        by auto

      obtain t' where "m (x,y) = Some t'"
                       and "?fi t' = Some tst"
        using \<open>?fo = Some tst\<close>
        by (metis (no_types, lifting) option.case_eq_if option.collapse option.distinct(1))
      then consider "h_obs M q x y = None \<and> \<not>b \<and> tst = empty" |
                    "\<exists> q' . h_obs M q x y = Some q' \<and> b \<and> tst = test_suite_from_io_tree M q' t'"
        unfolding option.case_eq_if
        using option.collapse[of "h_obs M q x y"]
        using option.distinct(1) option.inject
        by metis
      then show ?case proof cases
        case 1
        then have "h_obs M q x y = None" and "b = False" and "tst = empty"
          by auto

        have "isin empty xs"
          using \<open>isin tst xs\<close> \<open>tst = empty\<close> by auto
        then have "xs = []"
          using set_empty by auto
        then have *: "x'#xs = [((x,y),b)]"
          using \<open>x' = ((x,y),b)\<close> by auto

        have "[] \<in> LS M q"
          using \<open>q \<in> states M\<close> by auto
        moreover have "[] \<in> set t"
          using set_Nil by auto
        moreover have "[(x,y)] \<notin> LS M q"
          using \<open>h_obs M q x y = None\<close> unfolding h_obs_None[OF \<open>observable M\<close>]
          by auto
        moreover have "isin t [(x,y)]"
          unfolding \<open>t = PT m\<close> isin.simps using \<open>m (x,y) = Some t'\<close>
          using isin.elims(3) by auto
        ultimately have "[(x,y)] \<in> {xs @ [x] |xs x. xs \<in> Prefix_Tree.set t \<inter> LS M q \<and> xs @ [x] \<in> Prefix_Tree.set t - LS M q}"
          by auto
        moreover have "(x'#xs) = ((\<lambda> xs . (map (\<lambda> x . (x,True)) (butlast xs))@[(last xs,False)]) [(x,y)])"
          unfolding * \<open>b = False\<close> 
          by auto
        ultimately show ?thesis 
          by blast
      next
        case 2
        then obtain q' where "h_obs M q x y = Some q'" 
                             "b = True" 
                             "tst = test_suite_from_io_tree M q' t'"
          by blast

        have p1: "isin (test_suite_from_io_tree M q' t') xs"
          using \<open>isin tst xs\<close> \<open>tst = test_suite_from_io_tree M q' t'\<close> by auto
        have p2: "q' \<in> states M"
          using \<open>h_obs M q x y = Some q'\<close> fsm_transition_target unfolding h_obs_Some[OF \<open>observable M\<close>]
          by fastforce 

        have "xs \<in> ?S2 q' t'" 
          using Cons.IH[OF p1 p2] .
        then consider (a) "xs \<in> map (\<lambda>x. (x, True)) ` (Prefix_Tree.set t' \<inter> LS M q')" |
                      (b) "xs \<in> (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) ` {xs @ [x] |xs x. xs \<in> Prefix_Tree.set t' \<inter> LS M q' \<and> xs @ [x] \<in> Prefix_Tree.set t' - LS M q'}"
          by blast
        then show ?thesis proof cases
          case a
          then obtain xs' where "xs' \<in> set t'" and "xs' \<in> LS M q'"
                            and "xs = map (\<lambda>x. (x, True)) xs'"
            by auto

          have "(x,y)#xs' \<in> set t"
            using \<open>xs' \<in> set t'\<close> \<open>m (x,y) = Some t'\<close> unfolding \<open>t = PT m\<close> by auto
          moreover have "(x,y)#xs' \<in> LS M q"
            using \<open>h_obs M q x y = Some q'\<close> \<open>xs' \<in> LS M q'\<close> unfolding h_obs_Some[OF \<open>observable M\<close>] 
            using LS_prepend_transition[of "(q,x,y,q')" M xs'] by auto
          moreover have "x'#xs = map (\<lambda>x. (x, True)) ((x,y)#xs')"
            unfolding \<open>x' = ((x,y),b)\<close> \<open>b = True\<close> \<open>xs = map (\<lambda>x. (x, True)) xs'\<close> by auto
          ultimately show ?thesis
            by (metis (no_types, lifting) Int_iff UnI1 image_eqI)
        next
          case b
          then obtain xs' where "xs' \<in>  {xs @ [x] |xs x. xs \<in> Prefix_Tree.set t' \<inter> LS M q' \<and> xs @ [x] \<in> Prefix_Tree.set t' - LS M q'}"
                            and "xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) xs'"
            by blast
          moreover obtain bl l where "xs' = bl @ [l]"
            using calculation by blast 
          ultimately have "bl \<in> set t'" and "bl \<in> LS M q'" and "bl @ [l] \<in> set t'" and "bl@[l] \<notin> LS M q'"
                      and "xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (bl@[l])"
            by auto
            

          have "(x,y)#bl \<in> set t"
            using \<open>bl \<in> set t'\<close> \<open>m (x,y) = Some t'\<close> unfolding \<open>t = PT m\<close> by auto 
          moreover have "(x,y)#bl \<in> LS M q"
            using \<open>h_obs M q x y = Some q'\<close> \<open>bl \<in> LS M q'\<close> unfolding h_obs_Some[OF \<open>observable M\<close>] 
            using LS_prepend_transition[of "(q,x,y,q')" M bl] by auto
          moreover have "(x,y)#(bl @ [l]) \<in> set t"
            using \<open>bl @ [l] \<in> set t'\<close> \<open>m (x,y) = Some t'\<close> unfolding \<open>t = PT m\<close> by auto 
          moreover have "(x,y)#(bl@[l]) \<notin> LS M q"
            using \<open>h_obs M q x y = Some q'\<close> \<open>bl@[l] \<notin> LS M q'\<close> unfolding h_obs_Some[OF \<open>observable M\<close>]  
            using observable_language_transition_target[OF \<open>observable M\<close>, of "(q,x,y,q')" "bl@[l]"]
            unfolding fst_conv snd_conv
            by blast
          ultimately have "(x,y)#bl@[l] \<in> {xs @ [x] |xs x. xs \<in> Prefix_Tree.set t \<inter> LS M q \<and> xs @ [x] \<in> Prefix_Tree.set t - LS M q}"
            by fastforce
          moreover have "x'#xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) ((x,y)#(bl@[l]))"
            unfolding \<open>x' = ((x,y),b)\<close> \<open>b = True\<close> \<open>xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (bl@[l])\<close> by auto
          ultimately show ?thesis
            by fast
        qed
      qed
    qed
  qed

  show "?S2 q t \<subseteq> ?S1 q t"
  proof
    fix xs assume "xs \<in> ?S2 q t"
    then consider "xs \<in> map (\<lambda>x. (x, True)) ` (set t \<inter> LS M q)" |
                  "xs \<in> (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) ` {xs @ [x] |xs x. xs \<in> Prefix_Tree.set t \<inter> LS M q \<and> xs @ [x] \<in> Prefix_Tree.set t - LS M q}"
      by blast
    then show "xs \<in> ?S1 q t" proof cases
      case 1
      then show ?thesis 
        using \<open>q \<in> states M\<close> 
      proof (induction xs arbitrary: q t)
        case Nil
        then show ?case using set_Nil by auto
      next
        case (Cons x' xs) 
        obtain xs'' where "xs'' \<in> set t" and "xs'' \<in> LS M q"
                         and "x'#xs = map (\<lambda>x. (x, True)) xs''"
          using Cons.prems(1)
          by (meson IntD1 IntD2 imageE) 
        
        then obtain x y xs' where "(x,y)#xs' \<in> set t" and "(x,y)#xs' \<in> LS M q"
                              and "x'#xs = map (\<lambda>x. (x, True)) ((x,y)#xs')"
          by force
        then have "x' = ((x,y),True)" and "xs = map (\<lambda>x. (x, True)) xs'"
          by auto 

        obtain m where "t = PT m"
          by (meson prefix_tree.exhaust)
          
        have "isin (PT m) ((x,y)#xs')"
          using \<open>(x,y)#xs' \<in> set t\<close> unfolding \<open>t = PT m\<close> by auto
        then obtain t' where "m (x,y) = Some t'"
                         and "isin t' xs'"
          by (metis case_optionE isin.simps(2))

        have "[(x,y)] \<in> LS M q"
          using \<open>(x,y)#xs' \<in> LS M q\<close> language_prefix[of "[(x,y)]" xs' M q]
          by simp 
        then obtain q' where "h_obs M q x y = Some q'"
          using h_obs_None[OF \<open>observable M\<close>, of q x y] unfolding LS_single_transition by auto
        
        have "isin (test_suite_from_io_tree M q (PT m)) (((x,y),True)#xs) 
               = isin (test_suite_from_io_tree M q' t') (xs)"
          using \<open>m (x,y) = Some t'\<close> \<open>h_obs M q x y = Some q'\<close> by auto
        then have *: "x' # xs \<in> set (test_suite_from_io_tree M q t)
                      = (xs \<in> set (test_suite_from_io_tree M q' t'))"
          unfolding \<open>t = PT m\<close> \<open>x' = ((x,y),True)\<close> by auto

        have "xs' \<in> LS M q'"
          using \<open>h_obs M q x y = Some q'\<close> unfolding h_obs_Some[OF \<open>observable M\<close>, of q x y]
          using \<open>(x,y)#xs' \<in> LS M q\<close> observable_language_transition_target[OF \<open>observable M\<close>] by force
        moreover have "xs' \<in> set t'"
          using \<open>isin t' xs'\<close> by auto
        ultimately have p1: "xs \<in> map (\<lambda>x. (x, True)) ` (set t' \<inter> LS M q')"
          unfolding \<open>xs = map (\<lambda>x. (x, True)) xs'\<close> by auto

        have p2: "q' \<in> states M"
          using \<open>h_obs M q x y = Some q'\<close> fsm_transition_target unfolding h_obs_Some[OF \<open>observable M\<close>]
          by fastforce 

        show ?case 
          using Cons.IH[OF p1 p2] unfolding * .
      qed
    next
      case 2
      then show ?thesis 
        using \<open>q \<in> states M\<close> 
      proof (induction xs arbitrary: q t)
        case Nil
        then show ?case using set_Nil by auto
      next
        case (Cons x' xs) 
        then obtain xsT where "x'#xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) xsT"
                           and "xsT \<in> {xs @ [x] |xs x. xs \<in> Prefix_Tree.set t \<inter> LS M q \<and> xs @ [x] \<in> Prefix_Tree.set t - LS M q}"
          by blast
        moreover obtain bl l where "xsT = bl @ [l]"
          using calculation by auto
        ultimately have "bl \<in> set t" and "bl \<in> LS M q" and "bl @ [l] \<in> set t" and "bl@[l] \<notin> LS M q"
                    and "x'#xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (bl@[l])"
          by auto

        obtain m where "t = PT m"
          by (meson prefix_tree.exhaust)
        
        show ?case proof (cases xs)
          case Nil
          then have "x' = (l,False)" and "bl = []"
            using \<open>x'#xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (bl@[l])\<close> 
            by auto
          moreover obtain x y where "l = (x,y)"
            using prod.exhaust by metis
          ultimately have "[(x,y)] \<in> set t" and "[(x,y)] \<notin> LS M q"  
            using \<open>bl @ [l] \<in> set t\<close> \<open>bl@[l] \<notin> LS M q\<close> by auto

          obtain t' where "m (x,y) = Some t'"
            using \<open>[(x,y)] \<in> set t\<close> unfolding \<open>t = PT m\<close> by force
          moreover have "h_obs M q x y = None"
            using \<open>[(x,y)] \<notin> LS M q\<close> unfolding h_obs_None[OF \<open>observable M\<close>] LS_single_transition by auto
          ultimately have "isin (test_suite_from_io_tree M q (PT m)) (x'#xs) = isin empty []"
            unfolding Nil \<open>x' = (l,False)\<close> test_suite_from_io_tree.simps isin.simps \<open>l = (x,y)\<close>
            by (simp add: Prefix_Tree.empty_def) 
          then show ?thesis
            using set_Nil unfolding \<open>t = PT m\<close> by auto
        next
          case (Cons x'' xs'')
          then obtain x y bl' where "bl = (x,y)#bl'"
            using \<open>x'#xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (bl@[l])\<close>
            by (metis append.left_neutral butlast_snoc list.inject list.simps(8) neq_Nil_conv surj_pair) 
          then have "x' = ((x,y),True)"
                and "xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (bl'@[l])"
            using \<open>x'#xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (bl@[l])\<close>
            by auto

          have "isin (PT m) ((x,y)#(bl'@[l]))" 
            using \<open>bl@[l] \<in> set t\<close> unfolding \<open>bl = (x,y)#bl'\<close> \<open>t = PT m\<close> by auto
          then obtain t' where "m (x,y) = Some t'"
                           and "isin t' (bl'@[l])"
            unfolding isin.simps
            using case_optionE by blast 

          have "[(x,y)] \<in> LS M q"
            using \<open>bl \<in> LS M q\<close> language_prefix[of "[(x,y)]" bl' M q] unfolding \<open>bl = (x,y)#bl'\<close> by auto
          then obtain q' where "h_obs M q x y = Some q'"
            using h_obs_None[OF \<open>observable M\<close>] unfolding LS_single_transition by force
          then have p2: "q' \<in> states M"
            using fsm_transition_target unfolding h_obs_Some[OF \<open>observable M\<close>]
            by fastforce 

          have "bl' \<in> set t'"
            using \<open>isin t' (bl'@[l])\<close> isin_prefix by auto
          moreover have "bl' \<in> LS M q'"
            using \<open>h_obs M q x y = Some q'\<close> unfolding h_obs_Some[OF \<open>observable M\<close>]
            using \<open>bl \<in> LS M q\<close> observable_language_transition_target[OF \<open>observable M\<close>] 
            unfolding \<open>bl = (x,y)#bl'\<close> by force
          moreover have "bl'@[l] \<in> set t'"
            using \<open>isin t' (bl'@[l])\<close> by auto
          moreover have "bl'@[l] \<notin> LS M q'"
          proof -
            have "(x, y) # (bl' @ [l]) \<notin> LS M q"
              using \<open>bl@[l] \<notin> LS M q\<close> unfolding \<open>bl = (x,y)#bl'\<close> by auto
            then show ?thesis
              using \<open>h_obs M q x y = Some q'\<close> unfolding h_obs_Some[OF \<open>observable M\<close>]
              using LS_prepend_transition[of "(q,x,y,q')" M "bl'@[l]"]
              unfolding \<open>bl = (x,y)#bl'\<close> fst_conv snd_conv by blast
          qed
          ultimately have "(bl'@[l]) \<in>  {xs @ [x] |xs x. xs \<in> Prefix_Tree.set t' \<inter> LS M q' \<and> xs @ [x] \<in> Prefix_Tree.set t' - LS M q'}"
            by blast
          moreover have "xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (bl'@[l])"
            using \<open>x'#xs = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (bl@[l])\<close>
            unfolding Nil \<open>bl = (x,y)#bl'\<close> by auto
          ultimately have "xs \<in> Prefix_Tree.set (test_suite_from_io_tree M q' t')"
            using Cons.IH[of t', OF _ p2] by blast
          then have "isin (test_suite_from_io_tree M q t) (x'#xs)"
            unfolding \<open>x' = ((x,y),True)\<close> \<open>t = PT m\<close> 
            unfolding test_suite_from_io_tree.simps isin.simps
            using \<open>m (x,y) = Some t'\<close> \<open>h_obs M q x y = Some q'\<close> by auto
          then show ?thesis
            by auto
        qed
      qed
    qed
  qed
qed

(* function written using xyb instead of immediately unfolding to e.g. ((x,y),b) as the
   resulting domintros fact was too weak
    see also: https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2010-September/msg00001.html *)
function (domintros) passes_test_suite :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b,'c) test_suite \<Rightarrow> bool" where
  "passes_test_suite M q (PT m) = (\<forall> xyb \<in> dom m . case h_obs M q (fst (fst xyb)) (snd (fst xyb)) of
      None \<Rightarrow> \<not>(snd xyb) |
      Some q' \<Rightarrow> snd xyb \<and> passes_test_suite M q' (case m xyb of Some t \<Rightarrow> t))"
  by pat_completeness auto
termination 
proof -
  {
    fix M :: "('a,'b,'c) fsm"
    fix q t
    have "passes_test_suite_dom (M,q,t)"
    proof (induction t arbitrary: M q)
      case (PT m)
      then have "\<And> ab ba bb y x2 . m ((ab, ba), bb) = Some y \<Longrightarrow> passes_test_suite_dom (M, x2, y)"
        by blast
      then show ?case 
        using passes_test_suite.domintros[of q M m] by auto 
    qed
  }
  then show ?thesis by auto
qed

lemma passes_test_suite_iff :
  assumes "observable M"
      and "q \<in> states M"
shows "passes_test_suite M q t = (\<forall> iob \<in> set t . (map fst iob) \<in> LS M q \<longleftrightarrow> list_all snd iob)"
proof 
  show "passes_test_suite M q t \<Longrightarrow> \<forall>iob\<in>Prefix_Tree.set t. (map fst iob \<in> LS M q) = list_all snd iob"
  proof 
    fix iob assume "passes_test_suite M q t" 
               and "iob \<in> Prefix_Tree.set t" 
    then show "(map fst iob \<in> LS M q) = list_all snd iob"
      using \<open>q \<in> states M\<close>
    proof (induction iob arbitrary: q t)
      case Nil
      then show ?case by auto
    next
      case (Cons a iob)

      obtain m where "t = PT m"
        by (meson prefix_tree.exhaust) 
      then have "isin (PT m) (a#iob)" 
        using \<open>a # iob \<in> Prefix_Tree.set t\<close> by simp
      moreover obtain x y b where "a = ((x,y),b)"
        by (metis old.prod.exhaust)
      ultimately obtain t' where "m ((x,y),b) = Some t'"
                             and "isin t' iob"
        unfolding isin.simps
        using case_optionE by blast 
      then have "((x,y),b) \<in> dom m"
        by auto
      then have *: "(case h_obs M q x y of
                      None \<Rightarrow> \<not>b |
                      Some q' \<Rightarrow> b \<and> passes_test_suite M q' (case m ((x,y),b) of Some t \<Rightarrow> t))"
         using \<open>passes_test_suite M q t\<close> \<open>((x,y),b) \<in> dom m\<close> unfolding \<open>t = PT m\<close> passes_test_suite.simps
         by (metis fst_conv snd_conv)

      show ?case proof (cases b)
        case False
        then have "h_obs M q x y = None"
          using *
          using case_optionE by blast 
        then have "[(x,y)] \<notin> LS M q"
          unfolding h_obs_None[OF \<open>observable M\<close>] by auto
        then have "(map fst (a#iob)) \<notin> LS M q"
          unfolding \<open>a = ((x,y),b)\<close> using language_prefix[of "[(x,y)]" "map fst iob" M q]
          by fastforce 
        then show ?thesis
          unfolding \<open>a = ((x,y),b)\<close> using False by auto
      next
        case True
        then obtain q' where "h_obs M q x y = Some q'"
          using * case_optionE by blast 
        then have **: "((map fst (a#iob)) \<in> LS M q) = ((map fst iob) \<in> LS M q')"
          using observable_language_transition_target[OF \<open>observable M\<close>, of "(q,x,y,q')" "map fst iob"]
          unfolding \<open>a = ((x,y),b)\<close> h_obs_Some[OF \<open>observable M\<close>] fst_conv snd_conv
          by (metis (no_types, lifting) LS_prepend_transition fst_conv list.simps(9) mem_Collect_eq singletonI snd_conv)
        have ***: "list_all snd (a#iob) = list_all snd iob"
          unfolding \<open>a = ((x,y),b)\<close> using True by auto

        have "passes_test_suite M q' t'"
          using \<open>passes_test_suite M q t\<close> \<open>((x,y),b) \<in> dom m\<close> \<open>h_obs M q x y = Some q'\<close> True
          unfolding \<open>t = PT m\<close> passes_test_suite.simps
          using * \<open>m ((x, y), b) = Some t'\<close> by auto
        moreover have "iob \<in> set t'"
          using \<open>isin t' iob\<close> by auto
        moreover have "q' \<in> states M"
          using \<open>h_obs M q x y = Some q'\<close> fsm_transition_target
          unfolding h_obs_Some[OF \<open>observable M\<close>]
          by fastforce 
        ultimately show ?thesis
          using Cons.IH unfolding ** *** by blast
      qed
    qed
  qed

  show "\<forall>iob\<in>Prefix_Tree.set t. (map fst iob \<in> LS M q) = list_all snd iob \<Longrightarrow> passes_test_suite M q t"
  proof (induction t arbitrary: q)
    case (PT m)

    have "\<And> xyb . xyb \<in> dom m \<Longrightarrow> case h_obs M q (fst (fst xyb)) (snd (fst xyb)) of None \<Rightarrow> \<not> snd xyb | Some q' \<Rightarrow> snd xyb \<and> passes_test_suite M q' (case m xyb of Some t \<Rightarrow> t)"
    proof -
      fix xyb assume "xyb \<in> dom m"
      moreover obtain x y b where "xyb = ((x,y),b)"
        by (metis old.prod.exhaust)
      ultimately obtain t' where "m ((x,y),b) = Some t'"
        by auto
      then have "isin (PT m) [((x,y),b)]"
        by auto
      then have "[((x,y),b)] \<in> set (PT m)"
        by auto
      then have "(map fst [((x,y),b)] \<in> LS M q) = list_all snd [((x,y),b)]"
        using \<open>\<forall>iob\<in>Prefix_Tree.set (PT m). (map fst iob \<in> LS M q) = list_all snd iob\<close> by blast
      then have "([(x,y)] \<in> LS M q) = b"
        by auto
        


      show "case h_obs M q (fst (fst xyb)) (snd (fst xyb)) of None \<Rightarrow> \<not> snd xyb | Some q' \<Rightarrow> snd xyb \<and> passes_test_suite M q' (case m xyb of Some t \<Rightarrow> t)"
        
      proof (cases "h_obs M q x y")
        case None
        then have "[(x,y)] \<notin> LS M q"
          unfolding h_obs_None[OF \<open>observable M\<close>] by auto
        then have "b = False"
          using \<open>([(x,y)] \<in> LS M q) = b\<close> by blast 
        then show ?thesis 
          using None unfolding \<open>xyb = ((x,y),b)\<close> by auto
      next
        case (Some q')
        then have "[(x,y)] \<in> LS M q"
          unfolding h_obs_Some[OF \<open>observable M\<close>] LS_single_transition by force
        then have "b"
          using \<open>([(x,y)] \<in> LS M q) = b\<close> by blast 
        moreover have "passes_test_suite M q' t'"
        proof -
          have "Some t' \<in> range m"
            using \<open>m ((x,y),b) = Some t'\<close>
            by (metis range_eqI) 
          moreover have "t' \<in> set_option (Some t')"
            by auto
          moreover have "\<forall>iob\<in>Prefix_Tree.set t'. (map fst iob \<in> LS M q') = list_all snd iob"
          proof 
            fix iob assume "iob \<in> Prefix_Tree.set t'"
            then have "isin t' iob"
              by auto
            then have "isin (PT m) (((x,y),b)#iob)"
              using \<open>m ((x,y),b) = Some t'\<close> 
              by auto
            then have "((x,y),b)#iob \<in> set (PT m)"
              by auto
            then have "(map fst (((x,y),b)#iob) \<in> LS M q) = list_all snd (((x,y),b)#iob)"
              using PT.prems by blast
            moreover have "(map fst (((x,y),b)#iob) \<in> LS M q) = (map fst iob \<in> LS M q')"
              using observable_language_transition_target[OF \<open>observable M\<close>, of "(q,x,y,q')" "map fst iob"]
              by (metis (no_types, lifting) LS_prepend_transition Some h_obs_Some[OF \<open>observable M\<close>] fst_conv list.simps(9) mem_Collect_eq singletonI snd_conv) 
            moreover have "list_all snd (((x,y),b)#iob) = list_all snd iob"
              using \<open>b\<close> by auto
            ultimately show "(map fst iob \<in> LS M q') = list_all snd iob"
              by simp
          qed
          ultimately show ?thesis
            using PT.IH by blast
        qed
        ultimately show ?thesis 
          using \<open>m ((x,y),b) = Some t'\<close> \<open>xyb = ((x,y),b)\<close> Some
          by simp
      qed
    qed
    then show ?case 
      by auto    
  qed
qed



(* Main result of the test_suite transformation: 
    an IO prefix_tree representing a set of IO sequences can be transformed into a test suite
    such that passing the test suite equals passing the original set of sequences *)
lemma passes_test_suite_from_io_tree : 
  assumes "observable M" 
  and     "observable I"
  and     "qM \<in> states M"
  and     "qI \<in> states I"
shows "passes_test_suite I qI (test_suite_from_io_tree M qM t) = ((set t \<inter> LS M qM) = (set t \<inter> LS I qI))"
proof -

  define ts where "ts = test_suite_from_io_tree M qM t"
  then have "passes_test_suite I qI (test_suite_from_io_tree M qM t) = (\<forall>iob\<in>set ts. (map fst iob \<in> LS I qI) = list_all snd iob)"
    using passes_test_suite_iff[OF assms(2,4), of ts] 
    by auto
  also have "\<dots> = ((set t \<inter> LS M qM) = (set t \<inter> LS I qI))"
  proof 
    have ts_set: "set ts = map (\<lambda>x. (x, True)) ` (set t \<inter> LS M qM) \<union>
                           (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) `
                             {xs @ [x] |xs x. xs \<in> set t \<inter> LS M qM \<and> xs @ [x] \<in> set t - LS M qM}"
      using test_suite_from_io_tree_set[OF assms(1,3), of t] \<open>ts = test_suite_from_io_tree M qM t\<close>
      by auto

    show "\<forall>iob\<in>Prefix_Tree.set ts. (map fst iob \<in> LS I qI) = list_all snd iob \<Longrightarrow> set t \<inter> LS M qM = set t \<inter> LS I qI"
    proof -
      assume "\<forall>iob\<in>Prefix_Tree.set ts. (map fst iob \<in> LS I qI) = list_all snd iob"
      then have ts_assm: "\<And> iob . iob \<in> set ts \<Longrightarrow> (map fst iob \<in> LS I qI) = list_all snd iob"
        by blast

      show "set t \<inter> LS M qM = set t \<inter> LS I qI"
      proof
        show "set t \<inter> LS M qM \<subseteq> set t \<inter> LS I qI"
        proof 
          fix io assume "io \<in> set t \<inter> LS M qM"
          then have "map (\<lambda>x. (x, True)) io \<in> set ts"
            unfolding ts_set by auto
          moreover have "list_all snd (map (\<lambda>x. (x, True)) io)"
            by (induction io; auto)
          moreover have "map fst (map (\<lambda>x. (x, True)) io) = io"
            by (induction io; auto)
          ultimately have "io \<in> LS I qI"
            using ts_assm by force
          then show "io \<in> set t \<inter> LS I qI"
            using \<open>io \<in> set t \<inter> LS M qM\<close> by blast
        qed

        show "set t \<inter> LS I qI \<subseteq> set t \<inter> LS M qM"
        proof 
          fix io assume "io \<in> set t \<inter> LS I qI"
          show "io \<in> set t \<inter> LS M qM"
          proof (rule ccontr)
            assume "io \<notin> set t \<inter> LS M qM"
            then have "io \<in> LS I qI - LS M qM"
              using \<open>io \<in> set t \<inter> LS I qI\<close> by blast
            then obtain io' xy io'' where "io = io' @ [xy] @ io''" 
                                      and "io' \<in> LS I qI \<inter> LS M qM" 
                                      and "io' @ [xy] \<in> LS I qI - LS M qM" 
              using minimal_failure_prefix_ob[OF assms]
              by blast

            have "io' \<in> set t \<inter> LS M qM"
              using \<open>io' \<in> LS I qI \<inter> LS M qM\<close> \<open>io \<in> set t \<inter> LS I qI\<close> isin_prefix[of t io' "[xy] @ io''"] language_prefix[of io' "[xy] @ io''"]
              unfolding \<open>io = io' @ [xy] @ io''\<close>
              by auto
            moreover have "io' @ [xy] \<in> set t - LS M qM"
              using \<open>io' @ [xy] \<in> LS I qI - LS M qM\<close> \<open>io \<in> set t \<inter> LS I qI\<close> isin_prefix[of t "io'@[xy]" io''] 
              unfolding \<open>io = io' @ [xy] @ io''\<close> 
              by auto
            ultimately have "io'@[xy] \<in> {xs @ [x] |xs x. xs \<in> set t \<inter> LS M qM \<and> xs @ [x] \<in> set t - LS M qM}"
              by blast
            then have "(\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (io'@[xy]) \<in> set ts"
              unfolding ts_set by blast
            then have "(map (\<lambda>x. (x, True)) io' @ [(xy, False)]) \<in> set ts"
              by auto
            moreover have "(map fst (map (\<lambda>x. (x, True)) io' @ [(xy, False)]) \<in> LS I qI) \<noteq> list_all snd ((map (\<lambda>x. (x, True)) io' @ [(xy, False)]))"
            proof -
              have "(map fst (map (\<lambda>x. (x, True)) io' @ [(xy, False)])) = io'@[xy]"
                by (induction io'; auto)
              then show ?thesis
                using \<open>io' @ [xy] \<in> set t - LS M qM\<close> \<open>io \<in> set t \<inter> LS I qI\<close> language_prefix[of "io'@[xy]" io'' I qI]
                unfolding \<open>io = io' @ [xy] @ io''\<close>
                by auto
            qed
            ultimately show "False"
              using ts_assm by blast
          qed
        qed
      qed
    qed

    show "set t \<inter> LS M qM = Prefix_Tree.set t \<inter> LS I qI \<Longrightarrow> \<forall>iob\<in>set ts. (map fst iob \<in> LS I qI) = list_all snd iob"
    proof 
      fix iob assume "set t \<inter> LS M qM = set t \<inter> LS I qI"
                 and "iob \<in> set ts"

      then consider (a) "iob \<in> map (\<lambda>x. (x, True)) ` (set t \<inter> LS M qM)" |
                    (b) "iob \<in> (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) `
                             {xs @ [x] |xs x. xs \<in> set t \<inter> LS M qM \<and> xs @ [x] \<in> set t - LS M qM}"
        using ts_set by blast
      
      then show "(map fst iob \<in> LS I qI) = list_all snd iob" 
      proof cases
        case a 
        then obtain io where "iob = map (\<lambda>x. (x, True)) io"
                         and "io \<in> set t \<inter> LS M qM"
          by blast

        then have "map fst iob = io"
          by auto
        then have "map fst iob \<in> LS I qI"
          using \<open>io \<in> set t \<inter> LS M qM\<close> \<open>set t \<inter> LS M qM = set t \<inter> LS I qI\<close>
          by auto
        moreover have "list_all snd iob"
          unfolding \<open>iob = map (\<lambda>x. (x, True)) io\<close> by (induction io; auto)
        ultimately show ?thesis 
          by simp
      next
        case b

        then obtain ioxy where "iob = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (ioxy)"
                            and "ioxy \<in> {xs @ [x] |xs x. xs \<in> set t \<inter> LS M qM \<and> xs @ [x] \<in> set t - LS M qM}"
          by blast
        then obtain io xy where "ioxy = io@[xy]"
                            and "io@[xy] \<in> set t - LS M qM"
          by blast
        then have *: "iob = map (\<lambda>x. (x, True)) io @ [(xy, False)]"
          using \<open>iob = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (ioxy)\<close> by auto
        then have **: "map fst iob = io@[xy]"
          by (induction io arbitrary: iob; auto)

        have "\<not>map fst iob \<in> LS I qI"
          unfolding ** using \<open>io@[xy] \<in> set t - LS M qM\<close> \<open>set t \<inter> LS M qM = set t \<inter> LS I qI\<close>
          by blast
        moreover have "\<not> list_all snd iob"
          unfolding * by auto
        ultimately show ?thesis 
          by simp
      qed
    qed
  qed
  finally show ?thesis .
qed



subsection \<open>Code Refinement\<close>


context includes lifting_syntax
begin

lemma map_entries_parametric:
  "((A ===> B) ===> (A ===> C ===> rel_option D) ===> (B ===> rel_option C) ===> A ===> rel_option D)
     (\<lambda>f g m x. case (m \<circ> f) x of None \<Rightarrow> None | Some y \<Rightarrow> g x y) (\<lambda>f g m x. case (m \<circ> f) x of None \<Rightarrow> None | Some y \<Rightarrow> g x y)"
  by transfer_prover

end

lift_definition map_entries :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b \<Rightarrow> 'd option) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('c, 'd) mapping"
  is "\<lambda>f g m x. case (m \<circ> f) x of None \<Rightarrow> None | Some y \<Rightarrow> g x y" parametric map_entries_parametric .
  

lemma test_suite_from_io_tree_MPT[code] :
  "test_suite_from_io_tree M q (MPT m) = 
    MPT (map_entries
          fst 
          (\<lambda> ((x,y),b) t . (case h_obs M q x y of
            None \<Rightarrow> (if b then None else Some empty) |
            Some q' \<Rightarrow> (if b then Some (test_suite_from_io_tree M q' t) else None)))
          m)"
  (is "?t M q (MPT m) = MPT (?f M q m)")
proof -
  have "\<And>xyb . Mapping.lookup (?f M q m) xyb= (\<lambda> ((x,y),b) . case Mapping.lookup m (x,y) of
    None \<Rightarrow> None |
    Some t \<Rightarrow> (case h_obs M q x y of
      None \<Rightarrow> (if b then None else Some empty) |
      Some q' \<Rightarrow> (if b then Some (test_suite_from_io_tree M q' t) else None))) xyb"
  (is "\<And> xyb. ?f1 xyb = ?f2 xyb")
  proof -
    fix xyb 
    
    show "?f1 xyb = ?f2 xyb"
    proof -
      obtain x y b where *:"xyb = ((x,y),b)"
        by (metis prod.collapse)
      
      show ?thesis proof (cases "Mapping.lookup m (fst xyb)")
        case None

        have "?f1 xyb = None"
          by (metis (no_types, lifting) None lookup.rep_eq map_entries.rep_eq option.simps(4))
        moreover have "?f2 xyb = None"
          using None by (simp add: "*") 
        ultimately show ?thesis
          by simp
      next
        case (Some t)

        then have **:"?f1 xyb = (\<lambda> ((x,y),b) t . (case h_obs M q x y of
            None \<Rightarrow> (if b then None else Some empty) |
            Some q' \<Rightarrow> (if b then Some (test_suite_from_io_tree M q' t) else None))) xyb t"
          by (simp add: lookup.rep_eq map_entries.rep_eq)
        
        show ?thesis
          unfolding ** using Some 
          by (simp add: "*") 
      qed
    qed
  qed
  then show ?thesis 
    unfolding MPT_def by auto
qed


lemma passes_test_suite_MPT[code]: 
  "passes_test_suite M q (MPT m) = (\<forall> xyb \<in> Mapping.keys m . case h_obs M q (fst (fst xyb)) (snd (fst xyb)) of
      None \<Rightarrow> \<not>(snd xyb) |
      Some q' \<Rightarrow> snd xyb \<and> passes_test_suite M q' (case Mapping.lookup m xyb of Some t \<Rightarrow> t))"
  by (simp add: MPT_def keys_dom_lookup)




subsection \<open>Pass relations on list of lists representations of test suites\<close>

fun passes_test_case :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> (('b \<times> 'c) \<times> bool) list \<Rightarrow> bool" where
  "passes_test_case M q [] = True" |
  "passes_test_case M q (((x,y),b)#io) = (if b 
    then case h_obs M q x y of
      Some q' \<Rightarrow> passes_test_case M q' io |
      None    \<Rightarrow> False
    else h_obs M q x y = None)"

lemma passes_test_case_iff :
  assumes "observable M"
  and     "q \<in> states M"
  shows "passes_test_case M q iob = ((map fst (takeWhile snd iob) \<in> LS M q)
                                      \<and> (\<not> (list_all snd iob) \<longrightarrow> map fst (take (Suc (length (takeWhile snd iob))) iob) \<notin> LS M q))"
using assms(2) proof (induction iob arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons a iob)
  obtain x y b where "a = ((x,y),b)"
    by (metis prod.collapse)

  show ?case proof (cases b)
    case True
    
    show ?thesis proof (cases "h_obs M q x y")
      case None
      then have "[(x,y)] \<notin> LS M q"
        unfolding h_obs_None[OF assms(1)] LS_single_transition by force
      then have "(map fst (takeWhile snd (a#iob)) \<notin> LS M q)"
        unfolding \<open>a = ((x,y),b)\<close> using True
        by (metis (mono_tags, opaque_lifting) append.simps(1) append.simps(2) fst_conv language_prefix list.simps(9) prod.sel(2) takeWhile.simps(2)) 
      moreover have "passes_test_case M q (a#iob) = False"
        using None unfolding \<open>a = ((x,y),b)\<close> using True by auto
      ultimately show ?thesis 
        by blast
    next
      case (Some q')
      then have "passes_test_case M q (a#iob) = passes_test_case M q' iob"
        unfolding \<open>a = ((x,y),b)\<close> using True by auto
      moreover have "(map fst (takeWhile snd (a#iob)) \<in> LS M q) = (map fst (takeWhile snd iob) \<in> LS M q')"
      proof -
        have *: "map fst (takeWhile snd (a#iob)) = (x,y)#(map fst (takeWhile snd iob))"
          using True unfolding \<open>a = ((x,y),b)\<close> by auto
        show ?thesis
          using Some
          unfolding * h_obs_Some[OF assms(1)]
          by (metis LS_prepend_transition assms(1) fst_conv mem_Collect_eq observable_language_transition_target singletonI snd_conv)  
      qed
      moreover have "(\<not> list_all snd (a#iob) \<longrightarrow> map fst (take (Suc (length (takeWhile snd (a#iob)))) (a#iob)) \<notin> LS M q)
                      = (\<not> list_all snd iob \<longrightarrow> map fst (take (Suc (length (takeWhile snd iob))) iob) \<notin> LS M q')"
      proof -
        have *: "map fst (take (Suc (length (takeWhile snd (a#iob)))) (a#iob)) = (x,y)#(map fst (take (Suc (length (takeWhile snd iob))) iob))"
          using True unfolding \<open>a = ((x,y),b)\<close> by auto
        have **: "list_all snd (a#iob) = list_all snd iob"
          using True unfolding \<open>a = ((x,y),b)\<close> by auto
        show ?thesis
          using Some
          unfolding * ** h_obs_Some[OF assms(1)]
          by (metis LS_prepend_transition assms(1) fst_conv mem_Collect_eq observable_language_transition_target prod.sel(2) singletonI) 
      qed
      ultimately show ?thesis
        unfolding Cons.IH[OF h_obs_state[OF Some]] by simp
    qed
  next
    case False
    show ?thesis proof (cases "h_obs M q x y")
      case None
      then have "[(x,y)] \<notin> LS M q"
        unfolding h_obs_None[OF assms(1)] LS_single_transition by force
      then have "(\<not> list_all snd (a#iob) \<longrightarrow> map fst (take (Suc (length (takeWhile snd (a#iob)))) (a#iob)) \<notin> LS M q)"
        unfolding \<open>a = ((x,y),b)\<close> using False by auto
      moreover have "(map fst (takeWhile snd (a#iob)) \<in> LS M q)"
        unfolding \<open>a = ((x,y),b)\<close> using False Cons.prems by auto
      moreover have "passes_test_case M q (a#iob) = True"
        unfolding \<open>a = ((x,y),b)\<close> using False None by auto
      ultimately show ?thesis 
        by simp
    next
      case (Some q')
      then have "[(x,y)] \<in> LS M q"
        unfolding h_obs_Some[OF assms(1)] LS_single_transition by force
      then have "\<not> (\<not> list_all snd (a#iob) \<longrightarrow> map fst (take (Suc (length (takeWhile snd (a#iob)))) (a#iob)) \<notin> LS M q)"
        unfolding \<open>a = ((x,y),b)\<close> using False by auto
      moreover have "passes_test_case M q (a#iob) = False"
        unfolding \<open>a = ((x,y),b)\<close> using False Some by auto
      ultimately show ?thesis 
        by simp
    qed
  qed
qed


lemma test_suite_from_io_tree_finite_tree :
  assumes "observable M" 
  and     "qM \<in> states M" 
  and     "finite_tree t"
shows "finite_tree (test_suite_from_io_tree M qM t)"
proof -
  have "finite (Prefix_Tree.set t \<inter> LS M qM)"
    using assms(3) unfolding finite_tree_iff by blast
  then have "finite (map (\<lambda>x. (x, True)) ` (set t \<inter> LS M qM))"
    by blast

  have "((\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) `
              {xs @ [x] |xs x. xs \<in> set t \<inter> LS M qM \<and> xs @ [x] \<in> set t - LS M qM})
        \<subseteq> ((\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) ` (set t))"
    by blast
  moreover have "finite ((\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) ` (set t))"
    using assms(3) unfolding finite_tree_iff by blast
  ultimately have "finite ((\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) `
              {xs @ [x] |xs x. xs \<in> set t \<inter> LS M qM \<and> xs @ [x] \<in> set t - LS M qM})"
    using finite_subset by blast
  then show ?thesis
    using \<open>finite (map (\<lambda>x. (x, True)) ` (set t \<inter> LS M qM))\<close>
    unfolding finite_tree_iff test_suite_from_io_tree_set[OF assms(1,2)]
    by blast
qed

    

lemma passes_test_case_prefix :
  assumes "observable M"
  and     "passes_test_case M q (iob@iob')"
shows "passes_test_case M q iob"
using assms(2) proof (induction iob arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons a iob)
  obtain x y b where "a = ((x,y),b)"
    by (metis prod.collapse)
  
  show ?case proof (cases b)
    case False
    then show ?thesis 
      using Cons.prems unfolding \<open>a = ((x,y),b)\<close> by auto
  next
    case True
    
    show ?thesis proof (cases "h_obs M q x y")
      case None
      then show ?thesis
        using Cons.prems unfolding \<open>a = ((x,y),b)\<close> by auto
    next
      case (Some q')
      then have "passes_test_case M q' (iob @ iob')"
        using True Cons.prems unfolding \<open>a = ((x,y),b)\<close> by auto
      then have "passes_test_case M q' iob"
        using Cons.IH by auto
      then show ?thesis 
        using True Some unfolding \<open>a = ((x,y),b)\<close> by auto
    qed
  qed
qed



lemma passes_test_cases_of_test_suite : 
  assumes "observable M" 
  and     "observable I"
  and     "qM \<in> states M"
  and     "qI \<in> states I"
  and     "finite_tree t"
shows "list_all (passes_test_case I qI) (sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M qM t)) = passes_test_suite I qI (test_suite_from_io_tree M qM t)"
  (is "?P1 = ?P2")
proof 

  have "list.set (sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M qM t)) = 
          {y \<in> Prefix_Tree.set (test_suite_from_io_tree M qM t). \<nexists>y'. y' \<noteq> [] \<and> y @ y' \<in> Prefix_Tree.set (test_suite_from_io_tree M qM t)}"
    using sorted_list_of_maximal_sequences_in_tree_set[OF test_suite_from_io_tree_finite_tree[OF assms(1,3,5)]] .

  show "?P1 \<Longrightarrow> ?P2"
  proof -
    assume ?P1
    show ?P2
      unfolding passes_test_suite_iff[OF assms(2,4)]
    proof 
      fix iob assume "iob \<in> Prefix_Tree.set (test_suite_from_io_tree M qM t)"
      
      then obtain iob' where "iob@iob' \<in> list.set (sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M qM t))"
        unfolding sorted_list_of_maximal_sequences_in_tree_set[OF test_suite_from_io_tree_finite_tree[OF assms(1,3,5)]]
        using test_suite_from_io_tree_finite_tree[OF assms(1,3,5)] unfolding finite_tree_iff 
        using prefix_free_set_maximal_list_ob[of "set (test_suite_from_io_tree M qM t)"]
        by blast

      then have "passes_test_case I qI (iob@iob')"
        using \<open>?P1\<close>
        by (metis in_set_conv_decomp_last list_all_append list_all_simps(1)) 
      then have "passes_test_case I qI iob"
        using passes_test_case_prefix[OF assms(2)] by auto
      then have "map fst (takeWhile snd iob) \<in> LS I qI"
            and "(\<not> list_all snd iob \<longrightarrow> map fst (take (Suc (length (takeWhile snd iob))) iob) \<notin> LS I qI)"
        unfolding passes_test_case_iff[OF assms(2,4)]
        by auto

      have "list_all snd iob \<Longrightarrow> (map fst iob \<in> LS I qI)"
        using \<open>map fst (takeWhile snd iob) \<in> LS I qI\<close>
        by (metis in_set_conv_decomp_last list_all_append list_all_simps(1) takeWhile_eq_all_conv) 
      moreover have "(map fst iob \<in> LS I qI) \<Longrightarrow> list_all snd iob"
        using \<open>(\<not> list_all snd iob \<longrightarrow> map fst (take (Suc (length (takeWhile snd iob))) iob) \<notin> LS I qI)\<close>
        by (metis append_take_drop_id language_prefix map_append) 
      ultimately show "(map fst iob \<in> LS I qI) = list_all snd iob"
        by blast
    qed
  qed

  show "?P2 \<Longrightarrow> ?P1"
  proof -
    assume ?P2

    have "\<And> iob . iob \<in> list.set (sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M qM t)) \<Longrightarrow> passes_test_case I qI iob"
    proof -
      fix iob
      assume "iob \<in> list.set (sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M qM t))"
      then have "iob \<in> set (test_suite_from_io_tree M qM t)"
        unfolding sorted_list_of_maximal_sequences_in_tree_set[OF test_suite_from_io_tree_finite_tree[OF assms(1,3,5)]]
        by blast
      then have *: "(map fst iob \<in> LS I qI) = list_all snd iob"
        using \<open>?P2\<close> unfolding passes_test_suite_iff[OF assms(2,4)]
        by blast

      consider "iob \<in> map (\<lambda>x. (x, True)) ` (Prefix_Tree.set t \<inter> LS M qM)" |
               "iob \<in> (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) `  {xs @ [x] |xs x. xs \<in> Prefix_Tree.set t \<inter> LS M qM \<and> xs @ [x] \<in> Prefix_Tree.set t - LS M qM}"
        using \<open>iob \<in> set (test_suite_from_io_tree M qM t)\<close>
        unfolding test_suite_from_io_tree_set[OF assms(1,3)]
        by blast
      then show "passes_test_case I qI iob" proof cases
        case 1
        then obtain io where "iob = map  (\<lambda>x. (x, True)) io"
          by blast
        have "list_all snd iob" 
          unfolding \<open>iob = map  (\<lambda>x. (x, True)) io\<close> by (induction io; auto)
        then have "(takeWhile snd iob) = iob"
          by (induction iob; auto)
        
        have "map fst (takeWhile snd iob) \<in> LS I qI"
          using * \<open>list_all snd iob\<close>
          by (simp add: \<open>takeWhile snd iob = iob\<close>)
        then show ?thesis 
          unfolding passes_test_case_iff[OF assms(2,4)]
          using \<open>list_all snd iob\<close>
          by auto
      next
        case 2
        then obtain xs x where "iob = (\<lambda>xs. map (\<lambda>x. (x, True)) (butlast xs) @ [(last xs, False)]) (xs@[x])"
                           and "xs \<in> set t \<inter> LS M qM" 
                           and "xs @ [x] \<in> Prefix_Tree.set t - LS M qM"
          by blast
        then have **: "iob = (map (\<lambda>x. (x, True)) xs) @ [(x,False)]"
          by auto

        have "isin (test_suite_from_io_tree M qM t) ((takeWhile snd iob)@(dropWhile snd iob))"
          using \<open>iob \<in> set (test_suite_from_io_tree M qM t)\<close> by auto
        then have "(takeWhile snd iob) \<in> set (test_suite_from_io_tree M qM t)"
          using isin_prefix[of "test_suite_from_io_tree M qM t" "takeWhile snd iob" "dropWhile snd iob"] by simp
        then have "(map fst (takeWhile snd iob) \<in> LS I qI) = list_all snd (takeWhile snd iob)"
          using \<open>?P2\<close> unfolding passes_test_suite_iff[OF assms(2,4)]
          by blast
        moreover have "list_all snd (takeWhile snd iob)"
          by (induction iob; auto)
        ultimately have "map fst (takeWhile snd iob) \<in> LS I qI"
          by simp
          
        have "\<not> list_all snd iob"
          using ** by auto
        moreover have "(take (Suc (length (takeWhile snd iob))) iob) = iob"
          unfolding \<open>iob = (map (\<lambda>x. (x, True)) xs) @ [(x,False)]\<close> by (induction xs; auto)
        ultimately have "map fst (take (Suc (length (takeWhile snd iob))) iob) \<notin> LS I qI"
          using * by simp
        
        then show ?thesis 
          using \<open>map fst (takeWhile snd iob) \<in> LS I qI\<close>
          unfolding passes_test_case_iff[OF assms(2,4)]
          by simp
      qed  
    qed  
    then show ?P1
      using Ball_set_list_all by blast
  qed
qed

lemma passes_test_cases_from_io_tree : 
  assumes "observable M" 
  and     "observable I"
  and     "qM \<in> states M"
  and     "qI \<in> states I"
  and     "finite_tree t"
shows "list_all (passes_test_case I qI) (sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M qM t)) = ((set t \<inter> LS M qM) = (set t \<inter> LS I qI))"
  unfolding passes_test_cases_of_test_suite[OF assms] passes_test_suite_from_io_tree[OF assms(1-4)]
  by blast



subsection \<open>Alternative Representations\<close>

subsubsection \<open>Pass and Fail Traces\<close>

type_synonym ('b,'c) pass_traces = "('b \<times> 'c) list list"
type_synonym ('b,'c) fail_traces = "('b \<times> 'c) list list"
type_synonym ('b,'c) trace_test_suite = "('b,'c) pass_traces \<times> ('b,'c) fail_traces"

fun trace_test_suite_from_tree :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('b \<times> 'c) prefix_tree \<Rightarrow> ('b,'c) trace_test_suite" where
  "trace_test_suite_from_tree M T = (let
      (passes',fails) = separate_by (is_in_language M (initial M)) (sorted_list_of_sequences_in_tree T);
      passes = sorted_list_of_maximal_sequences_in_tree (from_list passes')
    in (passes, fails))"

lemma trace_test_suite_from_tree_language_equivalence :
  assumes "observable M" and "finite_tree T"
  shows "(L M \<inter> set T = L M' \<inter> set T) = (list.set (fst (trace_test_suite_from_tree M T)) \<subseteq> L M' \<and> L M' \<inter> list.set (snd (trace_test_suite_from_tree M T)) = {})"
proof -

  obtain passes' fails where *: "(passes',fails) = separate_by (is_in_language M (initial M)) (sorted_list_of_sequences_in_tree T)"
    by auto
  
  define passes where "passes = sorted_list_of_maximal_sequences_in_tree (from_list passes')"

  have "fst (trace_test_suite_from_tree M T) = passes"
    using "*" passes_def by auto
  have "snd (trace_test_suite_from_tree M T) = fails"
    using "*" passes_def by auto

  have "list.set passes' = L M \<inter> set T"
    using * sorted_list_of_sequences_in_tree_set[OF assms(2)]
    unfolding separate_by.simps 
    unfolding is_in_language_iff[OF assms(1) fsm_initial]
    by (metis inter_set_filter old.prod.inject) 
  moreover have "list.set passes' \<subseteq> L M' = (list.set passes \<subseteq> L M')"
  proof -

    have "\<And> io . io \<in> list.set passes - {[]} \<Longrightarrow> \<exists> io' . io@io' \<in> list.set passes'"
      unfolding passes_def
      unfolding sorted_list_of_maximal_sequences_in_tree_set[OF from_list_finite_tree]
      unfolding from_list_set by force
    moreover have "[] \<in> list.set passes'"
      unfolding \<open>list.set passes' = L M \<inter> set T\<close> by auto
    ultimately have "\<And> io . io \<in> list.set passes \<Longrightarrow> \<exists> io' . io@io' \<in> list.set passes'"
      by force
    moreover have "\<And> io . io \<in> list.set passes' \<Longrightarrow> \<exists> io' . io@io' \<in> list.set passes"
    proof -
      have "\<And> io . io \<in> list.set passes' \<Longrightarrow> io \<in> set (from_list passes')"
        unfolding from_list_set by auto
      moreover have "\<And> io. io \<in> set (from_list passes') \<Longrightarrow> \<exists> io' . io@io' \<in> list.set passes"
        unfolding passes_def
        unfolding sorted_list_of_maximal_sequences_in_tree_set[OF from_list_finite_tree]
        using from_list_finite_tree sorted_list_of_maximal_sequences_in_tree_ob sorted_list_of_maximal_sequences_in_tree_set by fastforce 
      ultimately show "\<And> io . io \<in> list.set passes' \<Longrightarrow> \<exists> io' . io@io' \<in> list.set passes"
        by blast
    qed
    ultimately show ?thesis
      using language_prefix[of _ _ M' "initial M'"]
      by (meson subset_iff)
  qed
  moreover have "list.set fails = set T - L M"
    using * sorted_list_of_sequences_in_tree_set[OF assms(2)]
    unfolding separate_by.simps 
    unfolding is_in_language_iff[OF assms(1) fsm_initial]
    by (simp add: set_diff_eq)
  ultimately show ?thesis
    unfolding \<open>fst (trace_test_suite_from_tree M T) = passes\<close>
    unfolding \<open>snd (trace_test_suite_from_tree M T) = fails\<close>
    by blast
qed


subsubsection \<open>Input Sequences\<close>

fun test_suite_to_input_sequences :: "('b::linorder\<times>'c::linorder) prefix_tree \<Rightarrow> 'b list list" where
  "test_suite_to_input_sequences T = sorted_list_of_maximal_sequences_in_tree (from_list (map input_portion (sorted_list_of_maximal_sequences_in_tree T)))"

lemma test_suite_to_input_sequences_pass :
  fixes T :: "('b::linorder \<times> 'c::linorder) prefix_tree"
  assumes "finite_tree T"
  and     "(L M = L M') \<longleftrightarrow> (L M \<inter> set T = L M' \<inter> set T)"
  shows "(L M = L M') \<longleftrightarrow> ({io \<in> L M . (\<exists> xs \<in> list.set (test_suite_to_input_sequences T) . \<exists> xs' \<in> list.set (prefixes xs) . input_portion io = xs')}
                                          = {io \<in> L M' . (\<exists> xs \<in> list.set (test_suite_to_input_sequences T) . \<exists> xs' \<in> list.set (prefixes xs) . input_portion io = xs')})"
proof -

  have *: "\<And> io :: ('b::linorder \<times> 'c::linorder) list . 
              (\<exists> xs \<in> list.set (test_suite_to_input_sequences T) . \<exists> xs' \<in> list.set (prefixes xs) . input_portion io = xs') = (\<exists>io'\<in>set T. map fst io = map fst io')"
  proof -
    fix io :: "('b::linorder \<times> 'c::linorder) list"    

    have "(\<exists>io'\<in>set T. map fst io = map fst io') = (\<exists> \<alpha> \<in> list.set (sorted_list_of_maximal_sequences_in_tree T) . \<exists> \<alpha>' \<in> list.set (prefixes \<alpha>) . map fst io = map fst \<alpha>')"
    proof 
      have *: "\<And> io' . io'\<in>set T \<longleftrightarrow> (\<exists> io''. io'@io'' \<in> list.set (sorted_list_of_maximal_sequences_in_tree T))"
        using sorted_list_of_maximal_sequences_in_tree_set[OF assms(1)]
        using assms(1) set_prefix sorted_list_of_maximal_sequences_in_tree_ob by fastforce 
      
      show "(\<exists>io'\<in>set T. map fst io = map fst io') \<Longrightarrow> (\<exists> \<alpha> \<in> list.set (sorted_list_of_maximal_sequences_in_tree T) . \<exists> \<alpha>' \<in> list.set (prefixes \<alpha>) . map fst io = map fst \<alpha>')"
        by (metis append_Nil2 assms(1) prefixes_prepend prefixes_set_Nil sorted_list_of_maximal_sequences_in_tree_ob) 
      show "\<exists>\<alpha>\<in>list.set (sorted_list_of_maximal_sequences_in_tree T). \<exists>\<alpha>'\<in>list.set (prefixes \<alpha>). map fst io = map fst \<alpha>' \<Longrightarrow> \<exists>io'\<in>Prefix_Tree.set T. map fst io = map fst io'"
        by (metis "*" prefixes_set_ob)
    qed
    also have "\<dots> = (\<exists> xs \<in> list.set (map input_portion (sorted_list_of_maximal_sequences_in_tree T)) . \<exists> xs' \<in> list.set (prefixes xs) . map fst io = xs')"
    proof -
      have *: "list.set (map input_portion (sorted_list_of_maximal_sequences_in_tree T)) = input_portion ` (list.set (sorted_list_of_maximal_sequences_in_tree T))"
        by auto
      have **: "\<And> (\<alpha> :: ('b::linorder \<times> 'c::linorder) list) . (\<exists> \<alpha>' \<in> list.set (prefixes \<alpha>) . map fst io = map fst \<alpha>') = (\<exists> xs' \<in> list.set (prefixes (input_portion \<alpha>)) . map fst io = xs')"
      proof 
        fix \<alpha> :: "('b::linorder \<times> 'c::linorder) list"
        show "\<exists>\<alpha>'\<in>list.set (prefixes \<alpha>). map fst io = map fst \<alpha>' \<Longrightarrow> \<exists>xs'\<in>list.set (prefixes (map fst \<alpha>)). map fst io = xs'"
        proof -
          assume "\<exists>\<alpha>'\<in>list.set (prefixes \<alpha>). map fst io = map fst \<alpha>'"
          then obtain \<alpha>' \<alpha>'' where "\<alpha>'@\<alpha>'' = \<alpha>" and "map fst io = map fst \<alpha>'"
            unfolding prefixes_set by blast
          then show "\<exists>xs'\<in>list.set (prefixes (map fst \<alpha>)). map fst io = xs'"
            unfolding prefixes_set
            by auto
        qed
        show "\<exists>xs'\<in>list.set (prefixes (map fst \<alpha>)). map fst io = xs' \<Longrightarrow> \<exists>\<alpha>'\<in>list.set (prefixes \<alpha>). map fst io = map fst \<alpha>'"
        proof - 
          assume "\<exists>xs'\<in>list.set (prefixes (map fst \<alpha>)). map fst io = xs'"
          then obtain xs' xs'' where "xs'@xs'' = (map fst \<alpha>)" and "map fst io = xs'"
            unfolding prefixes_set by blast
          then have "map fst (take (length xs') \<alpha>) = map fst io"
            by (metis \<open>\<exists>xs'\<in>list.set (prefixes (map fst \<alpha>)). map fst io = xs'\<close> prefixes_take_iff take_map)
          moreover have "(take (length xs') \<alpha>) \<in> list.set (prefixes \<alpha>)"
            by (metis \<open>map fst io = xs'\<close> calculation length_map prefixes_take_iff) 
          ultimately show ?thesis
            by metis 
        qed
      qed
      show ?thesis 
        unfolding ** *
        by blast 
    qed
    also have "\<dots> = (\<exists> xs \<in> list.set (test_suite_to_input_sequences T) . \<exists> xs' \<in> list.set (prefixes xs) . input_portion io = xs')"
    proof 
      show "\<exists>xs\<in>list.set (map (map fst) (sorted_list_of_maximal_sequences_in_tree T)). \<exists>xs'\<in>list.set (prefixes xs). map fst io = xs' \<Longrightarrow> \<exists>xs\<in>list.set (test_suite_to_input_sequences T). \<exists>xs'\<in>list.set (prefixes xs). map fst io = xs'" 
      proof -
        assume "\<exists>xs\<in>list.set (map (map fst) (sorted_list_of_maximal_sequences_in_tree T)). \<exists>xs'\<in>list.set (prefixes xs). map fst io = xs'"
        then obtain xs' xs'' where "xs'@xs'' \<in> list.set (map (map fst) (sorted_list_of_maximal_sequences_in_tree T))"
                               and "map fst io = xs'"
          unfolding prefixes_set by blast
        then have *:"xs'@xs'' \<in> set (from_list (map (map fst) (sorted_list_of_maximal_sequences_in_tree T)))"
          unfolding from_list_set by blast

        show ?thesis 
          using sorted_list_of_maximal_sequences_in_tree_ob[OF from_list_finite_tree *] \<open>map fst io = xs'\<close>
          unfolding test_suite_to_input_sequences.simps
          by (metis append.assoc append_Nil2 prefixes_prepend prefixes_set_Nil) 
      qed
      show "\<exists>xs\<in>list.set (test_suite_to_input_sequences T). \<exists>xs'\<in>list.set (prefixes xs). map fst io = xs' \<Longrightarrow> \<exists>xs\<in>list.set (map (map fst) (sorted_list_of_maximal_sequences_in_tree T)). \<exists>xs'\<in>list.set (prefixes xs). map fst io = xs'"
      proof -
        assume "\<exists>xs\<in>list.set (test_suite_to_input_sequences T). \<exists>xs'\<in>list.set (prefixes xs). map fst io = xs'"
        then obtain xs' xs'' where "xs'@xs'' \<in> list.set (test_suite_to_input_sequences T)"
                               and "map fst io = xs'"
          unfolding prefixes_set by blast
        then have "xs'@xs'' = [] \<or> (\<exists> xs''' . (xs'@xs'')@xs'''\<in>list.set (map (map fst) (sorted_list_of_maximal_sequences_in_tree T)))"
          unfolding test_suite_to_input_sequences.simps 
          unfolding sorted_list_of_maximal_sequences_in_tree_set[OF from_list_finite_tree] 
          unfolding from_list_set
          by blast
        then obtain xs''' where "(xs'@xs'')@xs'''\<in>list.set (map (map fst) (sorted_list_of_maximal_sequences_in_tree T))"
          by (metis Nil_is_append_conv \<open>map fst io = xs'\<close> append.left_neutral calculation list.simps(8) set_Nil)
        then show ?thesis 
          using \<open>map fst io = xs'\<close>
          by (metis append.assoc append.right_neutral prefixes_prepend prefixes_set_Nil) 
      qed
    qed
    finally show "(\<exists> xs \<in> list.set (test_suite_to_input_sequences T) . \<exists> xs' \<in> list.set (prefixes xs) . input_portion io = xs') = (\<exists>io'\<in>set T. map fst io = map fst io')"
      by presburger
  qed
            
  show ?thesis
    unfolding *
    using equivalence_io_relaxation[OF assms(2)] .
qed

lemma test_suite_to_input_sequences_pass_alt_def :
  fixes T :: "('b::linorder \<times> 'c::linorder) prefix_tree"
  assumes "finite_tree T"
  and     "(L M = L M') \<longleftrightarrow> (L M \<inter> set T = L M' \<inter> set T)"
shows "(L M = L M') \<longleftrightarrow> (\<forall> xs \<in> list.set (test_suite_to_input_sequences T)  . \<forall> xs' \<in> list.set (prefixes xs) . {io \<in> L M . input_portion io = xs'} = {io \<in> L M' . input_portion io = xs'})"
  unfolding test_suite_to_input_sequences_pass[OF assms]
  by blast
  
end