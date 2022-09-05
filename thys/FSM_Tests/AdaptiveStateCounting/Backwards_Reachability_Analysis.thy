section \<open>Backwards Reachability Analysis\<close>

text \<open>This theory introduces function @{text "select_inputs"} which is used for the calculation of
      both state preambles and state separators.\<close>


theory Backwards_Reachability_Analysis
imports "../FSM"
begin


text \<open>Function @{text "select_inputs"} calculates an associative list that maps states to a single
      input each such that the FSM induced by this input selection is acyclic, single input and 
      whose only deadlock states (if any) are contained in @{text "stateSet"}.
      The following parameters are used: 
        1) transition function @{text "f"} (typically @{text "(h M)"} for some FSM @{text "M"})
        2) a source state @{text "q0"} (selection terminates as soon as this states is assigned some input)
        3) a list of inputs that may be assigned to states
        4) a list of states not yet taken (these are considered when searching for the next possible
          assignment)
        5) a set @{text "stateSet"} of all states that already have an input assigned to them by @{text "m"}
        6) an associative list @{text "m"} containing previously chosen assignments\<close>

function select_inputs :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "select_inputs f q0 inputList [] stateSet m = (case find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> stateSet))) inputList of 
      Some x \<Rightarrow> m@[(q0,x)] |
      None   \<Rightarrow> m)" |
  "select_inputs f q0 inputList (n#nL) stateSet m = 
    (case find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> stateSet))) inputList of 
      Some x \<Rightarrow> m@[(q0,x)] |
      None   \<Rightarrow> (case find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> stateSet))) (n#nL) inputList
          of None            \<Rightarrow> m |
             Some (q',x,stateList') \<Rightarrow> select_inputs f q0 inputList stateList' (insert q' stateSet) (m@[(q',x)])))"
  by pat_completeness auto
termination 
proof -
  {
    fix f :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set)"
    fix q0 :: 'a
    fix inputList :: "'b list"
    fix n :: 'a
    fix nL :: "'a list" 
    fix stateSet :: "'a set"
    fix m :: "('a \<times> 'b) list" 
    fix qynL' q ynL' x nL'
    assume "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> stateSet)) inputList = None"
       and "find_remove_2 (\<lambda>q' x. f (q', x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q', x). q'' \<in> stateSet)) (n # nL) inputList = Some qynL'"
       and "(q, ynL') = qynL'"
       and "(x, nL') = ynL'"
  
    then have *: "find_remove_2 (\<lambda>q' x. f (q', x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q', x). q'' \<in> stateSet)) (n # nL) inputList = Some (q,x,nL')"
      by auto
  
    have "q \<in> set (n # nL)"
    and  "nL' = remove1 q (n # nL)"
      using find_remove_2_set(2,6)[OF *] by simp+
  
    then have "length nL' < length (n # nL)"
      using remove1_length by metis
      
  
    then have "((f, q0, inputList, nL', insert q stateSet, m @ [(q, x)]), f, q0, inputList, n # nL, stateSet, m) 
                \<in> measure (\<lambda>(f, q0, iL, nL, nS, m). length nL)"
      by auto
  } 
  then show ?thesis 
    by (relation "measure (\<lambda> (f,q0,iL,nL,nS,m) . length nL)"; simp)
qed


lemma select_inputs_length :
  "length (select_inputs f q0 inputList stateList stateSet m) \<le> (length m) + Suc (length stateList)"
proof (induction "length stateList" arbitrary: stateList stateSet m)
  case 0
  then show ?case 
    by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> stateSet)) inputList"; auto)
next
  case (Suc k)
  then obtain n nL where "stateList = n # nL"
    by (meson Suc_length_conv) 

  show ?case 
  proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> stateSet))) inputList")
    case None
    then show ?thesis 
    proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> stateSet))) stateList inputList")
      case None
      then show ?thesis 
        using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> stateSet)) inputList = None\<close> 
        unfolding \<open>stateList = n # nL\<close> by auto
    next
      case (Some a)
      then obtain q' x stateList' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> stateSet))) (n#nL) inputList 
                                            = Some (q',x,stateList')"
        unfolding \<open>stateList = n # nL\<close> by (metis prod_cases3)
      have "k = length stateList'"
        using find_remove_2_length[OF *] \<open>Suc k = length stateList\<close> 
        unfolding \<open>stateList = n # nL\<close>
        by simp
      show ?thesis 
        using Suc.hyps(1)[of stateList' "insert q' stateSet" "m@[(q',x)]", OF \<open>k = length stateList'\<close>] 
        unfolding \<open>stateList = n # nL\<close> select_inputs.simps None * find_remove_2_length[OF *]        
        by simp
    qed
  next
    case (Some a)
    then show ?thesis 
      unfolding \<open>stateList = n # nL\<close> by auto
  qed
qed


lemma select_inputs_length_min :
  "length (select_inputs f q0 inputList stateList stateSet m) \<ge> (length m)"
proof (induction "length stateList" arbitrary: stateList stateSet m)
  case 0
  then show ?case 
    by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> stateSet)) inputList"; auto)
next
  case (Suc k)
  then obtain n nL where "stateList = n # nL"
    by (meson Suc_length_conv) 

  show ?case 
  proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> stateSet))) inputList")
    case None
    then show ?thesis 
    proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> stateSet))) stateList inputList")
      case None
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> stateSet)) inputList = None\<close> 
        unfolding \<open>stateList = n # nL\<close> by auto
    next
      case (Some a)
      then obtain q' x stateList' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> stateSet))) (n#nL) inputList 
                                              = Some (q',x,stateList')"
        unfolding \<open>stateList = n # nL\<close> by (metis prod_cases3)
      have "k = length stateList'"
        using find_remove_2_length[OF *] \<open>Suc k = length stateList\<close> 
        unfolding \<open>stateList = n # nL\<close>
        by simp
      show ?thesis 
        unfolding \<open>stateList = n # nL\<close> select_inputs.simps None * find_remove_2_length[OF *]
        using Suc.hyps(1)[of stateList' "m@[(q',x)]" "insert q' stateSet" , OF \<open>k = length stateList'\<close>]  
        by simp
    qed
  next
    case (Some a)
    then show ?thesis unfolding \<open>stateList = n # nL\<close> by auto
  qed
qed


lemma select_inputs_helper1 :
  "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = Some x 
    \<Longrightarrow> (select_inputs f q0 iL nL nS m) = m@[(q0,x)]" 
  by (cases nL; auto)


lemma select_inputs_take :
  "take (length m) (select_inputs f q0 inputList stateList stateSet m) = m"
proof (induction "length stateList" arbitrary: stateList stateSet m)
  case 0
  then show ?case 
    by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> stateSet)) inputList"; auto)
next
  case (Suc k)
  then obtain n nL where "stateList = n # nL"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> stateSet))) inputList")
    case None
    then show ?thesis 
    proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> stateSet))) stateList inputList")
      case None
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> stateSet)) inputList = None\<close> 
        unfolding \<open>stateList = n # nL\<close> by auto
    next
      case (Some a)
      then obtain q' x stateList' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> stateSet))) (n#nL) inputList 
                                            = Some (q',x,stateList')"
        unfolding \<open>stateList = n # nL\<close> 
        by (metis prod_cases3)
      have "k = length stateList'"
        using find_remove_2_length[OF *] \<open>Suc k = length stateList\<close> 
        unfolding \<open>stateList = n # nL\<close>
        by simp

      have **: "(select_inputs f q0 inputList stateList stateSet m) 
                  = select_inputs f q0 inputList stateList' (insert q' stateSet) (m @ [(q', x)])"
        unfolding \<open>stateList = n # nL\<close> select_inputs.simps None * 
        by simp
      show ?thesis
        unfolding ** 
        using Suc.hyps(1)[of stateList' "m@[(q',x)]" "insert q' stateSet" , OF \<open>k = length stateList'\<close>]  
        by (metis butlast_snoc butlast_take diff_Suc_1 length_append_singleton select_inputs_length_min) 
    qed
  next
    case (Some a)
    then show ?thesis unfolding \<open>stateList = n # nL\<close> by auto
  qed
qed


lemma select_inputs_take' :
  "take (length m) (select_inputs f q0 iL nL nS (m@m')) = m"
  using select_inputs_take
  by (metis (no_types, lifting) add_leE append_eq_append_conv select_inputs_length_min length_append 
        length_take min_absorb2 take_add)


lemma select_inputs_distinct :
  assumes "distinct (map fst m)"
  and     "set (map fst m) \<subseteq> nS"
  and     "q0 \<notin> nS"
  and     "distinct nL"
  and     "q0 \<notin> set nL"
  and     "set nL \<inter> nS = {}"
  shows "distinct (map fst (select_inputs f q0 iL nL nS m))" 
using assms proof (induction "length nL" arbitrary: nL nS m)
  case 0
  then show ?case 
    by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL"; auto)
next
  case (Suc k)
  then obtain n nL'' where "nL = n # nL''"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    then show ?thesis 
    proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then have "(select_inputs f q0 iL nL nS m) = m"
        using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> 
        unfolding \<open>nL = n # nL''\<close> by auto
      then show ?thesis 
        using Suc.prems by auto
    next
      case (Some a)
      then obtain q' x nL' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL 
                                      = Some (q',x,nL')"
        by (metis prod_cases3)

      have "k = length nL'"
        using find_remove_2_length[OF *] \<open>Suc k = length nL\<close> 
        by simp

      have "select_inputs f q0 iL nL nS m = select_inputs f q0 iL nL' (insert q' nS) (m @ [(q', x)])" 
        using *
        unfolding  \<open>nL = n # nL''\<close> select_inputs.simps None 
        by auto

      have "q' \<in> set nL"
      and  "set nL' = set nL - {q'}"
      and  "distinct nL'"
        using find_remove_2_set[OF * ]  \<open>distinct nL\<close> by auto

      have "distinct (map fst (m@[(q',x)]))" 
        using \<open>(set (map fst m)) \<subseteq> nS\<close> \<open>set nL \<inter> nS = {}\<close> \<open>q' \<in> set nL\<close> \<open>distinct (map fst m)\<close> 
        by auto
      have "q0 \<notin> insert q' nS"
        using Suc.prems(3) Suc.prems(5) \<open>q' \<in> set nL\<close> by auto
      have "set (map fst (m@[(q',x)])) \<subseteq> insert q' nS" 
        using \<open>(set (map fst m)) \<subseteq> nS\<close> by auto
      have "(set (map fst (m@[(q',x)]))) \<subseteq> insert q' nS"
        using\<open>(set (map fst m)) \<subseteq> nS\<close> by auto
      have "q0 \<notin> set nL'"
        by (simp add: Suc.prems(5) \<open>set nL' = set nL - {q'}\<close>)
      have "set nL' \<inter> insert q' nS = {}"
        using Suc.prems(6) \<open>set nL' = set nL - {q'}\<close> by auto

      show ?thesis 
        unfolding select_inputs.simps None *
        using Suc.hyps(1)[OF \<open>k = length nL'\<close> \<open>distinct (map fst (m@[(q',x)]))\<close>
                               \<open>set (map fst (m@[(q',x)])) \<subseteq> insert q' nS\<close>
                               \<open>q0 \<notin> insert q' nS\<close>
                               \<open>distinct nL'\<close>
                               \<open>q0 \<notin> set nL'\<close>
                               \<open>set nL' \<inter> insert q' nS = {}\<close>]
        unfolding \<open>select_inputs f q0 iL nL nS m = select_inputs f q0 iL nL' (insert q' nS) (m @ [(q', x)])\<close> 
        by assumption
    qed
  next
    case (Some a)
    then show ?thesis 
      using Suc \<open>nL = n # nL''\<close> by auto
  qed
qed


lemma select_inputs_index_properties : 
  assumes "i < length (select_inputs (h M) q0 iL nL nS m)"
  and     "i \<ge> length m"
  and     "distinct (map fst m)"
  and     "nS = nS0 \<union> set (map fst m)"
  and     "q0 \<notin> nS"
  and     "distinct nL"
  and     "q0 \<notin> set nL"
  and     "set nL \<inter> nS = {}"
shows "fst (select_inputs (h M) q0 iL nL nS m ! i) \<in> (insert q0 (set nL))" 
      "fst (select_inputs (h M) q0 iL nL nS m ! i) \<notin> nS0"
      "snd (select_inputs (h M) q0 iL nL nS m ! i) \<in> set iL"
      "(\<forall> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst (select_inputs (h M) q0 iL nL nS m ! i) \<noteq> fst qx')"
      "(\<exists> t \<in> transitions M . t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i))"
      "(\<forall> t \<in> transitions M . (t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i)) \<longrightarrow> (t_target t \<in> nS0 \<or> (\<exists> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst qx' = (t_target t))))"
proof -
  have combined_props : 
    "fst (select_inputs (h M) q0 iL nL nS m ! i) \<in> (insert q0 (set nL))
      \<and> snd (select_inputs (h M) q0 iL nL nS m ! i) \<in> set iL
      \<and> fst (select_inputs (h M) q0 iL nL nS m ! i) \<notin> nS0
      \<and> (\<exists> t \<in> transitions M . t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i))
      \<and> (\<forall> t \<in> transitions M . (t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i)) \<longrightarrow> (t_target t \<in> nS0 \<or> (\<exists> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst qx' = (t_target t))))"    
  using assms proof (induction "length nL" arbitrary: nL nS m)
    case 0
    show ?case proof (cases "find (\<lambda> x . (h M) (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q0,x) . (q'' \<in> nS))) iL")
      case None
      then have "(select_inputs (h M) q0 iL nL nS m) = m" using 0 by auto
      then have "False" using "0.prems"(1,2) by auto
      then show ?thesis by simp
    next
      case (Some x)
      have "(select_inputs (h M) q0 iL nL nS m) = m@[(q0,x)]" using select_inputs_helper1[OF Some] by assumption
      then have "(select_inputs (h M) q0 iL nL nS m ! i) = (q0,x)" using "0.prems"(1,2)
        using antisym by fastforce 
  
      have "fst (q0, x) \<in> insert q0 (set nL)" by auto
      moreover have "snd (q0, x) \<in> set iL" using find_set[OF Some] by auto
      moreover have "fst (select_inputs (h M) q0 iL nL nS m ! i) \<notin> nS0"
        using \<open>select_inputs (h M) q0 iL nL nS m ! i = (q0, x)\<close> assms(4) assms(5) by auto
       
      moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = fst (q0, x) \<and> t_input t = snd (q0, x))"
        using find_condition[OF Some] unfolding fst_conv snd_conv h.simps
        by fastforce 
      moreover have "\<And> t . t \<in> FSM.transitions M \<Longrightarrow>
          t_source t = fst (q0, x) \<Longrightarrow> t_input t = snd (q0, x) \<Longrightarrow>
          t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t)"   
      proof -
        fix t assume "t \<in> FSM.transitions M" "t_source t = fst (q0, x)" "t_input t = snd (q0, x)"
        then have "t_target t \<in> nS"
          using find_condition[OF Some] unfolding h.simps fst_conv snd_conv
          by (metis (no_types, lifting) case_prod_beta' h_simps mem_Collect_eq prod.collapse)
        then show "t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t)"
          using \<open>nS = nS0 \<union> set (map fst m)\<close>
          using "0.prems"(1) "0.prems"(2) \<open>select_inputs (h M) q0 iL nL nS m = m @ [(q0, x)]\<close> by fastforce    
      qed
        
      ultimately show ?thesis 
        unfolding \<open>(select_inputs (h M) q0 iL nL nS m ! i) = (q0,x)\<close> by blast
    qed
  next
    case (Suc k)
    then obtain n nL'' where "nL = n # nL''"
      by (meson Suc_length_conv) 

    show ?case proof (cases "find (\<lambda> x . (h M) (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q0,x) . (q'' \<in> nS))) iL")
      case None
      show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . (h M) (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q',x) . (q'' \<in> nS))) nL iL")
        case None
        then have "(select_inputs (h M) q0 iL nL nS m) = m" using \<open>find (\<lambda>x. h M (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>h M (q0, x). q'' \<in> nS)) iL = None\<close> \<open>nL = n # nL''\<close> by auto
        then have "False" using Suc.prems(1,2) by auto
        then show ?thesis by simp
      next
        case (Some a)
        then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . (h M) (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
          by (metis prod_cases3)

        have "k = length nL'"
          using find_remove_2_length[OF **] \<open>Suc k = length nL\<close> by simp

        have "select_inputs (h M) q0 iL nL nS m = select_inputs (h M) q0 iL nL' (insert q' nS) (m @ [(q', x)])" 
          using **
          unfolding  \<open>nL = n # nL''\<close> select_inputs.simps None by auto
        then have "i < length (select_inputs (h M) q0 iL nL' (insert q' nS) (m@[(q',x)]))"
          using Suc.prems(1) by auto

        have "(set (map fst (m @ [(q', x)]))) \<subseteq> insert q' nS"
          using Suc.prems(4) by auto

        have "q' \<in> set nL"
        and  "set nL' = set nL - {q'}"
        and  "distinct nL'"
          using find_remove_2_set[OF ** ]  \<open>distinct nL\<close> by auto
        have "set nL' \<subseteq> set nL"
          using find_remove_2_set(4)[OF ** \<open>distinct nL\<close>] by blast

        have "distinct (map fst (m @ [(q', x)]))" 
          using Suc.prems(4) \<open>set nL \<inter> nS = {}\<close> \<open>q' \<in> set nL\<close> \<open>distinct (map fst m)\<close> by auto
        have "distinct (map fst (m@[(q',x)]))" 
          using Suc.prems(4) \<open>set nL \<inter> nS = {}\<close> \<open>q' \<in> set nL\<close> \<open>distinct (map fst m)\<close> by auto
        have "q0 \<notin> insert q' nS"
          using Suc.prems(7) Suc.prems(5) \<open>q' \<in> set nL\<close> by auto
        have "insert q' nS = nS0 \<union> set (map fst (m@[(q',x)]))" 
          using Suc.prems(4) by auto
        have "q0 \<notin> set nL'"
          by (metis Suc.prems(7) \<open>set nL' \<subseteq> set nL\<close> subset_code(1))
        have "set nL' \<inter> insert q' nS = {}"
          using Suc.prems(8) \<open>set nL' = set nL - {q'}\<close> by auto


        show ?thesis proof (cases "length (m @ [(q', x)]) \<le> i")
          case True

          show ?thesis
            using Suc.hyps(1)[OF \<open>k = length nL'\<close> \<open>i < length (select_inputs (h M) q0 iL nL' (insert q' nS) (m@[(q',x)]))\<close>
                            True
                            \<open>distinct (map fst (m @ [(q', x)]))\<close>
                            \<open>insert q' nS = nS0 \<union> set (map fst (m@[(q',x)]))\<close>
                            \<open>q0 \<notin> insert q' nS\<close>
                            \<open>distinct nL'\<close>
                            \<open>q0 \<notin> set nL'\<close>
                            \<open>set nL' \<inter> insert q' nS = {}\<close> ]
            unfolding \<open>select_inputs (h M) q0 iL nL nS m = select_inputs (h M) q0 iL nL' (insert q' nS) (m@[(q',x)])\<close> 
            using \<open>set nL' \<subseteq> set nL\<close> by blast
        next
          case False 
          then have "i = length m"
            using Suc.prems(2) by auto
          then have ***: "select_inputs (h M) q0 iL nL nS m ! i = (q',x)"
            unfolding \<open>select_inputs (h M) q0 iL nL nS m = select_inputs (h M) q0 iL nL' (insert q' nS) (m@[(q',x)])\<close> 
            using select_inputs_take
            by (metis length_append_singleton lessI nth_append_length nth_take) 
            
          
          have "q' \<in> insert q0 (set nL)"
            by (simp add: \<open>q' \<in> set nL\<close>) 
          moreover have "x \<in> set iL"
            using find_remove_2_set(3)[OF ** ] by auto
          moreover have "q' \<notin> nS0"
            using Suc.prems(4) Suc.prems(8) \<open>q' \<in> set nL\<close> by blast
          moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = q' \<and> t_input t = x) "
            using find_remove_2_set(1)[OF ** ] unfolding h.simps by force
          moreover have "(\<forall>t\<in>FSM.transitions M. t_source t = q' \<and> t_input t = x \<longrightarrow> t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t))"
            unfolding \<open>i = length m\<close> select_inputs_take 
            using find_remove_2_set(1)[OF ** ] unfolding h.simps \<open>nS = nS0 \<union> (set (map fst m))\<close> by force
          ultimately show ?thesis 
            unfolding *** fst_conv snd_conv by blast
        qed 
      qed
    next
      case (Some x)
      have "(select_inputs (h M) q0 iL nL nS m) = m@[(q0,x)]" using select_inputs_helper1[OF Some] by assumption
      then have "(select_inputs (h M) q0 iL nL nS m ! i) = (q0,x)" using Suc.prems(1,2)
        using antisym by fastforce 
  
      have "fst (q0, x) \<in> insert q0 (set nL)" by auto
      moreover have "snd (q0, x) \<in> set iL" using find_set[OF Some] by auto
      moreover have "fst (q0, x) \<notin> nS0"
        using assms(4) assms(5) by auto 
      moreover have "\<And> qx' . qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) - set (take (length m) (select_inputs (h M) q0 iL nL nS m)) \<Longrightarrow> fst (q0, x) \<noteq> fst qx'"
        using Suc.prems(1,2) \<open>select_inputs (h M) q0 iL nL nS m = m @ [(q0, x)]\<close> by auto
      moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = fst (q0, x) \<and> t_input t = snd (q0, x))"
        using find_condition[OF Some] unfolding fst_conv snd_conv h.simps
        by fastforce 
      moreover have "\<And> t . t \<in> FSM.transitions M \<Longrightarrow>
          t_source t = fst (q0, x) \<Longrightarrow> t_input t = snd (q0, x) \<Longrightarrow>
          t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t)"   
      proof -
        fix t assume "t \<in> FSM.transitions M" "t_source t = fst (q0, x)" "t_input t = snd (q0, x)"
        then have "t_target t \<in> nS"
          using find_condition[OF Some] unfolding h.simps fst_conv snd_conv
          by (metis (no_types, lifting) case_prod_beta' h_simps mem_Collect_eq prod.collapse) 
        then show "t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t)"
          using \<open>nS = nS0 \<union> (set (map fst m))\<close>
          using Suc.prems(1,2) \<open>select_inputs (h M) q0 iL nL nS m = m @ [(q0, x)]\<close> by fastforce    
      qed
        
      ultimately show ?thesis 
        unfolding \<open>(select_inputs (h M) q0 iL nL nS m ! i) = (q0,x)\<close> by blast
    qed
  qed

  then show "fst (select_inputs (h M) q0 iL nL nS m ! i) \<in> (insert q0 (set nL))"
            "snd (select_inputs (h M) q0 iL nL nS m ! i) \<in> set iL"
            "fst (select_inputs (h M) q0 iL nL nS m ! i) \<notin> nS0"
            "(\<exists> t \<in> transitions M . t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i))"
            "(\<forall> t \<in> transitions M . (t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i)) \<longrightarrow> (t_target t \<in> nS0 \<or> (\<exists> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst qx' = (t_target t))))"
    by blast+

  show "(\<forall> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst (select_inputs (h M) q0 iL nL nS m ! i) \<noteq> fst qx')" 
  proof 
    fix qx' assume "qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m))"
    then obtain j where "(take i (select_inputs (h M) q0 iL nL nS m)) ! j = qx'" and "j < length (take i (select_inputs (h M) q0 iL nL nS m))"
      by (meson in_set_conv_nth)
    then have "fst qx' = (map fst (select_inputs (h M) q0 iL nL nS m)) ! j" and "j < length (select_inputs (h M) q0 iL nL nS m)" by auto
      
    moreover have "fst (select_inputs (h M) q0 iL nL nS m ! i) = (map fst (select_inputs (h M) q0 iL nL nS m)) ! i"
      using assms(1) by auto

    moreover have "j \<noteq> i" 
      using \<open>j < length (take i (select_inputs (h M) q0 iL nL nS m))\<close> by auto

    moreover have "set (map fst m) \<subseteq> nS"
      using \<open>nS = nS0 \<union> set (map fst m)\<close> by blast

    ultimately show "fst (select_inputs (h M) q0 iL nL nS m ! i) \<noteq> fst qx'"
      using assms(1)
      using select_inputs_distinct[OF \<open>distinct (map fst m)\<close> _ \<open>q0 \<notin> nS\<close> \<open>distinct nL\<close> \<open>q0 \<notin> set nL\<close> \<open>set nL \<inter> nS = {}\<close>]
      by (metis distinct_Ex1 in_set_conv_nth length_map)
  qed
qed 


lemma select_inputs_initial :
  assumes "qx \<in> set (select_inputs f q0 iL nL nS m) - set m"
  and     "fst qx = q0"
  shows "(last (select_inputs f q0 iL nL nS m)) = qx"
using assms(1) proof (induction "length nL" arbitrary: nS nL m)
  case 0
  then have "nL = []" by auto

  have "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL \<noteq> None" 
    using 0 unfolding \<open>nL = []\<close> select_inputs.simps 
    by (metis Diff_cancel empty_iff option.simps(4))
  then obtain x where *: "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = Some x" 
    by auto
  
  have "set (select_inputs f q0 iL nL nS m) - set m = {qx}"
    using "0.prems"(1) unfolding select_inputs_helper1[OF *]
    by auto 
  
  then show ?case unfolding select_inputs_helper1[OF *]
    by (metis DiffD1 DiffD2 UnE empty_iff empty_set insert_iff last_snoc list.simps(15) set_append) 
next
  case (Suc k)
  then obtain n nL'' where "nL = n # nL''"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      have "(select_inputs f q0 iL nL nS m) = m"
        using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> None \<open>nL = n # nL''\<close> by auto
      then have "False" 
        using Suc.prems(1)
        by simp
      then show ?thesis by simp
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)

      have "k = length nL'"
        using find_remove_2_length[OF **] \<open>Suc k = length nL\<close> by simp

      have "select_inputs f q0 iL nL nS m = select_inputs f q0 iL nL' (insert q' nS) (m @ [(q', x)])" 
        using **
        unfolding  \<open>nL = n # nL''\<close> select_inputs.simps None by auto
      then have "qx \<in> set (select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)])) - set m"
        using Suc.prems by auto
      moreover have "q0 \<noteq> q'"
        using None unfolding find_None_iff
        using find_remove_2_set(1,2,3)[OF **]
        by blast
      ultimately have "qx \<in> set (select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)])) - set (m@[(q',x)])"
        using \<open>fst qx = q0\<close> by auto
      then show ?thesis 
        using Suc.hyps unfolding \<open>(select_inputs f q0 iL nL nS m) = (select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)]))\<close>
        using \<open>k = length nL'\<close> by blast 
    qed
  next
    case (Some a)

    have "set (select_inputs f q0 iL nL nS m ) - set m = {qx}"
      using Suc.prems(1) unfolding select_inputs_helper1[OF Some]
      by auto 
    
    then show ?thesis unfolding select_inputs_helper1[OF Some]
      by (metis DiffD1 DiffD2 UnE empty_iff empty_set insert_iff last_snoc list.simps(15) set_append)
  qed 
qed


lemma select_inputs_max_length :
  assumes "distinct nL"
  shows "length (select_inputs f q0 iL nL nS m) \<le> length m + Suc (length nL)" 
using assms proof (induction "length nL" arbitrary: nL nS m)
  case 0
  then show ?case by (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL"; auto)
next
  case (Suc k)
  then obtain n nL'' where "nL = n # nL''"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      show ?thesis unfolding \<open>nL = n # nL''\<close> select_inputs.simps None \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close>
        using None \<open>nL = n # nL''\<close> by auto 
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)
      have "k = length nL'"
        using find_remove_2_length[OF **] \<open>Suc k = length nL\<close> by simp

      have "select_inputs f q0 iL nL nS m = select_inputs f q0 iL nL' (insert q' nS) (m @ [(q', x)])" 
        using **
        unfolding  \<open>nL = n # nL''\<close> select_inputs.simps None by auto
      
      have "length nL = Suc (length nL') \<and> distinct nL'"
        using find_remove_2_set(2,4,5)[OF **] \<open>distinct nL\<close>
        by (metis One_nat_def Suc_pred distinct_card distinct_remove1 equals0D length_greater_0_conv length_remove1 set_empty2 set_remove1_eq) 
      then have "length (select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)])) \<le> length m + Suc (length nL)"
        using Suc.hyps(1)[OF \<open>k = length nL'\<close>]
        by (metis add_Suc_shift length_append_singleton)
      then show ?thesis 
        using \<open>(select_inputs f q0 iL nL nS m) = select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)])\<close> by simp
    qed
  next
    case (Some a)
    show ?thesis unfolding select_inputs_helper1[OF Some] by auto 
  qed
qed


lemma select_inputs_q0_containment :
  assumes "f (q0,x) \<noteq> {}"
  and     "(\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))"   
  and     "x \<in> set iL"
shows "(\<exists> qx \<in> set (select_inputs f q0 iL nL nS m) . fst qx = q0)" 
proof -
  have "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL \<noteq> None"
    using assms unfolding find_None_iff by blast
  then obtain x' where *: "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL = Some x'"
    by auto
  show ?thesis 
    unfolding select_inputs_helper1[OF *] by auto
qed


lemma select_inputs_from_submachine :
  assumes "single_input S"
  and     "acyclic S"
  and     "is_submachine S M"
  and     "\<And> q x . q \<in> reachable_states S \<Longrightarrow> h S (q,x) \<noteq> {} \<Longrightarrow> h S (q,x) = h M (q,x)"
  and     "\<And> q . q \<in> reachable_states S \<Longrightarrow> deadlock_state S q \<Longrightarrow> q \<in> nS0 \<union> set (map fst m)" 
  and     "states M = insert (initial S) (set nL \<union> nS0 \<union> set (map fst m))"
  and     "(initial S) \<notin> (set nL \<union> nS0 \<union> set (map fst m))"
shows "fst (last (select_inputs (h M) (initial S) (inputs_as_list M) nL (nS0 \<union> set (map fst m)) m)) = (initial S)"
and   "length (select_inputs (h M) (initial S) (inputs_as_list M) nL (nS0 \<union> set (map fst m)) m) > 0"
proof -
  have "fst (last (select_inputs (h M) (initial S) (inputs_as_list M) nL (nS0 \<union> set (map fst m)) m)) = (initial S) \<and> length (select_inputs (h M) (initial S) (inputs_as_list M) nL (nS0 \<union> set (map fst m)) m) > 0"
  using assms(5,6,7) proof (induction "length nL" arbitrary: nL m)
    case 0
    then have "nL = []" by auto
  
    have "\<not> (deadlock_state S (initial S))"
      using assms(5,6,3,7) reachable_states_initial by blast 
    then obtain x where "x \<in> set (inputs_as_list M)" and "h S ((initial S),x) \<noteq> {}"
      using assms(3) unfolding deadlock_state.simps h.simps inputs_as_list_set 
      by fastforce 
    
    then have "h M ((initial S),x) \<noteq> {}"
      using assms(4)[OF reachable_states_initial]  by fastforce 
    
  
    have "(initial S) \<in> reachable_states M"
      using assms(3) reachable_states_initial by auto
      
    then have "(initial S) \<in> states M"
      using reachable_state_is_state by force
    
  
    have "\<And> y q'' . (y,q'') \<in> h M ((initial S),x) \<Longrightarrow> q'' \<in> (nS0 \<union> set (map fst m))"
    proof -
      fix y q'' assume "(y,q'') \<in> h M ((initial S),x)"
      then have "q'' \<in> reachable_states M" using fsm_transition_target unfolding h.simps
        using \<open>FSM.initial S \<in> reachable_states M\<close> reachable_states_next by fastforce    
      then have "q'' \<in> insert (initial S) (nS0 \<union> set (map fst m))" using "0.prems"(2) \<open>nL = []\<close>
        using reachable_state_is_state by force
      moreover have "q'' \<noteq> (initial S)"
        using acyclic_no_self_loop[OF \<open>acyclic S\<close> reachable_states_initial]
        using \<open>(y,q'') \<in> h M ((initial S),x)\<close> assms(4)[OF reachable_states_initial \<open>h S ((initial S),x) \<noteq> {}\<close>] unfolding h_simps
        by blast 
      ultimately show "q'' \<in> (nS0 \<union> set (map fst m))" by blast
    qed
    then have "x \<in> set (inputs_as_list M) \<and> h M ((initial S), x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>h M ((initial S), x). q'' \<in> nS0 \<union> set (map fst m))"
      using \<open>x \<in> set (inputs_as_list M) \<close> \<open>h M ((initial S), x) \<noteq> {}\<close> by blast
    then have "find (\<lambda> x . (h M) ((initial S),x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) ((initial S),x) . (q'' \<in> (nS0 \<union> set (map fst m))))) (inputs_as_list M) \<noteq> None"
      unfolding find_None_iff by blast
    then show ?case
      unfolding \<open>nL = []\<close> select_inputs.simps by auto
  next
    case (Suc k)
    then obtain n nL'' where "nL = n # nL''"
      by (meson Suc_length_conv) 
  
  
    have "\<exists> q x . q \<in> reachable_states S - (nS0 \<union> set (map fst m)) \<and> h M (q,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> h M (q,x) . q'' \<in> (nS0 \<union> set (map fst m)))"
    proof -
      define ndlps where ndlps_def: "ndlps = {p . path S (initial S) p \<and> target (initial S) p \<notin> (nS0 \<union> set (map fst m))}"
  
      have "path S (initial S) [] \<and> target (initial S) [] \<notin> (nS0 \<union> set (map fst m))"
        using Suc.prems(3) by auto
      then have "[] \<in> ndlps"
        unfolding ndlps_def by blast
      then have "ndlps \<noteq> {}" by auto
      moreover have "finite ndlps"
        using acyclic_finite_paths_from_reachable_state[OF \<open>acyclic S\<close>, of "[]"] unfolding ndlps_def by fastforce
      ultimately have "\<exists> p \<in> ndlps . \<forall> p' \<in> ndlps . length p' \<le> length p"
        by (meson max_length_elem not_le_imp_less) 
      then obtain p where "path S (initial S) p"
                          and "target (initial S) p \<notin> (nS0 \<union> set (map fst m))"
                          and "\<And> p' . path S (initial S) p' \<Longrightarrow> target (initial S) p' \<notin> (nS0 \<union> set (map fst m)) \<Longrightarrow> length p' \<le> length p"
        unfolding ndlps_def by blast
      
  
      let ?q = "target (initial S) p"
      have "\<not> deadlock_state S ?q"
        using Suc.prems(1) reachable_states_intro[OF \<open>path S (initial S) p\<close>] using \<open>?q \<notin> (nS0 \<union> set (map fst m))\<close> by blast
      then obtain x where "h S (?q,x) \<noteq> {}"
        unfolding deadlock_state.simps h.simps by fastforce
      then have "h M (?q,x) \<noteq> {}"
        using assms(4)[of ?q _] reachable_states_intro[OF \<open>path S (initial S) p\<close>]
        by blast      
  
      moreover have "\<And> y q'' . (y,q'') \<in> h M (?q,x) \<Longrightarrow> q'' \<in> (nS0 \<union> set (map fst m))"
      proof (rule ccontr)
        fix y q'' assume "(y,q'') \<in> h M (?q,x)" and "q'' \<notin> nS0 \<union> set (map fst m)"
        then have "(?q,x,y,q'') \<in> transitions S"
          using assms(4)[OF reachable_states_intro[OF \<open>path S (initial S) p\<close>] \<open>h S (?q,x) \<noteq> {}\<close>] unfolding h_simps
          by blast 
        then have "path S (initial S) (p@[(?q,x,y,q'')])"
          using \<open>path S (initial S) p\<close> by (simp add: path_append_transition)
        moreover have "target (initial S) (p@[(?q,x,y,q'')]) \<notin> (nS0 \<union> set (map fst m))"
          using \<open>q'' \<notin> nS0 \<union> set (map fst m)\<close> by auto
        ultimately show "False"
          using \<open>\<And> p' . path S (initial S) p' \<Longrightarrow> target (initial S) p' \<notin> (nS0 \<union> set (map fst m)) \<Longrightarrow> length p' \<le> length p\<close>[of "(p@[(?q,x,y,q'')])"] by simp
      qed
  
      moreover have "?q \<in> reachable_states S - (nS0 \<union> set (map fst m))"
        using  \<open>?q \<notin> (nS0 \<union> set (map fst m))\<close> \<open>path S (initial S) p\<close>  by blast
      
      ultimately show ?thesis by blast
    qed
    
    then obtain q x where "q \<in> reachable_states S" and "q \<notin> (nS0 \<union> set (map fst m))" and "h M (q,x) \<noteq> {}" and "(\<forall> (y,q'') \<in> h M (q,x) . q'' \<in> (nS0 \<union> set (map fst m)))"
      by blast
    then have "x \<in> set (inputs_as_list M)"
      unfolding h.simps using fsm_transition_input inputs_as_list_set by fastforce 
  
    
  
    show ?case proof (cases "q = initial S")
      case True
      have "find (\<lambda>x. h M (FSM.initial S, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>h M (FSM.initial S, x). q'' \<in> nS0 \<union> set (map fst m))) (inputs_as_list M) \<noteq> None"
        using \<open>h M (q,x) \<noteq> {}\<close> \<open>(\<forall> (y,q'') \<in> h M (q,x) . q'' \<in> (nS0 \<union> set (map fst m)))\<close> \<open>x \<in> set (inputs_as_list M)\<close>
        unfolding True find_None_iff by blast
      then show ?thesis unfolding \<open>nL = n # nL''\<close> by auto
    next
      case False
      then have "q \<in> set nL" 
        using submachine_reachable_subset[OF \<open>is_submachine S M\<close>]
        unfolding is_submachine.simps \<open>states M = insert (initial S) (set nL \<union> nS0 \<union> set (map fst m))\<close>
        using \<open>q \<in> reachable_states S\<close>  \<open>q \<notin> (nS0 \<union> set (map fst m))\<close>
        by (metis (no_types, lifting) Suc.prems(2) UnE insertE reachable_state_is_state subsetD sup_assoc) 
        
  
      
      show ?thesis proof (cases "find (\<lambda>x. h M (FSM.initial S, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>h M (FSM.initial S, x). q'' \<in> nS0 \<union> set (map fst m))) (inputs_as_list M)")
        case None
        
  
        have "find_remove_2 (\<lambda> q' x . (h M) (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q',x) . (q'' \<in> nS0 \<union> set (map fst m)))) (nL) (inputs_as_list M) \<noteq> None"
          using \<open>q \<in> set nL\<close> \<open>h M (q,x) \<noteq> {}\<close> \<open>(\<forall> (y,q'') \<in> h M (q,x) . q'' \<in> (nS0 \<union> set (map fst m)))\<close> \<open>x \<in> set (inputs_as_list M)\<close>
          unfolding find_remove_2_None_iff \<open>nL = n # nL''\<close>
          by blast 
        then obtain q' x' nL' where *: "find_remove_2 (\<lambda> q' x . (h M) (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q',x) . (q'' \<in> nS0 \<union> set (map fst m)))) (n#nL'') (inputs_as_list M) = Some (q',x',nL')"
          unfolding \<open>nL = n # nL''\<close> by auto
        have "k = length nL'"
          using find_remove_2_length[OF *] \<open>Suc k = length nL\<close>  \<open>nL = n # nL''\<close> by simp
  
        have **: "select_inputs (h M) (initial S) (inputs_as_list M) nL (nS0 \<union> set (map fst m)) m
                  = select_inputs (h M) (initial S) (inputs_as_list M) nL' (nS0 \<union> set (map fst (m@[(q',x')]))) (m@[(q',x')])"
          unfolding \<open>nL = n # nL''\<close> select_inputs.simps None * by auto
  
        have p1: "(\<And>q. q \<in> reachable_states S \<Longrightarrow> deadlock_state S q \<Longrightarrow> q \<in> nS0 \<union> set (map fst (m@[(q',x')])))"
          using Suc.prems(1) by fastforce
  
        have "set nL = insert q' (set nL')" using find_remove_2_set(2,6)[OF *] unfolding \<open>nL = n # nL''\<close> by auto
        then have "(set nL \<union> set (map fst m)) = (set nL' \<union> set (map fst (m @ [(q', x')])))" by auto
        then have p2: "states M = insert (initial S) (set nL' \<union> nS0 \<union> set (map fst (m @ [(q', x')])))" 
          using Suc.prems(2) by auto
  
        have p3: "initial S \<notin> set nL' \<union> nS0 \<union> set (map fst (m @ [(q', x')]))"
          using Suc.prems(3) False \<open>set nL = insert q' (set nL')\<close> by auto
  
        show ?thesis unfolding **
          using Suc.hyps(1)[OF \<open>k = length nL'\<close> p1 p2 p3] by blast
      next
        case (Some a)
        then show ?thesis unfolding \<open>nL = n # nL''\<close> by auto
      qed
    qed
  qed
  then show "fst (last (select_inputs (h M) (initial S) (inputs_as_list M) nL (nS0 \<union> set (map fst m)) m)) = (initial S)"
       and  "length (select_inputs (h M) (initial S) (inputs_as_list M) nL (nS0 \<union> set (map fst m)) m) > 0"
    by blast+
qed


end