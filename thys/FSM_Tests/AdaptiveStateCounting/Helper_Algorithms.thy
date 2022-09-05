section \<open>Helper Algorithms\<close>

text \<open>This theory contains several algorithms used to calculate components of a test suite.\<close>   

theory Helper_Algorithms
imports State_Separator State_Preamble
begin

subsection \<open>Calculating r-distinguishable State Pairs with Separators\<close>

definition r_distinguishable_state_pairs_with_separators :: 
  "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> (('a \<times> 'a) \<times> (('a \<times> 'a) + 'a,'b,'c) fsm) set" 
  where
  "r_distinguishable_state_pairs_with_separators M = 
    {((q1,q2),Sep) | q1 q2 Sep . q1 \<in> states M 
                      \<and> q2 \<in> states M 
                      \<and> ((q1 < q2 \<and> state_separator_from_s_states M q1 q2 = Some Sep)
                        \<or> (q2 < q1 \<and> state_separator_from_s_states M q2 q1 = Some Sep)) }"

lemma r_distinguishable_state_pairs_with_separators_alt_def :
  "r_distinguishable_state_pairs_with_separators M = 
    \<Union> (image (\<lambda> ((q1,q2),A) . {((q1,q2),the A),((q2,q1),the A)}) 
              (Set.filter (\<lambda> (qq,A) . A \<noteq> None) 
                          (image (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                 (Set.filter (\<lambda> (q1,q2) . q1 < q2) (states M \<times> states M)))))"
  (is "?P1 = ?P2")
proof -
  have "\<And> x . x \<in> ?P1 \<Longrightarrow> x \<in> ?P2"
  proof -
    fix x assume "x \<in> ?P1"
    then obtain q1 q2 A where "x = ((q1,q2),A)"
      by (metis eq_snd_iff)
    then have "((q1,q2),A) \<in> ?P1" using \<open>x \<in> ?P1\<close> by auto
    then have "q1 \<in> states M"
         and  "q2 \<in> states M" 
         and  "((q1 < q2 \<and> state_separator_from_s_states M q1 q2 = Some A) 
                  \<or> (q2 < q1 \<and> state_separator_from_s_states M q2 q1 = Some A))"
      unfolding r_distinguishable_state_pairs_with_separators_def by blast+

    then consider (a) "q1 < q2 \<and> state_separator_from_s_states M q1 q2 = Some A" |
                  (b) "q2 < q1 \<and> state_separator_from_s_states M q2 q1 = Some A" 
      by blast
    then show "x \<in> ?P2" 
      using \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> unfolding \<open>x = ((q1,q2),A)\<close> by (cases; force)
  qed
  moreover have "\<And> x . x \<in> ?P2 \<Longrightarrow> x \<in> ?P1"
  proof -
    fix x assume "x \<in> ?P2"
    then obtain q1 q2 A where "x = ((q1,q2),A)"
      by (metis eq_snd_iff)
    then have "((q1,q2),A) \<in> ?P2" using \<open>x \<in> ?P2\<close> by auto
    then obtain q1' q2' A' where "((q1,q2),A) \<in> {((q1',q2'),the A'),((q2',q1'),the A')}"
                           and   "A' \<noteq> None"
                           and   "((q1',q2'), A') \<in> (image (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                                            (Set.filter (\<lambda> (q1,q2) . q1 < q2) (states M \<times> states M)))"
      by force
    
    then have "A' = Some A"
      by (metis (no_types, lifting) empty_iff insert_iff old.prod.inject option.collapse)  
    
    moreover have "A' = state_separator_from_s_states M q1' q2'"
             and  "q1' < q2'"
             and  "q1' \<in> states M"
             and  "q2' \<in> states M"
      using \<open>((q1',q2'), A') \<in> (image (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                      (Set.filter (\<lambda> (q1,q2) . q1 < q2) (states M \<times> states M)))\<close> 
      by force+
    ultimately have "state_separator_from_s_states M q1' q2' = Some A" by simp

    consider "((q1',q2'),the A') = ((q1,q2),A)" | "((q1',q2'),the A') = ((q2,q1),A)"
      using \<open>((q1,q2),A) \<in> {((q1',q2'),the A'),((q2',q1'),the A')}\<close>
      by force
    then show "x \<in> ?P1" 
    proof cases
      case 1
      then have *: "q1' = q1" and **: "q2' = q2" by auto

      show ?thesis 
        using \<open>q1' \<in> states M\<close> \<open>q2' \<in> states M\<close> \<open>q1' < q2'\<close> \<open>state_separator_from_s_states M q1' q2' = Some A\<close>
        unfolding r_distinguishable_state_pairs_with_separators_def
        unfolding * ** \<open>x = ((q1,q2),A)\<close> by blast
    next
      case 2
      then have *: "q1' = q2" and **: "q2' = q1" by auto

      show ?thesis 
        using \<open>q1' \<in> states M\<close> \<open>q2' \<in> states M\<close> \<open>q1' < q2'\<close> \<open>state_separator_from_s_states M q1' q2' = Some A\<close>
        unfolding r_distinguishable_state_pairs_with_separators_def
        unfolding * ** \<open>x = ((q1,q2),A)\<close> by blast
    qed
  qed
  ultimately show ?thesis by blast
qed


lemma r_distinguishable_state_pairs_with_separators_code[code] :
  "r_distinguishable_state_pairs_with_separators M = 
    set (concat (map 
                  (\<lambda> ((q1,q2),A) . [((q1,q2),the A),((q2,q1),the A)]) 
                  (filter (\<lambda> (qq,A) . A \<noteq> None) 
                          (map (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                               (filter (\<lambda> (q1,q2) . q1 < q2) 
                                       (List.product(states_as_list M) (states_as_list M)))))))"
  (is "r_distinguishable_state_pairs_with_separators M = ?C2")
proof -
  let ?C1 = "\<Union> (image (\<lambda> ((q1,q2),A) . {((q1,q2),the A),((q2,q1),the A)}) 
                       (Set.filter (\<lambda> (qq,A) . A \<noteq> None) 
                                   (image (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                          (Set.filter (\<lambda> (q1,q2) . q1 < q2) (states M \<times> states M)))))"

  have "r_distinguishable_state_pairs_with_separators M = ?C1"
    using r_distinguishable_state_pairs_with_separators_alt_def by assumption
  also have "\<dots> = ?C2"
  proof 
    show "?C1 \<subseteq> ?C2"
    proof 
      fix x assume "x \<in> ?C1"
      then obtain q1 q2 A where "x = ((q1,q2),A)"
        by (metis eq_snd_iff)
      then have "((q1,q2),A) \<in> ?C1" using \<open>x \<in> ?C1\<close> by auto
      then obtain q1' q2' A' where "((q1,q2),A) \<in> {((q1',q2'),the A'),((q2',q1'),the A')}"
                             and   "A' \<noteq> None"
                             and   "((q1',q2'), A') \<in> (image (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                                             (Set.filter (\<lambda> (q1,q2) . q1 < q2) (states M \<times> states M)))"
        by force
      
      then have "A' = Some A"
        by (metis (no_types, lifting) empty_iff insert_iff old.prod.inject option.collapse)  
      
      moreover have "A' = state_separator_from_s_states M q1' q2'"
               and  "q1' < q2'"
               and  "q1' \<in> states M"
               and  "q2' \<in> states M"
        using \<open>((q1',q2'), A') \<in> (image (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                        (Set.filter (\<lambda> (q1,q2) . q1 < q2) (states M \<times> states M)))\<close> 
        by force+
      ultimately have "state_separator_from_s_states M q1' q2' = Some A" 
                 and  "(q1',q2') \<in> set (filter (\<lambda> (q1,q2) . q1 < q2) (List.product(states_as_list M) (states_as_list M)))"
        unfolding states_as_list_set[symmetric] by auto

      then have "((q1',q2'),A') \<in> set (filter (\<lambda> (qq,A) . A \<noteq> None) 
                                              (map (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                                   (filter (\<lambda> (q1,q2) . q1 < q2) 
                                                           (List.product(states_as_list M) (states_as_list M)))))"
        using \<open>A' = state_separator_from_s_states M q1' q2'\<close> \<open>A' = Some A\<close> by force

      have scheme1: "\<And> f xs x . x \<in> set xs \<Longrightarrow> f x \<in> set (map f xs)" by auto
      have scheme2: "\<And> x xs xss . xs \<in> set xss \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> set (concat xss)" by auto
      have *:"[((q1',q2'),the A'),((q2',q1'),the A')] \<in> 
                set (map (\<lambda> ((q1,q2),A) . [((q1,q2),the A),((q2,q1),the A)]) 
                         (filter (\<lambda> (qq,A) . A \<noteq> None) 
                                 (map (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                      (filter (\<lambda> (q1,q2) . q1 < q2) 
                                              (List.product(states_as_list M) (states_as_list M))))))"
        using scheme1[OF \<open>((q1',q2'),A') \<in> set (filter (\<lambda> (qq,A) . A \<noteq> None) (map (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) (filter (\<lambda> (q1,q2) . q1 < q2) (List.product(states_as_list M) (states_as_list M)))))\<close>, of "\<lambda> ((q1', q2'), A') . [((q1',q2'),the A'),((q2',q1'),the A')]"] 
        by force
      have **: "((q1,q2),A) \<in> set [((q1',q2'),the A'),((q2',q1'),the A')]"
        using \<open>((q1,q2),A) \<in> {((q1',q2'),the A'),((q2',q1'),the A')}\<close> by auto
      
      show "x \<in> ?C2"
        unfolding \<open>x = ((q1,q2),A)\<close> using scheme2[OF * **] by assumption
    qed

    show "?C2 \<subseteq> ?C1"
    proof 
      fix x assume "x \<in> ?C2"
      obtain q1q2A where "x \<in>  set ((\<lambda> ((q1', q2'), A') . [((q1',q2'),the A'),((q2',q1'),the A')]) q1q2A)"
                   and   "q1q2A \<in> set (filter (\<lambda> (qq,A) . A \<noteq> None) 
                                              (map (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                                   (filter (\<lambda> (q1,q2) . q1 < q2) 
                                                           (List.product(states_as_list M) (states_as_list M)))))"
        using concat_map_elem[OF \<open>x \<in> ?C2\<close>] by blast

      moreover obtain q1 q2 A where "q1q2A = ((q1,q2),A)"
        by (metis prod.collapse)
        
      ultimately have "x \<in> set [((q1,q2),the A),((q2,q1),the A)]"
                 and  "((q1,q2),A) \<in> set (filter (\<lambda> (qq,A) . A \<noteq> None) 
                                                 (map (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                                      (filter (\<lambda> (q1,q2) . q1 < q2) 
                                                              (List.product(states_as_list M) (states_as_list M)))))"
        by force+

      then have "A = state_separator_from_s_states M q1 q2"
           and  "A \<noteq> None"
           and  "(q1,q2) \<in> set (filter (\<lambda> (q1,q2) . q1 < q2) (List.product(states_as_list M) (states_as_list M)))"
        by auto

      then have "q1 < q2" and "q1 \<in> states M" and "q2 \<in> states M"
        unfolding states_as_list_set[symmetric] by auto
      then have "(q1,q2) \<in> Set.filter (\<lambda>(q1, q2). q1 < q2) (FSM.states M \<times> FSM.states M)"
        by auto
      then have "((q1,q2),A) \<in> (Set.filter (\<lambda> (qq,A) . A \<noteq> None) 
                                           (image (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                                  (Set.filter (\<lambda> (q1,q2) . q1 < q2) (states M \<times> states M))))"
        using \<open>A \<noteq> None\<close> unfolding \<open>A = state_separator_from_s_states M q1 q2\<close> by auto
      then have "{((q1,q2),the A),((q2,q1),the A)} \<in> 
                      (image (\<lambda> ((q1,q2),A) . {((q1,q2),the A),((q2,q1),the A)}) 
                             (Set.filter (\<lambda> (qq,A) . A \<noteq> None) 
                                         (image (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) 
                                                (Set.filter (\<lambda> (q1,q2) . q1 < q2) (states M \<times> states M)))))"
        by (metis (no_types, lifting) \<open>q1q2A = ((q1, q2), A)\<close> case_prod_conv image_iff)
      then show "x \<in> ?C1"
        using \<open>x \<in> set [((q1,q2),the A),((q2,q1),the A)]\<close>
        by (metis (no_types, lifting) UnionI list.simps(15) set_empty2) 
    qed
  qed
         
  finally show ?thesis .
qed
  

lemma r_distinguishable_state_pairs_with_separators_same_pair_same_separator :
  assumes "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
  and     "((q1,q2),A') \<in> r_distinguishable_state_pairs_with_separators M"
shows "A = A'"
  using assms unfolding r_distinguishable_state_pairs_with_separators_def
  by force 


lemma r_distinguishable_state_pairs_with_separators_sym_pair_same_separator :
  assumes "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
  and     "((q2,q1),A') \<in> r_distinguishable_state_pairs_with_separators M"
shows "A = A'"
  using assms unfolding r_distinguishable_state_pairs_with_separators_def
  by force 


lemma r_distinguishable_state_pairs_with_separators_elem_is_separator:
  assumes "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
  and     "observable M"
  and     "completely_specified M"
shows "is_separator M q1 q2 A (Inr q1) (Inr q2)"
proof -
  have *:"q1 \<in> states M" 
  and **:"q2 \<in> states M" 
  and ***:"q1 \<noteq> q2" 
  and ****: "q2\<noteq>q1" 
  and *****: "state_separator_from_s_states M q1 q2 = Some A \<or> state_separator_from_s_states M q2 q1 = Some A"
    using assms(1) unfolding r_distinguishable_state_pairs_with_separators_def by auto

  from ***** have "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A 
                    \<or> is_state_separator_from_canonical_separator (canonical_separator M q2 q1) q2 q1 A"
    using state_separator_from_s_states_soundness[of M q1 q2 A, OF _ * ** assms(3)]
    using state_separator_from_s_states_soundness[of M q2 q1 A, OF _ ** * assms(3)] by auto
  then show ?thesis
    using state_separator_from_canonical_separator_is_separator[of M q1 q2 A, OF _ \<open>observable M\<close> * ** ***] 
    using state_separator_from_canonical_separator_is_separator[of M q2 q1 A, OF _ \<open>observable M\<close> ** * ****] 
    using is_separator_sym[of M q2 q1 A "Inr q2" "Inr q1"] by auto
qed




subsection \<open>Calculating Pairwise r-distinguishable Sets of States\<close>


definition pairwise_r_distinguishable_state_sets_from_separators :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a set set" where
  "pairwise_r_distinguishable_state_sets_from_separators M 
    = { S . S \<subseteq> states M \<and> (\<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> image fst (r_distinguishable_state_pairs_with_separators M))}" 

definition pairwise_r_distinguishable_state_sets_from_separators_list :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a set list" where
  "pairwise_r_distinguishable_state_sets_from_separators_list M = 
    (let RDS = image fst (r_distinguishable_state_pairs_with_separators M)
      in filter (\<lambda> S . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> RDS) 
             (map set (pow_list (states_as_list M))))"

(* uses a list-based calculation to avoid storing the entire powerset *)
lemma pairwise_r_distinguishable_state_sets_from_separators_code[code] :
  "pairwise_r_distinguishable_state_sets_from_separators M = set (pairwise_r_distinguishable_state_sets_from_separators_list M)"
  using pow_list_set[of "states_as_list M"]
  unfolding states_as_list_set[of M] 
            pairwise_r_distinguishable_state_sets_from_separators_def 
            pairwise_r_distinguishable_state_sets_from_separators_list_def 
  by auto


lemma pairwise_r_distinguishable_state_sets_from_separators_cover :
  assumes "q \<in> states M"
  shows "\<exists> S \<in> (pairwise_r_distinguishable_state_sets_from_separators M) . q \<in> S"
  unfolding pairwise_r_distinguishable_state_sets_from_separators_def using assms by blast



definition maximal_pairwise_r_distinguishable_state_sets_from_separators :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a set set" where
  "maximal_pairwise_r_distinguishable_state_sets_from_separators M 
    = { S . S \<in> (pairwise_r_distinguishable_state_sets_from_separators M) 
            \<and> (\<nexists> S' . S' \<in> (pairwise_r_distinguishable_state_sets_from_separators M) \<and> S \<subset> S')}"


definition maximal_pairwise_r_distinguishable_state_sets_from_separators_list :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a set list" where
  "maximal_pairwise_r_distinguishable_state_sets_from_separators_list M = 
    remove_subsets (pairwise_r_distinguishable_state_sets_from_separators_list M)"
      


lemma maximal_pairwise_r_distinguishable_state_sets_from_separators_code[code] :
  "maximal_pairwise_r_distinguishable_state_sets_from_separators M 
    = set (maximal_pairwise_r_distinguishable_state_sets_from_separators_list M)"
  unfolding maximal_pairwise_r_distinguishable_state_sets_from_separators_list_def 
            Let_def remove_subsets_set pairwise_r_distinguishable_state_sets_from_separators_code[symmetric] 
            maximal_pairwise_r_distinguishable_state_sets_from_separators_def 
  by blast


lemma maximal_pairwise_r_distinguishable_state_sets_from_separators_cover :
  assumes "q \<in> states M"
  shows "\<exists> S \<in> (maximal_pairwise_r_distinguishable_state_sets_from_separators M ). q \<in> S"
proof -

  have *: "{q} \<in> (pairwise_r_distinguishable_state_sets_from_separators M)"
    unfolding pairwise_r_distinguishable_state_sets_from_separators_def using assms by blast
  have **: "finite (pairwise_r_distinguishable_state_sets_from_separators M)"
    unfolding pairwise_r_distinguishable_state_sets_from_separators_def by (simp add: fsm_states_finite) 

  have "(maximal_pairwise_r_distinguishable_state_sets_from_separators M) = 
        {S \<in> (pairwise_r_distinguishable_state_sets_from_separators M). 
            \<not>(\<exists> S' \<in> (pairwise_r_distinguishable_state_sets_from_separators M) . S \<subset> S')}"
    unfolding maximal_pairwise_r_distinguishable_state_sets_from_separators_def  
              pairwise_r_distinguishable_state_sets_from_separators_def 
    by metis
  then have "(maximal_pairwise_r_distinguishable_state_sets_from_separators M) = 
        {S \<in> (pairwise_r_distinguishable_state_sets_from_separators M) . 
              (\<forall> S' \<in> (pairwise_r_distinguishable_state_sets_from_separators M) . \<not> S \<subset> S')}"
    by blast 
  moreover have "\<exists> S \<in> {S \<in> (pairwise_r_distinguishable_state_sets_from_separators M) . 
                      (\<forall> S' \<in> (pairwise_r_distinguishable_state_sets_from_separators M) . \<not> S \<subset> S')} . q \<in> S"
    using maximal_set_cover[OF ** *] 
    by blast
  ultimately show ?thesis 
    by blast 
qed





subsection \<open>Calculating d-reachable States with Preambles\<close>



(* calculate d-reachable states and a fixed assignment of preambles *)
definition d_reachable_states_with_preambles :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> ('a \<times> ('a,'b,'c) fsm) set" where
  "d_reachable_states_with_preambles M = 
    image (\<lambda> qp . (fst qp, the (snd qp))) 
          (Set.filter (\<lambda> qp . snd qp \<noteq> None) 
                      (image (\<lambda> q . (q, calculate_state_preamble_from_input_choices M q)) 
                             (states M)))"


lemma d_reachable_states_with_preambles_exhaustiveness :
  assumes "\<exists> P . is_preamble P M q"
  and     "q \<in> states M"
shows "\<exists> P . (q,P) \<in> (d_reachable_states_with_preambles M)"
  using calculate_state_preamble_from_input_choices_exhaustiveness[OF assms(1)] assms(2)
  unfolding d_reachable_states_with_preambles_def by force


lemma d_reachable_states_with_preambles_soundness :
  assumes "(q,P) \<in> (d_reachable_states_with_preambles M)"
  and     "observable M"
  shows "is_preamble P M q"
    and "q \<in> states M"
  using assms(1) calculate_state_preamble_from_input_choices_soundness[of M q P]
  unfolding d_reachable_states_with_preambles_def
  using imageE by auto


subsection \<open>Calculating Repetition Sets\<close>

text \<open>Repetition sets are sets of tuples each containing a maximal set of pairwise r-distinguishable 
      states and the subset of those states that have a preamble.\<close> 

definition maximal_repetition_sets_from_separators :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> ('a set \<times> 'a set) set" where
  "maximal_repetition_sets_from_separators M 
    = {(S, S \<inter> (image fst (d_reachable_states_with_preambles M))) | S . 
            S \<in> (maximal_pairwise_r_distinguishable_state_sets_from_separators M)}"

definition maximal_repetition_sets_from_separators_list_naive :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> ('a set \<times> 'a set) list" where
  "maximal_repetition_sets_from_separators_list_naive M 
    = (let DR = (image fst (d_reachable_states_with_preambles M))
        in map (\<lambda> S . (S, S \<inter> DR)) (maximal_pairwise_r_distinguishable_state_sets_from_separators_list M))"


lemma maximal_repetition_sets_from_separators_code[code]: 
  "maximal_repetition_sets_from_separators M = (let DR = (image fst (d_reachable_states_with_preambles M))
    in  image (\<lambda> S . (S, S \<inter> DR)) (maximal_pairwise_r_distinguishable_state_sets_from_separators M))" 
  unfolding maximal_repetition_sets_from_separators_def Let_def by force

lemma maximal_repetition_sets_from_separators_code_alt: 
  "maximal_repetition_sets_from_separators M = set (maximal_repetition_sets_from_separators_list_naive M)" 
  unfolding maximal_repetition_sets_from_separators_def 
            maximal_repetition_sets_from_separators_list_naive_def 
            maximal_pairwise_r_distinguishable_state_sets_from_separators_code 
  by force



subsubsection \<open>Calculating Sub-Optimal Repetition Sets\<close>

text \<open>Finding maximal pairwise r-distinguishable subsets of the state set of some FSM is likely too expensive
      for FSMs containing a large number of r-distinguishable pairs of states.
      The following functions calculate only subset of all repetition sets while maintaining the
      property that every state is contained in some repetition set.\<close>

fun extend_until_conflict :: "('a \<times> 'a) set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "extend_until_conflict non_confl_set candidates xs 0 = xs" |
  "extend_until_conflict non_confl_set candidates xs (Suc k) = (case dropWhile (\<lambda> x . find (\<lambda> y . (x,y) \<notin> non_confl_set) xs \<noteq> None) candidates of
    [] \<Rightarrow> xs |
    (c#cs) \<Rightarrow> extend_until_conflict non_confl_set cs (c#xs) k)"


lemma extend_until_conflict_retainment :
  assumes "x \<in> set xs"
  shows "x \<in> set (extend_until_conflict non_confl_set candidates xs k)" 
using assms proof (induction k arbitrary: candidates xs)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case proof (cases "dropWhile (\<lambda> x . find (\<lambda> y . (x,y) \<notin> non_confl_set) xs \<noteq> None) candidates")
    case Nil
    then show ?thesis
      by (metis Suc.prems extend_until_conflict.simps(2) list.simps(4)) 
  next
    case (Cons c cs)
    then show ?thesis
      by (simp add: Suc.IH Suc.prems) 
  qed
qed

lemma extend_until_conflict_elem :
  assumes "x \<in> set (extend_until_conflict non_confl_set candidates xs k)"
  shows "x \<in> set xs \<or> x \<in> set candidates"
using assms proof (induction k arbitrary: candidates xs)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case proof (cases "dropWhile (\<lambda> x . find (\<lambda> y . (x,y) \<notin> non_confl_set) xs \<noteq> None) candidates")
    case Nil
    then show ?thesis 
      by (metis Suc.prems extend_until_conflict.simps(2) list.simps(4)) 
  next
    case (Cons c cs)
    then have "extend_until_conflict non_confl_set candidates xs (Suc k) = extend_until_conflict non_confl_set cs (c#xs) k"
      by auto
    then have "x \<in> set (c # xs) \<or> x \<in> set cs"
      using Suc.IH[of cs "(c#xs)"] Suc.prems by auto
    moreover have "set (c#cs) \<subseteq> set candidates"
      using Cons by (metis set_dropWhileD subsetI) 
    ultimately show ?thesis
      using set_ConsD by auto 
  qed
qed


lemma extend_until_conflict_no_conflicts :
  assumes "x \<in> set (extend_until_conflict non_confl_set candidates xs k)"
  and     "y \<in> set (extend_until_conflict non_confl_set candidates xs k)"
  and     "x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> (x,y) \<in> non_confl_set \<or> (y,x) \<in> non_confl_set"  
  and     "x \<noteq> y"  
shows "(x,y) \<in> non_confl_set \<or> (y,x) \<in> non_confl_set" 
using assms proof (induction k arbitrary: candidates xs)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case proof (cases "dropWhile (\<lambda> x . find (\<lambda> y . (x,y) \<notin> non_confl_set) xs \<noteq> None) candidates")
    case Nil
    then have "extend_until_conflict non_confl_set candidates xs (Suc k) = xs"
      by (metis extend_until_conflict.simps(2) list.simps(4)) 
    then show ?thesis 
      using Suc.prems by auto
  next
    case (Cons c cs)
    then have "extend_until_conflict non_confl_set candidates xs (Suc k) = extend_until_conflict non_confl_set cs (c#xs) k"
      by auto
    then have xk: "x \<in> set (extend_until_conflict non_confl_set cs (c#xs) k)"
         and  yk: "y \<in> set (extend_until_conflict non_confl_set cs (c#xs) k)"
      using Suc.prems by auto

    have **: "x \<in> set (c#xs) \<Longrightarrow> y \<in> set (c#xs) \<Longrightarrow> (x,y) \<in> non_confl_set \<or> (y,x) \<in> non_confl_set"
    proof -
      have scheme: "\<And> P xs x xs' . dropWhile P xs = (x#xs') \<Longrightarrow> \<not> P x"
        by (simp add: dropWhile_eq_Cons_conv) 
      have "find (\<lambda> y . (c,y) \<notin> non_confl_set) xs = None" 
        using scheme[OF Cons] by simp
      then have *: "\<And> y . y \<in> set xs \<Longrightarrow> (c,y) \<in> non_confl_set"
        unfolding find_None_iff by blast

      assume "x \<in> set (c#xs)" and "y \<in> set (c#xs)"
      then consider (a1) "x = c \<and> y \<in> set xs" |
                    (a2) "y = c \<and> x \<in> set xs" |
                    (a3) "x \<in> set xs \<and> y \<in> set xs" 
        using \<open>x \<noteq> y\<close> by auto
      then show ?thesis 
        using * Suc.prems(3) by (cases; auto)
    qed

    show ?thesis using Suc.IH[OF xk yk ** Suc.prems(4)] by blast
  qed
qed


definition greedy_pairwise_r_distinguishable_state_sets_from_separators :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a set list" where
  "greedy_pairwise_r_distinguishable_state_sets_from_separators M = 
    (let pwrds = image fst (r_distinguishable_state_pairs_with_separators M);
         k     = size M;
         nL    = states_as_list M
     in map (\<lambda>q . set (extend_until_conflict pwrds (remove1 q nL) [q] k)) nL)"

definition maximal_repetition_sets_from_separators_list_greedy :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> ('a set \<times> 'a set) list" where
  "maximal_repetition_sets_from_separators_list_greedy M = (let DR = (image fst (d_reachable_states_with_preambles M))
    in remdups (map (\<lambda> S . (S, S \<inter> DR)) (greedy_pairwise_r_distinguishable_state_sets_from_separators M)))"



lemma greedy_pairwise_r_distinguishable_state_sets_from_separators_cover :
  assumes "q \<in> states M"
shows "\<exists> S \<in> set (greedy_pairwise_r_distinguishable_state_sets_from_separators M). q \<in> S"
  using assms extend_until_conflict_retainment[of q "[q]"]
  unfolding states_as_list_set[symmetric] greedy_pairwise_r_distinguishable_state_sets_from_separators_def Let_def
  by auto

lemma r_distinguishable_state_pairs_with_separators_sym :
  assumes "(q1,q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
  shows "(q2,q1) \<in> fst ` r_distinguishable_state_pairs_with_separators M" 
  using assms 
  unfolding r_distinguishable_state_pairs_with_separators_def 
  by force


lemma greedy_pairwise_r_distinguishable_state_sets_from_separators_soundness :
  "set (greedy_pairwise_r_distinguishable_state_sets_from_separators M) \<subseteq> (pairwise_r_distinguishable_state_sets_from_separators M)"
proof 
  fix S assume "S \<in> set (greedy_pairwise_r_distinguishable_state_sets_from_separators M)"
  then obtain q' where "q' \<in> states M"
                 and   *: "S = set (extend_until_conflict (image fst (r_distinguishable_state_pairs_with_separators M)) 
                                                          (remove1 q' (states_as_list M)) 
                                                          [q'] 
                                                          (size M))"
    unfolding greedy_pairwise_r_distinguishable_state_sets_from_separators_def Let_def states_as_list_set[symmetric] 
    by auto


  have "S \<subseteq> states M"
  proof 
    fix q assume "q \<in> S"
    then have "q \<in> set (extend_until_conflict (image fst (r_distinguishable_state_pairs_with_separators M)) (remove1 q' (states_as_list M)) [q'] (size M))"
      using * by auto
    then show "q \<in> states M"
      using extend_until_conflict_elem[of q "image fst (r_distinguishable_state_pairs_with_separators M)" "(remove1 q' (states_as_list M))" "[q']" "size M"]
      using states_as_list_set \<open>q' \<in> states M\<close> by auto
  qed

  moreover have "\<And> q1 q2 . q1 \<in> S \<Longrightarrow> q2 \<in> S \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1,q2) \<in> image fst (r_distinguishable_state_pairs_with_separators M)"  
  proof -
    fix q1 q2 assume "q1 \<in> S" and "q2 \<in> S" and "q1 \<noteq> q2"
    then have e1: "q1 \<in> set (extend_until_conflict (image fst (r_distinguishable_state_pairs_with_separators M)) (remove1 q' (states_as_list M)) [q'] (size M))"
         and  e2: "q2 \<in> set (extend_until_conflict (image fst (r_distinguishable_state_pairs_with_separators M)) (remove1 q' (states_as_list M)) [q'] (size M))"
      unfolding * by simp+
    have e3: "(q1 \<in> set [q'] \<Longrightarrow> q2 \<in> set [q'] 
              \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M 
                  \<or> (q2, q1) \<in> fst ` r_distinguishable_state_pairs_with_separators M)"
      using \<open>q1 \<noteq> q2\<close> by auto

    show "(q1,q2) \<in> image fst (r_distinguishable_state_pairs_with_separators M)"
      using extend_until_conflict_no_conflicts[OF e1 e2 e3 \<open>q1 \<noteq> q2\<close>]
            r_distinguishable_state_pairs_with_separators_sym[of q2 q1 M] by blast
  qed

  ultimately show "S \<in> (pairwise_r_distinguishable_state_sets_from_separators M)"
    unfolding pairwise_r_distinguishable_state_sets_from_separators_def by blast
qed


end