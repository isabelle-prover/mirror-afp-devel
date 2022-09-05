section \<open>R-Distinguishability\<close>

text \<open>This theory defines the notion of r-distinguishability and relates it to state separators.\<close>


theory R_Distinguishability
imports State_Separator
begin


definition r_compatible :: "('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  "r_compatible M q1 q2 = ((\<exists> S . completely_specified S \<and> is_submachine S (product (from_FSM M q1) (from_FSM M q2))))"

abbreviation(input) "r_distinguishable M q1 q2 \<equiv> \<not> r_compatible M q1 q2"

(* Note: If an input is not defined on states q and q', then they are r(0)-distinguishable (r_distinguishable_k M q1 q2 0).
         In particular, any state with some undefined input is r-distinguishable from itself 
         This behaviour is justified by the assumption that tested FSMs are completely specified.
*)

fun r_distinguishable_k :: "('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> (inputs M) . \<not> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> (inputs M) . \<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k))"



subsection \<open>R(k)-Distinguishability Properties\<close>


lemma r_distinguishable_k_0_alt_def : 
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> (inputs M) . \<not>(\<exists> y q1' q2' . (q1,x,y,q1') \<in> transitions M \<and> (q2,x,y,q2') \<in> transitions M))"
  by fastforce 

lemma r_distinguishable_k_Suc_k_alt_def :
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> (inputs M) . \<forall> y q1' q2' . ((q1,x,y,q1') \<in> transitions M \<and> (q2,x,y,q2') \<in> transitions M) \<longrightarrow> r_distinguishable_k M q1' q2' k))" 
  by fastforce

lemma r_distinguishable_k_by_larger :
  assumes "r_distinguishable_k M q1 q2 k"
      and "k \<le> k'"
    shows "r_distinguishable_k M q1 q2 k'"
  using assms nat_induct_at_least by fastforce


lemma r_distinguishable_k_0_not_completely_specified :
  assumes "r_distinguishable_k M q1 q2 0"
      and "q1 \<in> states M"
      and "q2 \<in> states M"
  shows "\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2)))"
proof -
  let ?F1 = "from_FSM M q1"
  let ?F2 = "from_FSM M q2"
  let ?P = "product ?F1 ?F2"

  obtain x where "x \<in> (inputs M)" 
             and "\<not> (\<exists> t1 t2 . t1 \<in> transitions M \<and> t2 \<in> transitions M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"  
    using assms(1) by fastforce

  then have *: "\<not> (\<exists> t1 t2 . t1 \<in> transitions ?F1 \<and> t2 \<in> transitions ?F2 \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
    unfolding from_FSM_simps[OF assms(2)] from_FSM_simps[OF assms(3)] by simp
  
  have **: "\<not> (\<exists> t \<in> transitions ?P . t_source t = (q1,q2) \<and> t_input t = x)"
  proof (rule ccontr)  
    assume "\<not> \<not> (\<exists>t\<in> transitions (product (from_FSM M q1) (from_FSM M q2)). t_source t = (q1, q2) \<and> t_input t = x)"
    then obtain t where "t \<in> transitions ?P" and "t_source t = (q1,q2)" and "t_input t = x"
      by blast 

    have "\<exists> t1 t2 . t1 \<in> transitions ?F1 \<and> t2 \<in> transitions ?F2 \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
      using product_transition_split[OF \<open>t \<in> transitions ?P\<close>]
      by (metis \<open>t_input t = x\<close> \<open>t_source t = (q1, q2)\<close> fst_conv snd_conv)
    then show "False" 
      using * by auto
  qed

  moreover have "x \<in> (inputs ?P)"
    using \<open>x \<in> (inputs M)\<close>
    by (simp add: assms(3)) 

  ultimately have "\<not> completely_specified_state ?P (q1,q2)"
    by (meson completely_specified_state.elims(2))
    

  have "(q1,q2) = initial (product (from_FSM M q1) (from_FSM M q2))"
    by (simp add: assms(2) assms(3))

  then show ?thesis
    using \<open>\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (q1, q2)\<close> by presburger
qed



lemma r_0_distinguishable_from_not_completely_specified_initial :
  assumes "\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (q1,q2)"
      and "q1 \<in> states M"
      and "q2 \<in> states M"
  shows "r_distinguishable_k M q1 q2 0"
proof -
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"

  from assms obtain x where "x \<in> (inputs ?P)"
                      and "\<not> (\<exists>t\<in> transitions ?P. t_source t = (q1, q2) \<and> t_input t = x)" 
        unfolding completely_specified_state.simps by blast

  then have "x \<in> (inputs M)"
    by (simp add: assms(2) assms(3))

  have *: "\<not> (\<exists> t1 t2.
                t1 \<in> transitions (from_FSM M q1) \<and>
                t2 \<in> transitions (from_FSM M q2) \<and>
                t_source t1 = q1 \<and>
                t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
  proof

    assume "\<exists>t1 t2.
       t1 \<in> transitions (from_FSM M q1) \<and>
       t2 \<in> transitions (from_FSM M q2) \<and>
       t_source t1 = q1 \<and>
       t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
    then obtain t1 t2 where "t1 \<in> transitions (from_FSM M q1)" 
                        and "t2 \<in> transitions (from_FSM M q2)"
                        and "t_source t1 = q1"
                        and "t_source t2 = q2" 
                        and "t_input t1 = x" 
                        and "t_input t2 = x" 
                        and "t_output t1 = t_output t2"
      by blast

    let ?t = "((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2))"
    let ?t1 = "(fst (t_source ?t), t_input ?t, t_output ?t, fst (t_target ?t))"
    let ?t2 = "(snd (t_source ?t), t_input ?t, t_output ?t, snd (t_target ?t))"

    have t1_alt : "t1 = ?t1"
      by auto
    have "t_source t2 = snd (t_source ?t)"
      by auto
    moreover have "t_input t2 = t_input ?t"
      using \<open>t_input t1 = x\<close> \<open>t_input t2 = x\<close> by auto
    moreover have "t_output t2 = t_output ?t"
      using \<open>t_output t1 = t_output t2\<close> by auto
    moreover have "t_target t2 = snd (t_target ?t)"
      by auto
    ultimately have "(t_source t2, t_input t2, t_output t2, t_target t2) = ?t2"
      by auto
    then have t2_alt : "t2 = ?t2"
      by auto
        
    have "?t1 \<in> transitions (from_FSM M q1)"
      using \<open>t1 \<in> transitions (from_FSM M q1)\<close> by auto
    moreover have "?t2 \<in> transitions (from_FSM M q2)"
      using \<open>t2 \<in> transitions (from_FSM M q2)\<close> t2_alt by auto

    ultimately have "?t \<in> transitions ?P"
      unfolding product_transitions_def by force
    moreover have "t_source ?t = (q1,q2)" using \<open>t_source t1 = q1\<close> \<open>t_source t2 = q2\<close> by auto
    moreover have "t_input ?t = x" using \<open>t_input t1 = x\<close> by auto
    ultimately show "False"
      using \<open>\<not> (\<exists>t\<in> transitions ?P. t_source t = (q1, q2) \<and> t_input t = x)\<close> by blast
  qed

  have **:  "\<And>t1 . t1 \<in> transitions M \<Longrightarrow> t_source t1 = q1 \<Longrightarrow> t1 \<in> transitions (from_FSM M q1)"
   and ***: "\<And>t2 . t2 \<in> transitions M \<Longrightarrow> t_source t2 = q2 \<Longrightarrow> t2 \<in> transitions (from_FSM M q2)"
    by (simp add: assms(2,3))+
    

  then show ?thesis unfolding r_distinguishable_k.simps
    using \<open>x \<in> (inputs M)\<close> * by blast
qed          


lemma r_0_distinguishable_from_not_completely_specified :
  assumes "\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (q1',q2')"
      and "q1 \<in> states M"
      and "q2 \<in> states M"
      and "(q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2))"
    shows "r_distinguishable_k M q1' q2' 0"
proof -
  have "q1' \<in> states M"
    using assms(2) assms(4) by simp
  have "q2' \<in> states M"
    using assms(3) assms(4) by simp
  show ?thesis
    using r_0_distinguishable_from_not_completely_specified_initial[OF _ \<open>q1' \<in> states M\<close> \<open>q2' \<in> states M\<close>]
          assms(1)
    unfolding completely_specified_state.simps product_simps from_FSM_simps[OF assms(2)] from_FSM_simps[OF assms(3)] from_FSM_simps[OF \<open>q1' \<in> states M\<close>] from_FSM_simps[OF \<open>q2' \<in> states M\<close>]
              product_transitions_alt_def by auto
qed
               

lemma r_distinguishable_k_intersection_path : 
  assumes "\<not> r_distinguishable_k M q1 q2 k"
  and "length xs \<le> Suc k"
  and "set xs \<subseteq> (inputs M)"
  and "q1 \<in> states M"
  and "q2 \<in> states M"
shows "\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs"
using assms proof (induction k arbitrary: q1 q2 xs)
  case 0
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  show ?case
  proof (cases "length xs < Suc 0")
    case True
    then have "xs = []" by auto
    moreover have "path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) []"
      by (simp add: "0.prems"(4) "0.prems"(5) nil)
    moreover have "map fst (p_io []) = []" by auto
    ultimately show ?thesis
      by simp 
  next
    case False
    
    have "completely_specified_state ?P (q1,q2)"
    proof (rule ccontr)
      assume "\<not> completely_specified_state ?P (q1,q2)"
      then have "r_distinguishable_k M q1 q2 0"
        using r_0_distinguishable_from_not_completely_specified_initial
        by (metis "0.prems"(4) "0.prems"(5)) 
      then show "False"
        using "0.prems" by simp
    qed
    then have *: "\<forall> x \<in> (inputs ?P) . \<exists> t . t \<in> transitions ?P \<and> t_source t = (q1,q2) \<and> t_input t = x"
      unfolding completely_specified_state.simps by blast

    let ?x = "hd xs"
    have "xs = [?x]"
      using "0.prems"(2) False
      by (metis Suc_length_conv le_neq_implies_less length_0_conv list.sel(1))
    
    have "?x \<in> (inputs M)"
      using "0.prems"(3) False by auto
    then obtain t where "t \<in> transitions ?P" and "t_source t = (q1,q2)" and "t_input t = ?x"
      using "*" "0.prems"(4) "0.prems"(5) by auto

    then have "path ?P (q1,q2) [t]" 
      using single_transition_path by metis
    moreover have "map fst (p_io [t]) = xs"
      using \<open>t_input t = ?x\<close> \<open>xs = [hd xs]\<close> by auto
    ultimately show ?thesis
      by (metis (no_types, lifting)) 
  qed
next
  case (Suc k)
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  
  show ?case 
  proof (cases "length xs \<le> Suc k")
    case True
    have "\<not> r_distinguishable_k M q1 q2 k" 
      using Suc.prems(1) by auto
    show ?thesis 
      using Suc.IH[OF \<open>\<not> r_distinguishable_k M q1 q2 k\<close> True Suc.prems(3,4,5)] by assumption
  next
    case False
    then have "length xs = Suc (Suc k)"
      using Suc.prems(2) by auto
    
    then have "hd xs \<in> (inputs M)"
      by (metis Suc.prems(3) contra_subsetD hd_in_set length_greater_0_conv zero_less_Suc) 
    have "set (tl xs) \<subseteq> (inputs M)"
      by (metis \<open>length xs = Suc (Suc k)\<close> Suc.prems(3) dual_order.trans hd_Cons_tl length_0_conv nat.simps(3) set_subset_Cons)
    have "length (tl xs) \<le> Suc k"
      by (simp add: \<open>length xs = Suc (Suc k)\<close>) 

    let ?x = "hd xs"
    let ?xs = "tl xs"

    have "\<forall> x \<in> (inputs M) . \<exists> t \<in> transitions ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
    proof 
      fix x assume "x \<in> (inputs M)"
  
      have "\<not>(\<exists> x \<in> (inputs M) . \<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)"
        using Suc.prems by auto
      then have "\<forall> x \<in> (inputs M) . \<exists> t1 t2 . (t1 \<in> transitions M \<and> t2 \<in> transitions M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> \<not> r_distinguishable_k M (t_target t1) (t_target t2) k)"
        by blast
      then obtain t1 t2 where "t1 \<in> transitions M"
                          and "t2 \<in> transitions M"  
                          and "t_source t1 = q1" 
                          and "t_source t2 = q2"  
                          and "t_input t1 = x" 
                          and "t_input t2 = x" 
                          and p4: "t_output t1 = t_output t2" 
                          and **: "\<not> r_distinguishable_k M (t_target t1) (t_target t2) k"
        using \<open>x \<in> (inputs M)\<close> by auto

      have p1: "t1 \<in> transitions (from_FSM M q1)"
        by (simp add: Suc.prems(4) \<open>t1 \<in> FSM.transitions M\<close>) 
      have p2: "t2 \<in> transitions (from_FSM M q2)"
        by (simp add: Suc.prems(5) \<open>t2 \<in> FSM.transitions M\<close>) 
      have p3: "t_input t1 = t_input t2"
        using \<open>t_input t1 = x\<close> \<open>t_input t2 = x\<close> by auto
      
      have ***: "((q1,q2), x, t_output t1, (t_target t1, t_target t2)) \<in> transitions ?P"
        using \<open>t_source t1 = q1\<close> \<open>t_source t2 = q2\<close> \<open>t_input t1 = x\<close> p1 p2 p3 p4
        unfolding product_transitions_alt_def
        by blast
      
      show "\<exists> t \<in> transitions ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
        by (metis "**" "***" fst_conv snd_conv)
    qed

    then obtain t where "t \<in> transitions ?P" and "t_source t = (q1,q2)" and "t_input t = ?x" 
                    and "\<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
      using \<open>?x \<in> (inputs M)\<close> by blast 

    have "fst (t_target t) \<in> FSM.states M" and "snd (t_target t) \<in> FSM.states M"
      using fsm_transition_target[OF \<open>t \<in> transitions ?P\<close>] unfolding product_simps from_FSM_simps[OF \<open>q1 \<in> states M\<close>] from_FSM_simps[OF \<open>q2 \<in> states M\<close>] by auto

    then obtain p where p_def: "path (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t)))) (t_target t) p" 
               and "map fst (p_io p) = ?xs"
      using Suc.IH[OF \<open>\<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k\<close> \<open>length (tl xs) \<le> Suc k\<close> \<open>set (tl xs) \<subseteq> (inputs M)\<close>] by auto
    
    have "path ?P (t_target t) p" 
      using product_from_path_previous[OF p_def \<open>t \<in> transitions ?P\<close> Suc.prems(4,5)]  by assumption

    have "path ?P (q1,q2) (t#p)"
      using path.cons[OF\<open>t \<in> transitions ?P\<close> \<open>path ?P (t_target t) p\<close>] \<open>t_source t = (q1,q2)\<close> by metis
    moreover have "map fst (p_io (t#p)) = xs"
      using \<open>t_input t = ?x\<close> \<open>map fst (p_io p) = ?xs\<close>
      by (metis (no_types, lifting) \<open>length xs = Suc (Suc k)\<close> \<open>t_input t = hd xs\<close> fst_conv hd_Cons_tl length_greater_0_conv list.simps(9) zero_less_Suc)
    ultimately show ?thesis
      by (metis (no_types, lifting)) 
  qed
qed


lemma r_distinguishable_k_intersection_paths : 
  assumes "\<not>(\<exists> k . r_distinguishable_k M q1 q2 k)"
  and "q1 \<in> states M"
  and "q2 \<in> states M"
  shows "\<forall> xs . set xs \<subseteq> (inputs M) \<longrightarrow> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs)"
proof (rule ccontr)
  assume "\<not> (\<forall> xs . set xs \<subseteq> (inputs M) \<longrightarrow> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs))"
  then obtain xs where "set xs \<subseteq> (inputs M)"
                   and "\<not> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs)" 
    by blast

  have "\<not> r_distinguishable_k M q1 q2 (length xs)"
    using assms by auto

  show "False" 
    using r_distinguishable_k_intersection_path[OF \<open>\<not> r_distinguishable_k M q1 q2 (length xs)\<close> _ \<open>set xs \<subseteq> (inputs M)\<close> assms(2,3)]
          \<open>\<not> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs)\<close> by fastforce
qed




subsubsection \<open>Equivalence of R-Distinguishability Definitions\<close>


lemma r_distinguishable_alt_def :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
  shows "r_distinguishable M q1 q2 \<longleftrightarrow> (\<exists> k . r_distinguishable_k M q1 q2 k)"
proof 
  show "r_distinguishable M q1 q2 \<Longrightarrow> \<exists>k. r_distinguishable_k M q1 q2 k" 
  proof (rule ccontr)

    (* Proof sketch: if no k exists such that q1 and q2 are r(k)-distinguishable, then 
                     it is possible to construct a complete submachine of the product 
                     machine (product (from_FSM M q1) (from_FSM M q2)) by using only those
                     transitions in (product (from_FSM M q1) (from_FSM M q2)) that lead
                     from a pair of non r(0)-distinguishable states to a pair that is not
                     r(j)-distinguishable for any j. 
    *)

    assume "r_distinguishable M q1 q2"
    assume c_assm: "\<not> (\<exists>k. r_distinguishable_k M q1 q2 k)"
  
    let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
    (* filter function to restrict transitions of ?P *)
    let ?f = "\<lambda> t . \<not> r_distinguishable_k M (fst (t_source t)) (snd (t_source t)) 0 \<and> \<not> (\<exists> k . r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k) \<and> t_source t \<in> reachable_states ?P"
    let ?ft = "Set.filter ?f (transitions ?P)"
    (* resulting submachine of ?P *)
    let ?PC = "filter_transitions ?P ?f" 
    let ?PCR = "restrict_to_reachable_states ?PC"
  
  
    have h_ft : "transitions ?PC = { t \<in> transitions ?P . ?f t }" 
      by auto

    have states_non_r_d_k : "\<And> q . q \<in> reachable_states ?PC \<Longrightarrow> \<not> (\<exists> k . r_distinguishable_k M (fst q) (snd q) k)"
    proof -   
      fix q assume "q \<in> reachable_states ?PC"
      have "q = initial ?PC \<or> (\<exists> t \<in> transitions ?PC . q = t_target t)"
        by (metis (no_types, lifting) \<open>q \<in> reachable_states (FSM.filter_transitions (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2)) (\<lambda>t. \<not> r_distinguishable_k M (fst (t_source t)) (snd (t_source t)) 0 \<and> (\<nexists>k. r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k) \<and> t_source t \<in> reachable_states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))))\<close> reachable_states_initial_or_target)
      then have "q = (q1,q2) \<or> (\<exists> t \<in> transitions ?PC . q = t_target t)"
        by (simp add: assms(1) assms(2))

      show "\<not> (\<exists> k . r_distinguishable_k M (fst q) (snd q) k)"
      proof (cases "q = (q1,q2)")
        case True
        then show ?thesis using c_assm by auto
      next
        case False
        then obtain t where "t \<in> transitions ?PC" and "q = t_target t" using \<open>q = (q1,q2) \<or> (\<exists> t \<in> transitions ?PC . q = t_target t)\<close> by blast
        then show ?thesis
          using h_ft by blast 
      qed
    qed
    then have states_non_r_d_k_PCR: "\<And> q . q \<in> states ?PCR \<Longrightarrow> \<not> (\<exists> k . r_distinguishable_k M (fst q) (snd q) k)"
      unfolding restrict_to_reachable_states_simps by blast

    have "\<And> q . q \<in> reachable_states ?PC \<Longrightarrow> completely_specified_state ?PC q"  
    proof -
      fix q assume "q \<in> reachable_states ?PC"
      then have "q \<in> reachable_states ?P"
        using filter_transitions_reachable_states by fastforce

      show "completely_specified_state ?PC q"
      proof (rule ccontr)
        assume "\<not> completely_specified_state ?PC q"
        then obtain x where "x \<in> (inputs ?PC)" 
                        and "\<not>(\<exists> t \<in> transitions ?PC . t_source t = q \<and> t_input t = x)"
          unfolding completely_specified_state.simps by blast
        then have "\<not>(\<exists> t \<in> transitions ?P . t_source t = q \<and> t_input t = x \<and> ?f t)"
          using h_ft by blast
        then have not_f : "\<And> t . t \<in> transitions ?P \<Longrightarrow> t_source t = q \<Longrightarrow> t_input t = x \<Longrightarrow> \<not> ?f t"
          by blast


        have "\<exists> k . r_distinguishable_k M (fst q) (snd q) k"
        proof (cases "r_distinguishable_k M (fst q) (snd q) 0")
          case True
          then show ?thesis by blast
        next
          case False

          let ?tp = "{t . t \<in> transitions ?P \<and> t_source t = q \<and> t_input t = x}"
          have "finite ?tp" using fsm_transitions_finite[of ?P] by force
 
          have k_ex : "\<forall> t \<in> ?tp . \<exists> k . \<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k'"
          proof 
            fix t assume "t \<in> ?tp"
            then have "\<not> ?f t" using not_f by blast
            then obtain k where "r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k" 
              using False \<open>t \<in> ?tp\<close>
              using \<open>q \<in> reachable_states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))\<close> by blast
            then have "\<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k'"
              using nat_induct_at_least by fastforce
            then show "\<exists> k . \<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k'" by auto
          qed

          obtain k where k_def : "\<And> t . t \<in> ?tp \<Longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"          
            using finite_set_min_param_ex[OF \<open>finite ?tp\<close>, of "\<lambda> t k' . r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k'"]  k_ex by blast
          
          then have "\<forall> t \<in> transitions ?P . (t_source t = q \<and> t_input t = x) \<longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
            by blast
          
          have "r_distinguishable_k M (fst q) (snd q) (Suc k)"
          proof - 
            have "\<And> t1 t2 . t1 \<in> transitions M \<Longrightarrow> t2 \<in> transitions M \<Longrightarrow> t_source t1 = fst q \<Longrightarrow> t_source t2 = snd q \<Longrightarrow> t_input t1 = x \<Longrightarrow> t_input t2 = x \<Longrightarrow> t_output t1 = t_output t2 \<Longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k"
            proof -
              fix t1 t2 assume "t1 \<in> transitions M" 
                           and "t2 \<in> transitions M" 
                           and "t_source t1 = fst q" 
                           and "t_source t2 = snd q" 
                           and "t_input t1 = x" 
                           and "t_input t2 = x" 
                           and "t_output t1 = t_output t2"
              then have "t_input t1 = t_input t2"
                    and "t_output t1 = t_output t2" by auto

              
              have "(fst q, snd q) \<in> reachable_states ?P" using  \<open>q \<in> reachable_states ?P\<close> by (metis prod.collapse)
              then have "(fst q, snd q) \<in> states ?P" using reachable_state_is_state by metis
              then have "fst q \<in> states (from_FSM M q1)"
                    and "snd q \<in> states (from_FSM M q2)"
                unfolding product_simps by auto

              have "t1 \<in> transitions (from_FSM M q1)"
                by (simp add: \<open>t1 \<in> FSM.transitions M\<close> assms(1))
              moreover have "t2 \<in> transitions (from_FSM M q2)"
                by (simp add: \<open>t2 \<in> FSM.transitions M\<close> assms(2))   
              moreover have "t_source ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2)) = q"
                using \<open>t_source t1 = fst q\<close> \<open>t_source t2 = snd q\<close> by auto
              moreover have "t_input ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2)) = x"
                using \<open>t_input t1 = x\<close> by auto
              ultimately have tt: "((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2)) \<in> ?tp"
                unfolding product_transitions_alt_def
                using \<open>t_input t1 = x\<close> \<open>t_input t2 = x\<close> \<open>t_output t1 = t_output t2\<close> by fastforce
                

              show "r_distinguishable_k M (t_target t1) (t_target t2) k"
                using k_def[OF tt] by auto
            qed

            moreover have "x \<in> (inputs M)" 
              using \<open>x \<in> (inputs ?PC)\<close> unfolding filter_transitions_simps product_simps  from_FSM_simps[OF \<open>q1 \<in> states M\<close>] from_FSM_simps[OF \<open>q2 \<in> states M\<close>]
              by blast
            ultimately show ?thesis
              unfolding r_distinguishable_k.simps by blast
          qed
          then show ?thesis by blast
        qed

        then show "False" 
          using states_non_r_d_k[OF \<open>q \<in> reachable_states ?PC\<close>] by blast
      qed
    qed
    then have "\<And> q . q \<in> states ?PCR \<Longrightarrow> completely_specified_state ?PCR q"
      unfolding restrict_to_reachable_states_simps completely_specified_state.simps
      by blast 
    then have "completely_specified ?PCR"
      using completely_specified_states by blast   
    moreover have "is_submachine ?PCR ?P"
    proof -
      have "is_submachine ?PC ?P"
        unfolding is_submachine.simps filter_transitions_simps by blast
      moreover have "is_submachine ?PCR ?PC"
        unfolding is_submachine.simps restrict_to_reachable_states_simps
        using reachable_state_is_state by fastforce 
      ultimately show ?thesis
        using submachine_transitive by blast
    qed
    ultimately have "r_compatible M q1 q2"
      unfolding r_compatible_def by blast
    then show "False" using \<open>r_distinguishable M q1 q2\<close>
      by blast 
  qed  
  

  show "\<exists>k. r_distinguishable_k M q1 q2 k \<Longrightarrow> r_distinguishable M q1 q2"
  proof (rule ccontr)
    assume *: "\<not> r_distinguishable M q1 q2"
    assume **: "\<exists>k. r_distinguishable_k M q1 q2 k"        
    then obtain k where "r_distinguishable_k M q1 q2 k" by auto
    then show "False"
    using * assms proof (induction k arbitrary: q1 q2)
      case 0
      then obtain S where "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
                      and "completely_specified S"
        by (meson r_compatible_def)      
      then have "completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2)))"
        using complete_submachine_initial by metis
      then show "False" using r_distinguishable_k_0_not_completely_specified[OF "0.prems"(1,3,4) ] by metis
    next
      case (Suc k)
      then show "False" 
      proof (cases "r_distinguishable_k M q1 q2 k")
        case True
        then show ?thesis 
          using Suc.IH Suc.prems by blast 
      next
        case False
        then obtain x where "x \<in> (inputs M)"
                        and "\<forall>y q1' q2'. (q1, x, y, q1') \<in> transitions M \<and> (q2, x, y, q2') \<in> transitions M \<longrightarrow> r_distinguishable_k M q1' q2' k"
          using Suc.prems(1) by fastforce

        from Suc obtain S where "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
                            and "completely_specified S"
          by (meson r_compatible_def) 

        have "x \<in> (inputs (product (from_FSM M q1) (from_FSM M q2)))"
          by (simp add: Suc.prems(4) \<open>x \<in> FSM.inputs M\<close>) 
        then have "x \<in> (inputs S)" 
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          by (metis is_submachine.elims(2)) 

        moreover have "initial S = (q1,q2)"
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          by (simp add: Suc.prems(3) Suc.prems(4))
        ultimately obtain y q1' q2' where "((q1,q2),x,y,(q1',q2')) \<in> transitions S"
          using \<open>completely_specified S\<close> using fsm_initial by fastforce 
        then have "((q1,q2),x,y,(q1',q2')) \<in> transitions (product (from_FSM M q1) (from_FSM M q2))"
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          by auto
        then have "(q1, x, y, q1') \<in> transitions (from_FSM M q1)" and "(q2, x, y, q2') \<in> transitions (from_FSM M q2)" 
          unfolding product_transitions_def by force+
        then have "(q1, x, y, q1') \<in> transitions M" and "(q2, x, y, q2') \<in> transitions M"
          by (simp add: Suc.prems(3,4))+
        then have "r_distinguishable_k M q1' q2' k" 
          using \<open>\<forall>y q1' q2'. (q1, x, y, q1') \<in> transitions M \<and> (q2, x, y, q2') \<in> transitions M \<longrightarrow> r_distinguishable_k M q1' q2' k\<close> by blast
        have "r_distinguishable M q1' q2'"
          by (metis (no_types) Suc.IH \<open>(q1, x, y, q1') \<in> FSM.transitions M\<close> \<open>(q2, x, y, q2') \<in> FSM.transitions M\<close> \<open>r_distinguishable_k M q1' q2' k\<close> fsm_transition_target snd_conv) 
        moreover have "\<exists> S' . completely_specified S' \<and> is_submachine S' (product (from_FSM M q1') (from_FSM M q2'))"
          using submachine_transition_complete_product_from[OF \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close> \<open>completely_specified S\<close> \<open>((q1,q2),x,y,(q1',q2')) \<in> transitions S\<close> Suc.prems(3,4)]
                submachine_transition_product_from[OF \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close> \<open>((q1,q2),x,y,(q1',q2')) \<in> transitions S\<close> Suc.prems(3,4)]          by blast 

        ultimately show "False" unfolding r_compatible_def by blast
      qed
    qed
  qed
qed



subsection \<open>Bounds\<close>


inductive is_least_r_d_k_path :: "('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) \<times> 'b \<times> nat) list \<Rightarrow> bool" where
  immediate[intro!] : "x \<in> (inputs M) \<Longrightarrow> \<not> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<Longrightarrow> is_least_r_d_k_path M q1 q2 [((q1,q2),x,0)]" |
  step[intro!] : "Suc k = (LEAST k' . r_distinguishable_k M q1 q2 k') 
                  \<Longrightarrow> x \<in> (inputs M)
                  \<Longrightarrow> (\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)
                  \<Longrightarrow> t1 \<in> transitions M
                  \<Longrightarrow> t2 \<in> transitions M
                  \<Longrightarrow> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2
                  \<Longrightarrow> is_least_r_d_k_path M (t_target t1) (t_target t2) p
                  \<Longrightarrow> is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#p)"

inductive_cases is_least_r_d_k_path_immediate_elim[elim!]: "is_least_r_d_k_path M q1 q2 [((q1,q2),x,0)]"
inductive_cases is_least_r_d_k_path_step_elim[elim!]: "is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#p)"


lemma is_least_r_d_k_path_nonempty :
  assumes "is_least_r_d_k_path M q1 q2 p"
  shows "p \<noteq> []"
  using is_least_r_d_k_path.cases[OF assms] by blast

lemma is_least_r_d_k_path_0_extract : 
  assumes "is_least_r_d_k_path M q1 q2 [t]"
  shows "\<exists> x . t = ((q1,q2),x,0)"
    using is_least_r_d_k_path.cases[OF assms]
    by (metis (no_types, lifting) list.inject is_least_r_d_k_path_nonempty) 

lemma is_least_r_d_k_path_Suc_extract : 
  assumes "is_least_r_d_k_path M q1 q2 (t#t'#p)"
  shows "\<exists> x k . t = ((q1,q2),x,Suc k)"
    using is_least_r_d_k_path.cases[OF assms]
    by (metis (no_types, lifting) list.distinct(1) list.inject)

lemma is_least_r_d_k_path_Suc_transitions :
  assumes "is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#p)"
  shows "(\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)"
  using is_least_r_d_k_path_step_elim[OF assms]
        Suc_inject[of _ k]  
  by metis


lemma is_least_r_d_k_path_is_least :
  assumes "is_least_r_d_k_path M q1 q2 (t#p)"
  shows "r_distinguishable_k M q1 q2 (snd (snd t)) \<and> (snd (snd t)) = (LEAST k' . r_distinguishable_k M q1 q2 k')"
proof (cases p)
  case Nil
  then obtain x where "t = ((q1,q2),x,0)" and "is_least_r_d_k_path M q1 q2 [((q1,q2),x,0)]"
    using assms is_least_r_d_k_path_0_extract by metis
  have *: "r_distinguishable_k M q1 q2 0"
    using is_least_r_d_k_path_immediate_elim[OF \<open>is_least_r_d_k_path M q1 q2 [((q1,q2),x,0)]\<close>] unfolding r_distinguishable_k.simps by auto
  then have "(\<exists>k. r_distinguishable_k M q1 q2 k)"
    by blast
  then have "0 = (LEAST k' . r_distinguishable_k M q1 q2 k')" 
    using \<open>r_distinguishable_k M q1 q2 0\<close> by auto
  moreover have "snd (snd t) = 0"
    using \<open>t = ((q1,q2),x,0)\<close> by auto
  ultimately show ?thesis using * by auto  
next
  case (Cons t' p')
  then obtain x k where "t = ((q1,q2),x,Suc k)" and "is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#t'#p')"
    using assms is_least_r_d_k_path_Suc_extract by metis

  have "x \<in> (inputs M)"
    using is_least_r_d_k_path_step_elim[OF \<open>is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#t'#p')\<close>] by blast
  moreover have "(\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)"
    using is_least_r_d_k_path_Suc_transitions[OF \<open>is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#(t'#p'))\<close>] by assumption
  ultimately have "r_distinguishable_k M q1 q2 (Suc k)"
    unfolding r_distinguishable_k.simps by blast
  moreover have "Suc k = (LEAST k' . r_distinguishable_k M q1 q2 k')"
    using is_least_r_d_k_path_step_elim[OF \<open>is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#t'#p')\<close>] by blast  
  ultimately show ?thesis
    by (metis \<open>t = ((q1, q2), x, Suc k)\<close> snd_conv) 
qed


lemma r_distinguishable_k_least_next :
  assumes "\<exists> k . r_distinguishable_k M q1 q2 k"
      and "(LEAST k . r_distinguishable_k M q1 q2 k) = Suc k"
      and "x \<in> (inputs M)"
      and "\<forall>t1\<in> transitions M. \<forall>t2\<in> transitions M.
            t_source t1 = q1 \<and>
            t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
            r_distinguishable_k M (t_target t1) (t_target t2) k"
    shows "\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<and> (LEAST k . r_distinguishable_k M (t_target t1) (t_target t2) k) = k"
proof -
  have "r_distinguishable_k M q1 q2 (Suc k)"
    using assms LeastI by metis
  moreover have "\<not> r_distinguishable_k M q1 q2 k"
    using assms(2) by (metis lessI not_less_Least) 

  have **: "(\<forall>t1\<in> transitions M.
         \<forall>t2\<in> transitions M.
            t_source t1 = q1 \<and>
            t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
            (LEAST k' . r_distinguishable_k M (t_target t1) (t_target t2) k') \<le> k)"
    using assms(3,4) Least_le by blast

  show ?thesis proof (rule ccontr)
    assume assm : "\<not> (\<exists>t1\<in>(transitions M).
           \<exists>t2\<in>(transitions M).
              (t_source t1 = q1 \<and>
               t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<and>
              (LEAST k. r_distinguishable_k M (t_target t1) (t_target t2) k) = k)"
    
    let ?hs = "{(t1,t2) | t1 t2 . t1 \<in> transitions M \<and> t2 \<in> transitions M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2}"
    have "finite ?hs"
    proof -
      have "?hs \<subseteq> (transitions M \<times> transitions M)" by blast
      moreover have "finite (transitions M \<times> transitions M)" using fsm_transitions_finite by blast
      ultimately show ?thesis
        by (simp add: finite_subset) 
    qed
    have fk_def : "\<And> tt . tt \<in> ?hs \<Longrightarrow> r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) (LEAST k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k)"
    proof -
      fix tt assume "tt \<in> ?hs"
      then have "(fst tt) \<in> transitions M \<and> (snd tt) \<in> transitions M \<and> t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt)"
        by force 
      then have "\<exists> k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k"
        using assms(4) by blast
      then show "r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) (LEAST k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k)"
        using LeastI2_wellorder by blast            
    qed

    let ?k = "Max (image (\<lambda> tt . (LEAST k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k)) ?hs)"
    have "\<And> t1 t2 . t1 \<in> transitions M \<Longrightarrow> t2 \<in> transitions M \<Longrightarrow> t_source t1 = q1 \<Longrightarrow> t_source t2 = q2 \<Longrightarrow> t_input t1 = x \<Longrightarrow> t_input t2 = x \<Longrightarrow> t_output t1 = t_output t2 \<Longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) ?k"
    proof -
      fix t1 t2 assume "t1 \<in> transitions M" 
                   and "t2 \<in> transitions M" 
                   and "t_source t1 = q1" 
                   and "t_source t2 = q2" 
                   and "t_input t1 = x" 
                   and "t_input t2 = x" 
                   and "t_output t1 = t_output t2"   
      then have "(t1,t2) \<in> ?hs" by force
      then have "r_distinguishable_k M (t_target t1) (t_target t2) ((\<lambda> tt . (LEAST k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k)) (t1,t2))"
        using fk_def by force
      have "(\<lambda> tt . (LEAST k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k)) (t1,t2) \<le> ?k"
        using \<open>(t1,t2) \<in> ?hs\<close> \<open>finite ?hs\<close>
        by (meson Max.coboundedI finite_imageI image_iff) 
      show "r_distinguishable_k M (t_target t1) (t_target t2) ?k" 
        using r_distinguishable_k_by_larger[OF \<open>r_distinguishable_k M (t_target t1) (t_target t2) ((\<lambda> tt . (LEAST k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k)) (t1,t2))\<close> \<open>(\<lambda> tt . (LEAST k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k)) (t1,t2) \<le> ?k\<close>] by assumption
    qed


    then have "r_distinguishable_k M q1 q2 (Suc ?k)"
      unfolding r_distinguishable_k.simps 
      using \<open>x \<in> (inputs M)\<close> by blast

    have "?hs \<noteq> {}"
    proof 
      assume "?hs = {}"
      then have "r_distinguishable_k M q1 q2 0"
        unfolding r_distinguishable_k.simps using \<open>x \<in> (inputs M)\<close> by force
      then show "False"
        using assms(2) by auto
    qed

    have "\<And> t1 t2 . t1\<in> transitions M \<Longrightarrow>
         t2\<in> transitions M \<Longrightarrow>
            t_source t1 = q1 \<and>
            t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<Longrightarrow>
            (LEAST k' . r_distinguishable_k M (t_target t1) (t_target t2) k') < k" 
    proof -  
      fix t1 t2 assume "t1\<in> transitions M" and "t2\<in> transitions M" and t12_def : "t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
      have "(LEAST k' . r_distinguishable_k M (t_target t1) (t_target t2) k') \<le> k" using \<open>t1\<in> transitions M\<close> \<open>t2\<in> transitions M\<close> t12_def ** by blast
      moreover have "(LEAST k' . r_distinguishable_k M (t_target t1) (t_target t2) k') \<noteq> k" using \<open>t1\<in> transitions M\<close> \<open>t2\<in> transitions M\<close> t12_def assm by blast
      ultimately show "(LEAST k' . r_distinguishable_k M (t_target t1) (t_target t2) k') < k" by auto
    qed
    moreover have "\<And> tt . tt \<in> ?hs \<Longrightarrow> (fst tt) \<in> transitions M \<and> (snd tt) \<in> transitions M \<and> t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt)"
      by force
    ultimately have "\<And> tt . tt \<in> ?hs \<Longrightarrow> (LEAST k' . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k') < k" by blast
    moreover obtain tt where "tt \<in> ?hs" and "?k = (LEAST k' . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k')" 
      using Max_elem[OF \<open>finite ?hs\<close> \<open>?hs \<noteq> {}\<close>, of "\<lambda> tt . (LEAST k' . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k')"] by blast
    ultimately have "?k < k" 
      using \<open>finite ?hs\<close> by presburger

    then show "False"
      using assms(2) \<open>r_distinguishable_k M q1 q2 (Suc ?k)\<close>
      by (metis (no_types, lifting) Suc_mono not_less_Least) 
  qed
qed   


lemma is_least_r_d_k_path_length_from_r_d :
  assumes "\<exists> k . r_distinguishable_k M q1 q2 k"
  shows "\<exists> t p . is_least_r_d_k_path M q1 q2 (t#p) \<and> length (t#p) = Suc (LEAST k . r_distinguishable_k M q1 q2 k)"
proof -
  let ?k = "LEAST k . r_distinguishable_k M q1 q2 k"
  have "r_distinguishable_k M q1 q2 ?k"
    using assms LeastI by blast 
  
  then show ?thesis using assms proof (induction ?k arbitrary: q1 q2)
    case 0
    then have "r_distinguishable_k M q1 q2 0" by auto
    then obtain x where "x \<in> (inputs M)" and "\<not> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
      unfolding r_distinguishable_k.simps by blast
    then have "is_least_r_d_k_path M q1 q2 [((q1,q2),x,0)]"
      by auto
    then show ?case using "0.hyps"
      by (metis length_Cons list.size(3))
  next
    case (Suc k)
    then have "r_distinguishable_k M q1 q2 (Suc k)" by auto
    moreover have "\<not> r_distinguishable_k M q1 q2 k"
      using Suc by (metis lessI not_less_Least) 
    ultimately obtain x where "x \<in> (inputs M)" and *: "(\<forall>t1\<in>(transitions M).
           \<forall>t2\<in>(transitions M).
              t_source t1 = q1 \<and>
              t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
              r_distinguishable_k M (t_target t1) (t_target t2) k)"
      unfolding r_distinguishable_k.simps by blast
    
    obtain t1 t2 where "t1 \<in> transitions M" and "t2 \<in> transitions M"
                        and "t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
                        and "k = (LEAST k. r_distinguishable_k M (t_target t1) (t_target t2) k)"
      using r_distinguishable_k_least_next[OF Suc.prems(2) _ \<open>x \<in> (inputs M)\<close> *] Suc.hyps(2) by metis
    then have "r_distinguishable_k M (t_target t1) (t_target t2) (LEAST k. r_distinguishable_k M (t_target t1) (t_target t2) k)"
      using * by metis
    
    then obtain t' p' where "is_least_r_d_k_path M (t_target t1) (t_target t2) (t' # p')"
                        and "length (t' # p') = Suc (Least (r_distinguishable_k M (t_target t1) (t_target t2)))"
      using Suc.hyps(1)[OF \<open>k = (LEAST k. r_distinguishable_k M (t_target t1) (t_target t2) k)\<close>] by blast

    then have "is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#t'#p')"
      using is_least_r_d_k_path.step[OF Suc.hyps(2) \<open>x \<in> (inputs M)\<close> * \<open>t1 \<in> transitions M\<close> \<open>t2 \<in> transitions M\<close> \<open>t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2\<close>] 
      by auto

    
    show ?case
      by (metis (no_types) Suc.hyps(2) \<open>is_least_r_d_k_path M q1 q2 (((q1, q2), x, Suc k) # t' # p')\<close> \<open>k = (LEAST k. r_distinguishable_k M (t_target t1) (t_target t2) k)\<close> \<open>length (t' # p') = Suc (Least (r_distinguishable_k M (t_target t1) (t_target t2)))\<close> length_Cons)      
  qed
qed



lemma is_least_r_d_k_path_states :
  assumes "is_least_r_d_k_path M q1 q2 p"
      and "q1 \<in> states M"
      and "q2 \<in> states M"
shows "set (map fst p) \<subseteq> states (product (from_FSM M q1) (from_FSM M q2))"
  using assms proof (induction p)
  case (immediate x M q1 q2) 
  then show ?case by auto
next
  case (step k M q1 q2 x t1 t2 p)
  then have "t_target t1 \<in> states M" and "t_target t2 \<in> states M" by blast+
  have "t_source t1 = q1" and "t_source t2 = q2"
    using step by metis+

  have "t_target t1 \<in> states (from_FSM M q1)"
    by (simp add: \<open>t_target t1 \<in> FSM.states M\<close> step.prems(1))
  have "t_target t2 \<in> states (from_FSM M q2)"
    by (simp add: \<open>t_target t2 \<in> FSM.states M\<close> step.prems(2)) 

  have "t1 \<in> transitions (from_FSM M q1)"
    by (simp add: step.hyps(4) step.prems(1))    
  have "t2 \<in> transitions (from_FSM M q2)"
    by (simp add: step.hyps(5) step.prems(2))
  have "t_input t1 = t_input t2" using step.hyps(6) by auto
  have "t_output t1 = t_output t2" using step.hyps(6) by auto

  have "((q1,q2),t_input t1, t_output t1, (t_target t1, t_target t2)) \<in> transitions (product (from_FSM M q1) (from_FSM M q2))" 
    using \<open>t1 \<in> transitions (from_FSM M q1)\<close> \<open>t2 \<in> transitions (from_FSM M q2)\<close> \<open>t_input t1 = t_input t2\<close> \<open>t_output t1 = t_output t2\<close> \<open>t_source t1 = q1\<close> \<open>t_source t2 = q2\<close>
    unfolding product_transitions_alt_def by blast

  then have "(t_target t1, t_target t2) \<in> states (product (from_FSM M q1) (from_FSM M q2))"
    using fsm_transition_target
    by (metis snd_conv) 

  moreover have "states (product (from_FSM M (t_target t1)) (from_FSM M (t_target t2))) \<subseteq> states (product (from_FSM M q1) (from_FSM M q2))"
    using calculation step.prems(1) step.prems(2) by auto
    

  moreover have "set (map fst p) \<subseteq> states (product (from_FSM M (t_target t1)) (from_FSM M (t_target t2)))"
    using step.IH  \<open>t_target t1 \<in> states (from_FSM M q1)\<close>  \<open>t_target t2 \<in> states (from_FSM M q2)\<close>
    using step.prems by auto
  ultimately have "set (map fst p) \<subseteq> states (product (from_FSM M q1) (from_FSM M q2))"
    by blast
  
  moreover have "set (map fst [((q1,q2),x,Suc k)]) \<subseteq> states (product (from_FSM M q1) (from_FSM M q2))"
    using fsm_transition_source[OF \<open>((q1, q2), t_input t1, t_output t1, t_target t1, t_target t2) \<in> (transitions (product (from_FSM M q1) (from_FSM M q2)))\<close>]
    by auto
    
  ultimately show ?case
    by auto
qed


lemma is_least_r_d_k_path_decreasing :
  assumes "is_least_r_d_k_path M q1 q2 p"
  shows "\<forall> t' \<in> set (tl p) . snd (snd t') < snd (snd (hd p))"
using assms proof(induction p)
  case (immediate x M q1 q2)
  then show ?case by auto
next
  case (step k M q1 q2 x t1 t2 p)
  then show ?case proof (cases p)
    case Nil
    then show ?thesis by auto
  next
    case (Cons t' p')
    then have "is_least_r_d_k_path M (t_target t1) (t_target t2) (t'#p')" using step.hyps(7) by auto

    have "r_distinguishable_k M (t_target t1) (t_target t2) (snd (snd t'))" 
     and "snd (snd t') = (LEAST k'. r_distinguishable_k M (t_target t1) (t_target t2) k')"
      using is_least_r_d_k_path_is_least[OF \<open>is_least_r_d_k_path M (t_target t1) (t_target t2) (t'#p')\<close>] by auto

    have "snd (snd t') < Suc k"
      by (metis \<open>snd (snd t') = (LEAST k'. r_distinguishable_k M (t_target t1) (t_target t2) k')\<close> local.step(3) local.step(4) local.step(5) local.step(6) not_less_Least not_less_eq)
    moreover have "\<forall>t''\<in>set p. snd (snd t'') \<le> snd (snd t')" 
      using Cons step.IH by auto
    ultimately show ?thesis by auto
  qed
qed


lemma is_least_r_d_k_path_suffix :
  assumes "is_least_r_d_k_path M q1 q2 p"
      and "i < length p"
    shows "is_least_r_d_k_path M (fst (fst (hd (drop i p)))) (snd (fst (hd (drop i p)))) (drop i p)"
using assms proof(induction p arbitrary: i)
  case (immediate x M q1 q2)
  then show ?case by auto
next
  case (step k M q1 q2 x t1 t2 p)
  then have "is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#p)"
    by blast 

  have "\<And> i . i < length p \<Longrightarrow> is_least_r_d_k_path M (fst (fst (hd (drop (Suc i) (((q1, q2), x, Suc k) # p))))) (snd (fst (hd (drop (Suc i) (((q1, q2), x, Suc k) # p))))) (drop (Suc i) (((q1, q2), x, Suc k) # p))"
    using step.IH by simp
  then have "\<And> i . i < length (((q1, q2), x, Suc k) # p) \<Longrightarrow> i > 0 \<Longrightarrow> is_least_r_d_k_path M (fst (fst (hd (drop i (((q1, q2), x, Suc k) # p))))) (snd (fst (hd (drop i (((q1, q2), x, Suc k) # p))))) (drop i (((q1, q2), x, Suc k) # p))"
    by (metis Suc_less_eq gr0_implies_Suc length_Cons)
  moreover have "\<And> i . i < length (((q1, q2), x, Suc k) # p) \<Longrightarrow> i = 0 \<Longrightarrow> is_least_r_d_k_path M (fst (fst (hd (drop i (((q1, q2), x, Suc k) # p))))) (snd (fst (hd (drop i (((q1, q2), x, Suc k) # p))))) (drop i (((q1, q2), x, Suc k) # p))"
    using \<open>is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#p)\<close> by auto
  ultimately show ?case
    using step.prems by blast 
qed

  
lemma is_least_r_d_k_path_distinct :
  assumes "is_least_r_d_k_path M q1 q2 p"
  shows "distinct (map fst p)"
using assms proof(induction p)
  case (immediate x M q1 q2)
  then show ?case by auto
next
  case (step k M q1 q2 x t1 t2 p)
  then have "is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#p)"
    by blast 
  
  show ?case proof (rule ccontr)
    assume "\<not> distinct (map fst (((q1, q2), x, Suc k) # p))"
    then have "(q1,q2) \<in> set (map fst p)"
      using step.IH by simp 
    then obtain i where "i < length p" and "(map fst p) ! i = (q1,q2)"
      by (metis distinct_Ex1 length_map step.IH)
    then obtain x' k' where "hd (drop i p) = ((q1,q2),x',k')"
      by (metis fst_conv hd_drop_conv_nth nth_map old.prod.exhaust)

    have "is_least_r_d_k_path M q1 q2 (drop i p)"
      using is_least_r_d_k_path_suffix[OF \<open>is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#p)\<close>] \<open>i < length p\<close>
    proof -
      have "snd (fst (hd (drop i p))) = q2"
        using \<open>hd (drop i p) = ((q1, q2), x', k')\<close> by auto
      then show ?thesis
        by (metis (no_types) \<open>hd (drop i p) = ((q1, q2), x', k')\<close> \<open>i < length p\<close> fst_conv is_least_r_d_k_path_suffix step.hyps(7))
    qed

    have "k' < Suc k"
      using is_least_r_d_k_path_decreasing[OF \<open>is_least_r_d_k_path M q1 q2 (((q1,q2),x,Suc k)#p)\<close>]
      by (metis Cons_nth_drop_Suc \<open>hd (drop i p) = ((q1, q2), x', k')\<close> \<open>i < length p\<close> hd_in_set in_set_dropD list.sel(1) list.sel(3) list.simps(3) snd_conv)
    moreover have "k' = (LEAST k'. r_distinguishable_k M q1 q2 k')"  
      using is_least_r_d_k_path_is_least \<open>is_least_r_d_k_path M q1 q2 (drop i p)\<close> is_least_r_d_k_path_is_least
      by (metis Cons_nth_drop_Suc \<open>hd (drop i p) = ((q1, q2), x', k')\<close> \<open>i < length p\<close> hd_drop_conv_nth snd_conv)
    ultimately show "False"
      using step.hyps(1) dual_order.strict_implies_not_eq by blast 
  qed
qed


lemma r_distinguishable_k_least_bound :
  assumes "\<exists> k . r_distinguishable_k M q1 q2 k"
      and "q1 \<in> states M"
      and "q2 \<in> states M"
  shows "(LEAST k . r_distinguishable_k M q1 q2 k) \<le> (size (product (from_FSM M q1) (from_FSM M q2)))"
proof (rule ccontr)
  assume "\<not> (LEAST k. r_distinguishable_k M q1 q2 k) \<le> (size (product (from_FSM M q1) (from_FSM M q2)))"
  then have c_assm : "(size (product (from_FSM M q1) (from_FSM M q2))) < (LEAST k. r_distinguishable_k M q1 q2 k)"
    by linarith

  obtain t p where "is_least_r_d_k_path M q1 q2 (t # p)" 
               and "length (t # p) = Suc (LEAST k. r_distinguishable_k M q1 q2 k)"
    using is_least_r_d_k_path_length_from_r_d[OF assms(1)] by blast
  then have "(size (product (from_FSM M q1) (from_FSM M q2))) < length (t # p)"
    using c_assm by linarith

  have "distinct (map fst (t # p))"
    using is_least_r_d_k_path_distinct[OF \<open>is_least_r_d_k_path M q1 q2 (t # p)\<close>] by assumption
  then have "card (set (map fst (t # p))) = length (t # p)"
    using distinct_card by fastforce
  moreover have "card (set (map fst (t # p))) \<le> size (product (from_FSM M q1) (from_FSM M q2))"
    using is_least_r_d_k_path_states[OF \<open>is_least_r_d_k_path M q1 q2 (t # p)\<close> assms(2,3)] fsm_states_finite card_mono unfolding size_def by blast
  ultimately have "length (t # p) \<le> size (product (from_FSM M q1) (from_FSM M q2))"
    by (metis) 
  then show "False"
    using \<open>size (product (from_FSM M q1) (from_FSM M q2)) < length (t # p)\<close> by linarith
qed




subsection \<open>Deciding R-Distinguishability\<close>

fun r_distinguishable_k_least :: "('a, 'b::linorder, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'b) option" where
  "r_distinguishable_k_least M q1 q2 0 = (case find (\<lambda> x . \<not> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (sort (inputs_as_list M)) of
    Some x \<Rightarrow> Some (0,x) |
    None \<Rightarrow> None)" |
  "r_distinguishable_k_least M q1 q2 (Suc n) = (case r_distinguishable_k_least M q1 q2 n of
    Some k \<Rightarrow> Some k |
    None \<Rightarrow> (case find (\<lambda> x . \<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) n) (sort (inputs_as_list M)) of
      Some x \<Rightarrow> Some (Suc n,x) |
      None \<Rightarrow> None))"


lemma r_distinguishable_k_least_ex : 
  assumes "r_distinguishable_k_least M q1 q2 k = None" 
  shows "\<not> r_distinguishable_k M q1 q2 k"
using assms proof (induction k)
  case 0
  show ?case proof (rule ccontr)
    assume "\<not> \<not> r_distinguishable_k M q1 q2 0"
    then have "(\<exists>x\<in>set (sort (inputs_as_list M)).
                 \<not> (\<exists>t1\<in>(transitions M).
                        \<exists>t2\<in>(transitions M).
                           t_source t1 = q1 \<and>
                           t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))"
      unfolding r_distinguishable_k.simps
      using inputs_as_list_set by auto 
    then obtain x where "find (\<lambda> x . \<not> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (sort (inputs_as_list M)) = Some x"
      unfolding r_distinguishable_k.simps using find_None_iff[of "\<lambda> x . \<not> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)" "sort (inputs_as_list M)"] by blast
    then have "r_distinguishable_k_least M q1 q2 0 = Some (0,x)"
      unfolding r_distinguishable_k_least.simps by auto
    then show "False" using 0 by simp
  qed
next
  case (Suc k)
  
  have "r_distinguishable_k_least M q1 q2 k = None"
    using Suc.prems unfolding r_distinguishable_k_least.simps
    using option.disc_eq_case(2) by force 
  then have *: "\<not> r_distinguishable_k M q1 q2 k"
    using Suc.IH by auto

  have "find
             (\<lambda>x. \<forall>t1\<in>(transitions M).
                     \<forall>t2\<in>(transitions M).
                        t_source t1 = q1 \<and>
                        t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
                        r_distinguishable_k M (t_target t1) (t_target t2) k)
             (sort (inputs_as_list M))  = None"
    using Suc.prems \<open>r_distinguishable_k_least M q1 q2 k = None\<close> unfolding r_distinguishable_k_least.simps
    using option.disc_eq_case(2) by force 

  then have **: "\<not>(\<exists> x \<in> set (sort (inputs_as_list M)) .  (\<forall>t1\<in>(transitions M).
                     \<forall>t2\<in>(transitions M).
                        t_source t1 = q1 \<and>
                        t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
                        r_distinguishable_k M (t_target t1) (t_target t2) k))"
    using find_None_iff[of "(\<lambda>x. \<forall>t1\<in>(transitions M).
                     \<forall>t2\<in>(transitions M).
                        t_source t1 = q1 \<and>
                        t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
                        r_distinguishable_k M (t_target t1) (t_target t2) k)" "(sort (inputs_as_list M))"] by auto
  
    
  show ?case using * ** unfolding r_distinguishable_k.simps
    using inputs_as_list_set by fastforce 
qed
  

lemma r_distinguishable_k_least_0_correctness :
  assumes  "r_distinguishable_k_least M q1 q2 n = Some (0,x)"  
  shows "r_distinguishable_k M q1 q2 0 \<and> 0 = 
            (LEAST k . r_distinguishable_k M q1 q2 k) 
            \<and> (x \<in> (inputs M) \<and> \<not> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
            \<and> (\<forall> x' \<in> (inputs M) . x' < x \<longrightarrow> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x' \<and> t_input t2 = x' \<and> t_output t1 = t_output t2))"
using assms proof (induction n)
  case 0
  then obtain x' where x'_def : "find (\<lambda> x . \<not> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (sort (inputs_as_list M)) = Some x'"
    unfolding r_distinguishable_k_least.simps by fastforce 
  then have "x = x'" using 0 unfolding r_distinguishable_k_least.simps by fastforce
  then have "x \<in> set (sort (inputs_as_list M)) \<and> \<not> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)" using 0 unfolding r_distinguishable_k_least.simps r_distinguishable_k.simps 
    using find_condition[OF x'_def] find_set[OF x'_def] by blast
  moreover have "r_distinguishable_k M q1 q2 0"
    using calculation List.linorder_class.set_sort unfolding r_distinguishable_k.simps
    using inputs_as_list_set by auto
  moreover have "0 = (LEAST k . r_distinguishable_k M q1 q2 k)"
    using calculation(2) by auto
  moreover have "(\<forall> x' \<in> (inputs M) . x' < x \<longrightarrow> (\<exists> t1 \<in> transitions M . \<exists> t2 \<in> transitions M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x' \<and> t_input t2 = x' \<and> t_output t1 = t_output t2))"
    using find_sort_least(1)[OF x'_def] \<open>x = x'\<close> inputs_as_list_set
    using leD by blast
  ultimately show ?case unfolding inputs_as_list_set set_sort by force
next
  case (Suc n)
  then show ?case proof (cases "r_distinguishable_k_least M q1 q2 n")
    case None
    have "r_distinguishable_k_least M q1 q2 (Suc n) \<noteq> Some (0, x)"
      using Suc.prems unfolding r_distinguishable_k_least.simps None
      by (metis (no_types, lifting) Zero_not_Suc fst_conv option.case_eq_if option.distinct(1) option.sel) 
    then show ?thesis using Suc.prems by auto
  next
    case (Some a)
    then have "r_distinguishable_k_least M q1 q2 n = Some (0, x)"
      using Suc.prems by auto
    then show ?thesis using Suc.IH by blast
  qed
qed


lemma r_distinguishable_k_least_Suc_correctness :
  assumes  "r_distinguishable_k_least M q1 q2 n = Some (Suc k,x)"  
  shows "r_distinguishable_k M q1 q2 (Suc k) \<and> (Suc k) = 
          (LEAST k . r_distinguishable_k M q1 q2 k) 
          \<and> (x \<in> (inputs M) \<and> (\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k))
          \<and> (\<forall> x' \<in> (inputs M) . x' < x \<longrightarrow> \<not>(\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x' \<and> t_input t2 = x' \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k))"
using assms proof (induction n)
  case 0
  then show ?case by (cases " find
         (\<lambda>x. \<not> (\<exists>t1\<in>(transitions M).
                     \<exists>t2\<in>(transitions M).
                        t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
         (sort (inputs_as_list M))"; auto)
next
  case (Suc n)
  then show ?case proof (cases "r_distinguishable_k_least M q1 q2 n")
    case None
    then have *: "(case find (\<lambda> x . \<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) n) (sort (inputs_as_list M)) of
      Some x \<Rightarrow> Some (Suc n,x) |
      None \<Rightarrow> None) = Some (Suc k,x)"
      using Suc.prems unfolding r_distinguishable_k_least.simps by auto
    then obtain x' where x'_def : "find (\<lambda> x . \<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) n) (sort (inputs_as_list M)) =  Some x'" 
      by fastforce
    then have "x = x'" using * by fastforce
    then have p3: "x \<in> (inputs M) \<and> (\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) n)"  
      using find_condition[OF x'_def] find_set[OF x'_def] set_sort inputs_as_list_set by metis
    then have p1: "r_distinguishable_k M q1 q2 (Suc n)"
      unfolding r_distinguishable_k.simps by blast
    moreover have "\<not> r_distinguishable_k M q1 q2 n"
      using r_distinguishable_k_least_ex[OF None] by assumption
    ultimately have p2: "(Suc n) = (LEAST k . r_distinguishable_k M q1 q2 k)"
      by (metis LeastI Least_le le_SucE r_distinguishable_k_by_larger)

    from * have "k = n" using x'_def by auto
    then have "(\<forall> x' \<in> (inputs M) . x' < x \<longrightarrow> \<not>(\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x' \<and> t_input t2 = x' \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k))"
      using find_sort_least(1)[OF x'_def] \<open>x = x'\<close> inputs_as_list_set
      using leD by blast
    then show ?thesis using p1 p2 p3 \<open>k = n\<close> by blast
  next
    case (Some a)
    then have "r_distinguishable_k_least M q1 q2 n = Some (Suc k, x)"
      using Suc.prems by auto
    then show ?thesis using Suc.IH
      by (meson r_distinguishable_k.simps(2))
  qed
qed


lemma r_distinguishable_k_least_is_least :
  assumes "r_distinguishable_k_least M q1 q2 n = Some (k,x)"
  shows "(\<exists> k . r_distinguishable_k M q1 q2 k) \<and> (k = (LEAST k . r_distinguishable_k M q1 q2 k))"
proof (cases k)
  case 0
  then show ?thesis using assms r_distinguishable_k_least_0_correctness by metis
next
  case (Suc n)
  then show ?thesis using assms r_distinguishable_k_least_Suc_correctness by metis
qed 


lemma r_distinguishable_k_from_r_distinguishable_k_least :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
shows "(\<exists> k . r_distinguishable_k M q1 q2 k) = (r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) \<noteq> None)"
  (is "?P1 = ?P2")
proof 
  show "?P1 \<Longrightarrow> ?P2"
    using r_distinguishable_k_least_ex r_distinguishable_k_least_bound[OF _ assms] r_distinguishable_k_by_larger
    by (metis LeastI)
  show "?P2 \<Longrightarrow> ?P1"
  proof -
    assume ?P2
    then obtain a where "(r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) = Some a)"
      by blast
    then obtain x k where kx_def : "(r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) = Some (k,x))"
      using prod.collapse by metis
    then show ?P1
    proof (cases k)
      case 0
      then have "(r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) = Some (0,x))"
        using kx_def by presburger
      show ?thesis using r_distinguishable_k_least_0_correctness[OF \<open>(r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) = Some (0,x))\<close>] by blast
    next
      case (Suc n)
      then have "(r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) = Some ((Suc n),x))"
        using kx_def by presburger
      show ?thesis using r_distinguishable_k_least_Suc_correctness[OF \<open>(r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) = Some ((Suc n),x))\<close>] by blast
    qed
  qed
qed


definition is_r_distinguishable :: "('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_r_distinguishable M q1 q2 = (\<exists> k . r_distinguishable_k M q1 q2 k)"


lemma is_r_distinguishable_contained_code[code] :
  "is_r_distinguishable M q1 q2 = (if (q1 \<in> states M \<and> q2 \<in> states M) then (r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) \<noteq> None)
                                                                    else \<not>(inputs M = {}))"
proof (cases "q1 \<in> states M \<and> q2 \<in> states M")
  case True
  then show ?thesis 
    unfolding is_r_distinguishable_def using r_distinguishable_k_from_r_distinguishable_k_least by metis
next
  case False
  then have *: "(\<not> (\<exists> t \<in> transitions M . t_source t = q1)) \<or> (\<not> (\<exists> t \<in> transitions M . t_source t = q2))"
    using fsm_transition_source by auto
  show ?thesis proof (cases "inputs M = {}")
    case True
    moreover have "\<And> k . r_distinguishable_k M q1 q2 k \<Longrightarrow> inputs M \<noteq> {}"
    proof -
      fix k assume "r_distinguishable_k M q1 q2 k"
      then show "inputs M \<noteq> {}" by (induction k; auto)
    qed
    ultimately have "is_r_distinguishable M q1 q2 = False"
      by (meson is_r_distinguishable_def)
    then show ?thesis using False True by auto
  next
    case False
    then show ?thesis
      by (meson "*" equals0I fst_conv is_r_distinguishable_def r_distinguishable_k_0_alt_def r_distinguishable_k_from_r_distinguishable_k_least) 
  qed 
qed



subsection \<open>State Separators and R-Distinguishability\<close>

lemma state_separator_r_distinguishes_k :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
      and "q1 \<in> states M" and "q2 \<in> states M" 
  shows "\<exists> k . r_distinguishable_k M q1 q2 k"
proof -
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  let ?C = "(canonical_separator M q1 q2)"
  
  have "is_submachine S ?C"
        and "single_input S"
        and "acyclic S"
        and "deadlock_state S (Inr q1)"
        and "deadlock_state S (Inr q2)"
        and "Inr q1 \<in> reachable_states S"
        and "Inr q2 \<in> reachable_states S"
        and "(\<forall>q\<in>reachable_states S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)"
        and tc: "(\<forall>q\<in>reachable_states S.
              \<forall>x\<in>(inputs ?C).
                 (\<exists>t\<in> transitions S. t_source t = q \<and> t_input t = x) \<longrightarrow>
                 (\<forall>t'\<in> transitions ?C. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S))"
    using assms(1) unfolding is_state_separator_from_canonical_separator_def by linarith+

  let ?Prop = "(\<lambda> q . case q of 
                    (Inl (q1',q2')) \<Rightarrow> (\<exists> k . r_distinguishable_k M q1' q2' k) |
                    (Inr qr) \<Rightarrow> True)"
  have rprop: "\<forall> q \<in> reachable_states S . ?Prop q"
  using \<open>acyclic S\<close> proof (induction rule: acyclic_induction)
  case (reachable_state q)
    then show ?case proof (cases "\<not> isl q")
      case True
      then have "q = Inr q1 \<or> q = Inr q2"
        using \<open>(\<forall>q\<in>reachable_states S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)\<close> reachable_state(1) by blast
      then show ?thesis by auto
    next
      case False
      then obtain q1' q2' where "q = Inl (q1',q2')" 
        using isl_def prod.collapse by metis
      then have "\<not> deadlock_state S q"
        using \<open>(\<forall>q\<in>reachable_states S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)\<close> reachable_state(1) by blast

      then obtain t where "t \<in> transitions S" and "t_source t = q"
        unfolding deadlock_state.simps by blast
      then have "(\<forall>t'\<in> transitions ?C. t_source t' = q \<and> t_input t' = t_input t \<longrightarrow> t' \<in> transitions S)"
        using reachable_state(1) tc
        using fsm_transition_input by fastforce  


      have "Inl (q1',q2') \<in> reachable_states ?C"
        using reachable_state(1) unfolding  \<open>q = Inl (q1',q2')\<close> reachable_states_def
        using submachine_path_initial[OF \<open>is_submachine S (canonical_separator M q1 q2)\<close>] 
        unfolding canonical_separator_simps[OF assms(2,3)] is_state_separator_from_canonical_separator_initial[OF assms(1-3)] by fast
      then obtain p where "path ?C (initial ?C) p"
                      and "target (initial ?C) p = Inl (q1',q2')"
        unfolding reachable_states_def by auto 
      then have "isl (target (initial ?C) p)" by auto
      then obtain p' where "path ?P (initial ?P) p'"
                       and "p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'"
        using canonical_separator_path_from_shift[OF \<open>path ?C (initial ?C) p\<close>]
        using assms(2) assms(3) by blast  

      have "(q1',q2') \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))"
        using reachable_state_is_state[OF \<open>Inl (q1',q2') \<in> reachable_states ?C\<close>] unfolding canonical_separator_simps[OF assms(2,3)]
        by auto 

      have "path (from_FSM M q1) (initial (from_FSM M q1)) (left_path p')"
          and "path (from_FSM M q2) (initial (from_FSM M q2)) (right_path p')"
        using product_path[of "from_FSM M q1" "from_FSM M q2" q1 q2 p'] \<open>path ?P (initial ?P) p'\<close>
        by (simp add: paths_from_product_path)+
      moreover have "target (initial (from_FSM M q1)) (left_path p') = q1'"
        using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> \<open>target (initial ?C) p = Inl (q1',q2')\<close> canonical_separator_simps(1)[OF assms(2,3)] assms(2)
        by (cases p' rule: rev_cases; auto)
      moreover have "target (initial (from_FSM M q2)) (right_path p') = q2'"
        using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> \<open>target (initial ?C) p = Inl (q1',q2')\<close> canonical_separator_simps(1)[OF assms(2,3)] assms(3) 
        by (cases p' rule: rev_cases; auto)
      moreover have "p_io (left_path p') = p_io (right_path p')" by auto
      ultimately have p12' : "\<exists>p1 p2.
               path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
               path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
               target (initial (from_FSM M q1)) p1 = q1' \<and>
               target (initial (from_FSM M q2)) p2 = q2' \<and> p_io p1 = p_io p2"
        by blast

      have "q1' \<in> states (from_FSM M q1)"
        using path_target_is_state[OF \<open>path (from_FSM M q1) (initial (from_FSM M q1)) (left_path p')\<close>] \<open>target (initial (from_FSM M q1)) (left_path p') = q1'\<close> by auto
      have "q2' \<in> states (from_FSM M q2)"
        using path_target_is_state[OF \<open>path (from_FSM M q2) (initial (from_FSM M q2)) (right_path p')\<close>] \<open>target (initial (from_FSM M q2)) (right_path p') = q2'\<close> by auto

      have "t_input t \<in> (inputs S)"
        using \<open>t \<in> transitions S\<close> by auto
      then have "t_input t \<in> (inputs ?C)"
        using \<open>is_submachine S ?C\<close> by auto
      then have "t_input t \<in> (inputs M)"
        using canonical_separator_simps(3)[OF assms(2,3)] by metis

      have *: "\<And> t1 t2 . t1 \<in> transitions M \<Longrightarrow> t2 \<in> transitions M \<Longrightarrow> t_source t1 = q1' \<Longrightarrow> t_source t2 = q2' \<Longrightarrow> t_input t1 = t_input t \<Longrightarrow> t_input t2 = t_input t \<Longrightarrow> t_output t1 = t_output t2 \<Longrightarrow> (\<exists> k . r_distinguishable_k M (t_target t1) (t_target t2) k)"
      proof -
        fix t1 t2 assume "t1 \<in> transitions M" 
                     and "t2 \<in> transitions M" 
                     and "t_source t1 = q1'" 
                     and "t_source t2 = q2'" 
                     and "t_input t1 = t_input t" 
                     and "t_input t2 = t_input t" 
                     and "t_output t1 = t_output t2"
        then have "t_input t1 = t_input t2" by auto

        have "t1 \<in> transitions (from_FSM M q1)" 
          using \<open>t_source t1 = q1'\<close> \<open>q1' \<in> states (from_FSM M q1)\<close> \<open>t1 \<in> transitions M\<close> by (simp add: assms(2))
        have "t2 \<in> transitions (from_FSM M q2)"
          using \<open>t_source t2 = q2'\<close> \<open>q2' \<in> states (from_FSM M q2)\<close> \<open>t2 \<in> transitions M\<close> by (simp add: assms(3))

        let ?t = "((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)"

        have "?t \<in> transitions ?P"
          using \<open>t1 \<in> transitions (from_FSM M q1)\<close> \<open>t2 \<in> transitions (from_FSM M q2)\<close> \<open>t_input t1 = t_input t2\<close> \<open>t_output t1 = t_output t2\<close>
          unfolding product_transitions_alt_def 
          by blast
        then have "shift_Inl ?t \<in> transitions ?C"
          using \<open>(q1',q2') \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))\<close>
          unfolding \<open>t_source t1 = q1'\<close> \<open>t_source t2 = q2'\<close> canonical_separator_transitions_def[OF assms(2,3)] by fastforce
        moreover have "t_source (shift_Inl ?t) = q"
          using \<open>t_source t1 = q1'\<close> \<open>t_source t2 = q2'\<close> \<open>q = Inl (q1',q2')\<close> by auto
        ultimately have "shift_Inl ?t \<in> transitions S"
          using \<open>(\<forall>t'\<in> transitions ?C. t_source t' = q \<and> t_input t' = t_input t \<longrightarrow> t' \<in> transitions S)\<close> \<open>t_input t1 = t_input t\<close> by auto

        
        have "case t_target (shift_Inl ?t) of Inl (q1', q2') \<Rightarrow> \<exists>k. r_distinguishable_k M q1' q2' k | Inr qr \<Rightarrow> True"
          using reachable_state.IH(2)[OF \<open>shift_Inl ?t \<in> transitions S\<close> \<open>t_source (shift_Inl ?t) = q\<close>] by (cases q; auto)
        moreover have "t_target (shift_Inl ?t) = Inl (t_target t1, t_target t2)" 
          by auto
        ultimately show "\<exists>k. r_distinguishable_k M (t_target t1) (t_target t2) k"
          by auto
      qed

      
      let ?hs = "{(t1,t2) | t1 t2 . t1 \<in> transitions M \<and> t2 \<in> transitions M \<and> t_source t1 = q1' \<and> t_source t2 = q2' \<and> t_input t1 = t_input t \<and> t_input t2 = t_input t \<and> t_output t1 = t_output t2}"
      have "finite ?hs"
      proof -
        have "?hs \<subseteq> (transitions M \<times> transitions M)" by blast
        moreover have "finite (transitions M \<times> transitions M)" using fsm_transitions_finite by blast
        ultimately show ?thesis
          by (simp add: finite_subset) 
      qed
      obtain fk where fk_def : "\<And> tt . tt \<in> ?hs \<Longrightarrow> r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) (fk tt)"
      proof 
        let ?fk = "\<lambda> tt . SOME k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k"
        show "\<And> tt . tt \<in> ?hs \<Longrightarrow> r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) (?fk tt)"
        proof -
          fix tt assume "tt \<in> ?hs"
          then have "(fst tt) \<in> transitions M \<and> (snd tt) \<in> transitions M \<and> t_source (fst tt) = q1' \<and> t_source (snd tt) = q2' \<and> t_input (fst tt) = t_input t \<and> t_input (snd tt) = t_input t \<and> t_output (fst tt) = t_output (snd tt)"
            by force 
          then have "\<exists> k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k"
            using * by blast
          then show "r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) (?fk tt)"
            by (simp add: someI_ex)
        qed
      qed

      let ?k = "Max (image fk ?hs)"
      have "\<And> t1 t2 . t1 \<in> transitions M \<Longrightarrow> t2 \<in> transitions M \<Longrightarrow> t_source t1 = q1' \<Longrightarrow> t_source t2 = q2' \<Longrightarrow> t_input t1 = t_input t \<Longrightarrow> t_input t2 = t_input t \<Longrightarrow> t_output t1 = t_output t2 \<Longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) ?k"
      proof -
        fix t1 t2 assume "t1 \<in> transitions M" 
                     and "t2 \<in> transitions M" 
                     and "t_source t1 = q1'" 
                     and "t_source t2 = q2'" 
                     and "t_input t1 = t_input t" 
                     and "t_input t2 = t_input t" 
                     and "t_output t1 = t_output t2"   
        then have "(t1,t2) \<in> ?hs"
          by force
        then have "r_distinguishable_k M (t_target t1) (t_target t2) (fk (t1,t2))"
          using fk_def by force
        have "fk (t1,t2) \<le> ?k"
          using \<open>(t1,t2) \<in> ?hs\<close> \<open>finite ?hs\<close> by auto
        show "r_distinguishable_k M (t_target t1) (t_target t2) ?k" 
          using r_distinguishable_k_by_larger[OF \<open>r_distinguishable_k M (t_target t1) (t_target t2) (fk (t1,t2))\<close> \<open>fk (t1,t2) \<le> ?k\<close>] by assumption
      qed


      then have "r_distinguishable_k M q1' q2' (Suc ?k)"
        unfolding r_distinguishable_k.simps 
        using \<open>t_input t \<in> (inputs M)\<close> by blast
      then show "?Prop q"
        using \<open>q = Inl (q1',q2')\<close>
        by (metis (no_types, lifting) case_prodI old.sum.simps(5)) 
    qed
  qed

  moreover have "Inl (q1,q2) \<in> states S"
    using \<open>is_submachine S ?C\<close> canonical_separator_simps(1)[OF assms(2,3)] fsm_initial[of S] by auto
  ultimately show "\<exists>k. r_distinguishable_k M q1 q2 k"
    using reachable_states_initial[of S] using is_state_separator_from_canonical_separator_initial[OF assms(1-3)] by auto 
qed

end