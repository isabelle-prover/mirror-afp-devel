(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

subsubsection "Flat Aux via Sloped-Language Automaton"

theory Flat_Aux_SLA
  imports Flat_Aux
begin

lemma InfiniteDescentI:"(\<And>nds. alw (holds2 edge) nds \<Longrightarrow> Ex (descentIpath nds)) \<Longrightarrow> InfiniteDescent"
  unfolding SLA_Criterion Paut\<^sub>R_lang Rst_correct[symmetric] 
  using ipath_def Taut\<^sub>R_lang_in by auto


lemma "InfiniteDescent"
  (*SLA Criterion*)
proof(rule InfiniteDescentI)   
    fix x 
    assume "alw (holds2 edge) x" 
    hence edge_always:"\<And>i. edge (x !! i) (x !! Suc i)"
      and Node_always:"\<And>i. (x !! i) \<in> Node" 
    using alw_nodes
    unfolding alw_holds2_iff_snth alw_holdsS_iff_snth by auto

  have flat_trans_is_aux:"\<And>i. x !! i = Flat \<Longrightarrow> stl x !! i = Aux" 
    subgoal for i using edge_always[of i] by (auto) .

  (*if at flat choose 1, since both (1,1,decr) and (1,2,decr) for transitions to aux
    Now, there are two cases, either:
         we eventually return to flat from aux, so we choose the later, pos = 2
                  i.e. we want (2,2,Main) for any self loop
                       upon a transition back to flat we choose (2,1,Main)
         or, we are forever in aux, so we choose (1,1,decr) transition, similarly for self loops
      *)
  define Pss::"node stream \<Rightarrow> nat \<Rightarrow> nat" where
    "Pss = (\<lambda>x n. (if x !! n = Flat then 0 else 1))"


  define Ps where Ps:"Ps = fToStream (Pss x)"
  note Ps_defs = Ps[unfolded Pss_def fToStream_def]
    (*now we use this stream of positions*)

  show "Ex (descentIpath x)"
  (*cases: 
        (1) Flat occurs infinitely often  - use Ps
        (2) Flat occurs finitely often
            \<longrightarrow> either:
              (2.1) Always Aux - use stream of 1's
              (2.2) There is an existence of some final Flat, followed by an infinite stream of aux
                               - use Ps up until final flat, then use stream of 1's
              *)
  proof(cases "infs (\<lambda>x. x = Flat) x")
    case True

    show ?thesis
      apply(rule exI[of _ Ps], unfold descentIpath_iff_snth)
      apply(rule exI[of _ 0], intro conjI allI impI)
      (*Always a valid transition*)
      subgoal for j apply(cases "x !! j")
          subgoal apply(cases "x !! Suc j")
            using edge_always[of j] by (auto simp: RR_defs Ps_defs) 
          by(cases "x !! Suc j",auto simp: RR_defs Ps_defs) 
      (*A decrease always occurs, namely flat \<rightarrow> aux*)
        using True flat_trans_is_aux unfolding alw_ev_holds_iff_snth
        by(auto simp: RR_defs Ps_defs)
    next
      case False
      then consider (alw_aux) "alw (holds (\<lambda>x. x = Aux)) x"
                  | (some_flat) "\<exists>i. \<forall>k > i. (x !! i) = Flat \<and> (x !! k) = Aux"
        apply-by(drule fins_imp, auto)

      thus ?thesis proof(cases)
        case alw_aux
        hence alw_aux:"\<And>i. x !! i = Aux"  unfolding alw_holds_iff_snth by auto
        also have alw_aux':"\<And>i. stl x !! i = Aux" subgoal for i using calculation[of "Suc i"] by auto .

        show ?thesis
          apply(rule exI[of _ "sconst 0"], unfold descentIpath_iff_snth)
          apply(rule exI[of _ 0], intro conjI allI impI)
          using alw_aux alw_aux' by auto
      next
        case some_flat
        then obtain i where i:"\<forall>n>i. x !! n = Aux" "x !! i = Flat" by blast
  
        hence always_aux:"\<And>j. j\<ge>Suc 0 \<Longrightarrow> x !! (i + j) = Aux"
                         "\<And>j. j\<ge>Suc 0 \<Longrightarrow> stl x !! (i + j) = Aux" 
          by (auto,metis less_add_Suc1 stl_Suc_eq)
      
        have flat_aux_not_i_le:
          "\<And>j. x !! j = Flat \<Longrightarrow> x !! Suc j = Aux \<Longrightarrow> j \<noteq> i \<Longrightarrow> Suc j < i \<and> j < i"
          by (metis Suc_lessI i(1,2) linorder_neqE_nat node.simps(2))
        
        have aux_flat_not_i_le:
          "\<And>j. x !! j = Aux \<Longrightarrow> x !! Suc j = Flat \<Longrightarrow> j < i"
          by (metis i(1) node.simps(2) not_less_eq)
      
        have aux_ngr:"\<And>j. x !! j = Aux \<Longrightarrow> x !! Suc j = Aux \<Longrightarrow> \<not> i < j \<Longrightarrow> Suc j < i \<and> j < i" 
          by (metis Suc_lessI i(2) linorder_neqE_nat node.distinct(1))
          
      
        define newPs where newPs:"newPs = stake i Ps @- sconst 0"
        note newPs_defs = newPs[unfolded Ps_defs]
      
        hence always_1:"\<And>j. j\<ge>Suc 0 \<Longrightarrow> newPs !! (i + j) = 0"
                       "\<And>j. j\<ge>Suc 0 \<Longrightarrow> stl newPs !! (i + j) = 0" by auto
      
        also have newPs_le:"\<And>j. j < i \<Longrightarrow> newPs !! j = (stake i Ps) ! j"
          by (simp add: newPs)
      
        have newPs_gr:"\<And>j. i < j \<Longrightarrow> newPs !! j = 0" unfolding newPs by auto
      
        show ?thesis
          apply(rule exI[of _ newPs], unfold descentIpath_iff_snth)
          apply(rule exI[of _ "Suc 0"], intro conjI allI impI)
          (*there's always a sound transition either maintain or decrease*)
          (*source: flat*) 
          subgoal for j apply(cases "x !! j")
              subgoal apply(cases "x !! Suc j")
                (*no valid edge flat \<rightarrow> flat*)
                subgoal using edge_always[of j] by auto
                (*either we are at flat \<rightarrow> aux, s.t. aux\<^sup>\<infinity> ...*)
                apply(cases "j = i")
                subgoal by (auto simp: RR_defs newPs_defs)
                (*or we are still going between flat and aux*)
                apply(frule flat_aux_not_i_le[of j], safe)
                apply(frule newPs_le[of j], frule newPs_le[of "Suc j"])
                using nth_map_upt by (auto simp: RR_defs Ps_defs)
              (*source: aux*) 
              subgoal apply(cases "x !! Suc j")
                (*we are transitioning back aux \<rightarrow> flat*)
                subgoal apply(frule aux_flat_not_i_le, safe)
                  apply(frule newPs_le[of j], drule Suc_disj)
                  apply (erule disjE, frule newPs_le[of "Suc j"])
                  subgoal using nth_map_upt  by (auto simp: RR_defs Ps_defs)
                  subgoal by (auto simp: RR_defs newPs_defs) . 
                (*self loop at aux*)
                apply(cases "i<j")
                (*in the infinite tail of aux*)
                subgoal using newPs_gr newPs_gr[of "Suc j"] by auto
                (*a flat transition is still to come...*)
                subgoal apply(frule aux_ngr, safe)
                  apply(frule newPs_le[of j], frule newPs_le[of "Suc j"])
                  using nth_map_upt by (auto simp: RR_defs Ps_defs) . .
      
            (*we obtain infinite decreases if we are above i... (i+j)*)
            subgoal for j apply(rule exI[of _ "i + j"]) using always_aux always_1 by (auto simp: RR_defs) .

      qed
        
    qed
  qed 


end
