(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

subsection "Flat Cycles Criterion"
theory Flat_Cycles_Criterion
imports "../Sloped_Graphs"
begin


(* 1. THE FLAT CYCLE CRITERION *)

context Sloped_Graph
begin

definition FlatEdges::"('node \<times> 'node) set" where
"FlatEdges \<equiv> {(u, v). edge u v \<and> (\<forall>p \<in> PosOf u. \<forall>q \<in> PosOf v. \<not>RR (u,p) (v,q) Decr)}"


(*Any edge in this set is not decreasing*)
lemma FlatEdges_no_Decr:"(u,v) \<in> FlatEdges \<Longrightarrow> \<not> RR (u,p) (v,q) Decr"
  unfolding FlatEdges_def
  apply(rule notI, frule RR_PosOf, safe)
  apply(drule bspec[of "PosOf u" "\<lambda>p. \<forall>q\<in>PosOf v.
          \<not>RR (u, p) (v, q) Decr" p], simp)
  apply(drule bspec[of "PosOf v" _ q], simp)
  using RR_SlopeRels[of u v, unfolded SlopedRels_def]
  by auto


(* A FlatCycle exists if there is a subset which is a cycle and every edge is flat *)
definition FlatCycle :: bool where
  "FlatCycle \<equiv> \<exists>nds. (\<forall>i < length nds - 1. (nds ! i, nds ! (Suc i)) \<in> FlatEdges) \<and> cycleG nds"

lemma FlatCycle_properties:"FlatCycle \<Longrightarrow> \<exists>xs. cycleG xs \<and> (\<forall>i < length xs - 1.  \<forall>p q. \<not> RR (xs!i,p) (xs!(i+1),q) Decr)"
  apply(unfold FlatCycle_def, erule exE)
  subgoal for nds apply(intro exI[of _ nds] conjI allI impI)
    subgoal by auto
    subgoal for i apply(elim conjE allE[of _ i] impE, simp)
      using FlatEdges_no_Decr[of "nds ! i" "nds ! Suc i"] by auto . .

(*This is in particular the cycle obtained from the definition -(srepeat (butlast xs)), but this property is enough*)
lemma FlatCycle_imp_flat_ipath:
  assumes "FlatCycle"
  shows "\<exists>S. ipath S \<and> (\<forall>i p q. \<not> RR (S !! i, p) (S !! (Suc i), q) Decr)"
proof -
  obtain xs where cyc: "cycleG xs" 
    and no_decr_finite: "\<forall>i < length xs - 1. \<forall>p q. \<not> RR (xs!i,p) (xs!(i+1),q) Decr"
    using FlatCycle_properties[OF assms] by blast

  (* Let ys be the non-repeating part of the cycle *)
  let ?ys = "butlast xs"
  let ?S = "srepeat ?ys"
  
  (* Basic properties of cycleG imply xs is not empty and hd xs = last xs *)
  have xs_nemp:"xs \<noteq> []" using cyc unfolding cycleG_def  by auto
  have xs_len:"length xs \<ge> 2" using cyc unfolding cycleG_def by (simp add: path_length_ge2)
  have len_pos: "length ?ys > 0" 
    using xs_nemp cyc  
    by (meson Graph.cycleG_def bot_nat_0.not_eq_extremum length_0_conv pathG_butlast_not_nil)

  have ipaths:"ipath ?S"
    apply (unfold ipath_def, intro allI conjI)
    subgoal using cyc by (meson ipath_def cycle_srepeat_ipath)
    subgoal using cyc cycle_srepeat_ipath ipath_def by auto . 

  have no_decr_stream: "\<forall>i p q. \<not> RR (?S !! i, p) (?S !! (Suc i), q) Decr"
  proof (intro allI)
    fix i p q
    let ?n = "length ?ys"
    let ?k = "i mod ?n"

    have wrap:"i mod (length xs - Suc 0) = length xs - Suc (Suc 0) \<Longrightarrow> Suc i  mod (length xs - Suc 0) = 0" 
      by (metis One_nat_def Suc_pred' diff_Suc_eq_diff_pred len_pos
          length_butlast mod_Suc)


    have len_le:"length xs - Suc (Suc 0) < length xs - Suc 0" using xs_len by fastforce

    have butlast_wrap:"butlast xs ! 0 = xs ! Suc (length xs - Suc (Suc 0))"
      using cyc xs_len last_conv_nth[OF xs_nemp] unfolding cycleG_def 
      by (metis One_nat_def Suc_diff_Suc Suc_le_lessD cyc cycle_iff_nth len_pos
          nth_butlast numeral_2_eq_2)


    
    (* The edge in the stream corresponds to an edge in the finite list xs *)
    (* Case 1: The index is within the list body (not the wraparound) *)
    (* Case 2: The index is the wraparound (last element to first) *)
    have cases_mod:"i mod length (butlast xs) = length (butlast xs) - 1 \<or> i mod length (butlast xs) < length (butlast xs) - 1"
      by (metis Suc_diff_1 len_pos mod_less_divisor nat_cases
          not_less_eq)


    have "\<not> RR (?ys ! ?k, p) (?ys ! ((Suc i) mod ?n), q) Decr"
    using no_decr_finite cases_mod
    apply-apply(erule disjE)
      (*edge case, the wrap around*)
      subgoal apply(elim allE[of _ "length xs - Suc (Suc 0)"] impE)
        subgoal using xs_len by auto
        subgoal apply(erule allE[of _ p], erule allE[of _ q])
          using nth_butlast[of "length xs - Suc (Suc 0)" xs] by (simp add: len_le butlast_wrap wrap) .
      (*trivial case*)
      subgoal apply(erule allE[of _ "i mod length (butlast xs)"])
        by (simp,metis One_nat_def len_le len_pos length_butlast mod_Suc
            mod_less_divisor not_less_eq nth_butlast) .
      
    thus "\<not> RR (?S !! i, p) (?S !! (Suc i), q) Decr"
      using len_pos by force
  qed
  show ?thesis 
    using ipaths no_decr_stream by blast
qed

lemma FlatCycleE:"FlatCycle \<Longrightarrow> (\<And>xs. ipath xs \<Longrightarrow> (\<forall>i p q. \<not> RR (xs!! i,p) (xs!!(i+1),q) Decr) \<Longrightarrow> P) \<Longrightarrow> P"
  apply(drule FlatCycle_imp_flat_ipath)
  using cycle_srepeat_ipath by auto

lemma notFlatCycleI:"
   (\<And>nds. \<forall>i<length nds - 1. (nds ! i, nds ! Suc i) \<in> FlatEdges \<Longrightarrow>
           cycleG nds \<Longrightarrow> HOL.False) \<Longrightarrow> \<not>FlatCycle"
  by(unfold FlatCycle_def, rule notI, elim exE conjE, assumption)

lemma notFlatCycleI':"
   (\<And>nds. pathG nds \<Longrightarrow> 
           \<forall>i<length nds - 1. (nds ! i, nds ! Suc i) \<in> FlatEdges \<Longrightarrow>
           hd nds = last nds \<Longrightarrow> HOL.False) \<Longrightarrow> \<not>FlatCycle"
  by(unfold FlatCycle_def cycleG_def, rule notI, elim exE conjE, assumption)


theorem Flat_Cycles_Criterion:"FlatCycle \<Longrightarrow> \<not>InfiniteDescent"
  apply(rule notI, erule FlatCycleE)
  unfolding InfiniteDescent_def
  subgoal for xs apply(erule allE[of _ "xs"], simp)
  unfolding descentIpath_iff_snth by auto .

end (* context Heighted_Graph *)

end 
