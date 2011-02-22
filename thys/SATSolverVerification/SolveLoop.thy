(*    Title:              SatSolverVerification/SolveLoop.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

theory SolveLoop
imports UnitPropagate ConflictAnalysis Decide
begin


(******************************************************************************)
(*          S O L V E   L O O P   B O D Y                                     *)
(******************************************************************************)

lemma soundnessForUNSAT:
assumes 
  "equivalentFormulae (F @ val2form M) F0"
  "formulaFalse F M"
shows
  "\<not> satisfiable F0"
proof-
  have "formulaEntailsValuation (F @ val2form M) M"
    using val2formIsEntailed[of "F" "M" "[]"]
    by simp
  moreover
  have "formulaFalse (F @ val2form M) M"
    using `formulaFalse F M`
    by (simp add: formulaFalseAppend)
  ultimately
  have "\<not> satisfiable (F @ val2form M)"
    using formulaFalseInEntailedValuationIsUnsatisfiable[of "F @ val2form M" "M"]
    by simp
  thus ?thesis
    using `equivalentFormulae (F @ val2form M) F0`
    by (simp add: satisfiableEquivalent)
qed

lemma soundnessForSat:
  fixes F0 :: Formula and F :: Formula and M::LiteralTrail
  assumes "vars F0 \<subseteq> Vbl" and "InvariantVarsF F F0 Vbl" and "InvariantConsistent M" and "InvariantEquivalentZL F M F0" and
  "\<not> formulaFalse F (elements M)" and "vars (elements M) \<supseteq> Vbl"
  shows "model (elements M) F0"
proof-
  from `InvariantConsistent M`
  have "consistent (elements M)"
    unfolding InvariantConsistent_def
    .
  moreover
  from `InvariantVarsF F F0 Vbl` 
  have "vars F \<subseteq> vars F0 \<union> Vbl"
    unfolding InvariantVarsF_def
    .
  with `vars F0 \<subseteq> Vbl` 
  have "vars F \<subseteq> Vbl"
    by auto
  with `vars (elements M) \<supseteq> Vbl`
  have "vars F \<subseteq> vars (elements M)"
    by simp
  hence "formulaTrue F (elements M) \<or> formulaFalse F (elements M)"
    by (simp add:totalValuationForFormulaDefinesItsValue)
  with `\<not> formulaFalse F (elements M)`
  have "formulaTrue F (elements M)"
    by simp
  ultimately
  have "model (elements M) F"
    by simp
  moreover
  obtain s
    where "elements (prefixToLevel 0 M) @ s = elements M"
    using isPrefixPrefixToLevel[of "0" "M"]
    using isPrefixElements[of "prefixToLevel 0 M" "M"]
    unfolding isPrefix_def
    by auto
  hence "elements M = elements (prefixToLevel 0 M) @ s"
    by (rule sym)
  hence "formulaTrue (val2form (elements (prefixToLevel 0 M))) (elements M)"
    using val2formFormulaTrue[of "elements (prefixToLevel 0 M)" "elements M"]
    by auto
  hence "model (elements M) (val2form (elements (prefixToLevel 0 M)))"
    using `consistent (elements M)`
    by simp
  ultimately
  show ?thesis
    using `InvariantEquivalentZL F M F0`
    unfolding InvariantEquivalentZL_def
    unfolding equivalentFormulae_def
    using formulaTrueAppend[of "F" "val2form (elements (prefixToLevel 0 M))" "elements M"]
    by auto
qed

definition
"satFlagLessState = {(state1::State, state2::State). (getSATFlag state1) \<noteq> UNDEF \<and> (getSATFlag state2) = UNDEF}"


lemma wellFoundedSatFlagLessState:
  shows "wf satFlagLessState"
  unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix state::State and Q::"State set"
      assume "state \<in> Q"
      have "\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
      proof (cases "\<exists> stateDef \<in> Q. (getSATFlag stateDef) \<noteq> UNDEF")
        case True
        then obtain stateDef where "stateDef \<in> Q" "(getSATFlag stateDef) \<noteq> UNDEF"
          by auto
        have "\<forall>state'. (state', stateDef) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
        proof
          fix state'
          show "(state', stateDef) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
          proof
            assume "(state', stateDef) \<in> satFlagLessState"
            hence "getSATFlag stateDef = UNDEF"
              unfolding satFlagLessState_def
              by auto
            with `getSATFlag stateDef \<noteq> UNDEF` have False
              by simp
            thus "state' \<notin> Q"
              by simp
          qed
        qed
        with `stateDef \<in> Q`
        show ?thesis
          by auto
      next
        case False
        have "\<forall>state'. (state', state) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
        proof
          fix state'
          show "(state', state) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
          proof
            assume "(state', state) \<in> satFlagLessState"
            hence "getSATFlag state' \<noteq> UNDEF"
              unfolding satFlagLessState_def
              by simp
            with False
            show "state' \<notin> Q"
              by auto
          qed
        qed
        with `state \<in> Q` 
        show ?thesis
          by auto
      qed
    }
    thus ?thesis
      by auto
  qed
qed

definition
"lexLessState1 Vbl = {(state1::State, state2::State). 
     getSATFlag state1 = UNDEF \<and> getSATFlag state2 = UNDEF \<and>
     (getM state1, getM state2) \<in> lexLessRestricted Vbl
}"

lemma wellFoundedLexLessState1:
assumes
  "finite Vbl"
shows
  "wf (lexLessState1 Vbl)"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q :: "State set" and state :: State
      assume "state \<in> Q"
      let ?Q1 = "{M::LiteralTrail. \<exists> state. state \<in> Q \<and> getSATFlag state = UNDEF \<and> (getM state) = M}"
      have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q)"
      proof (cases "?Q1 \<noteq> {}")
        case True
        then obtain M::LiteralTrail
          where "M \<in> ?Q1"
          by auto
        then obtain MMin::LiteralTrail
          where "MMin \<in> ?Q1" "\<forall>M'. (M', MMin) \<in> lexLessRestricted Vbl \<longrightarrow> M' \<notin> ?Q1"
          using wfLexLessRestricted[of "Vbl"] `finite Vbl`
          unfolding wf_eq_minimal
          apply simp
          apply (erule_tac x="?Q1" in allE)
          by auto
        from `MMin \<in> ?Q1` obtain stateMin
          where "stateMin \<in> Q" "(getM stateMin) = MMin" "getSATFlag stateMin = UNDEF"
          by auto
        have "\<forall>state'. (state', stateMin) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
        proof
          fix state'
          show "(state', stateMin) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
          proof
            assume "(state', stateMin) \<in> lexLessState1 Vbl"
            hence "getSATFlag state' = UNDEF" "(getM state', getM stateMin) \<in> lexLessRestricted Vbl"
              unfolding lexLessState1_def
              by auto
            hence "getM state' \<notin> ?Q1"
              using `\<forall>M'. (M', MMin) \<in> lexLessRestricted Vbl \<longrightarrow> M' \<notin> ?Q1`
              using `(getM stateMin) = MMin`
              by auto
            thus "state' \<notin> Q"
              using `getSATFlag state' = UNDEF`
              by auto
          qed
        qed
        thus ?thesis
          using `stateMin \<in> Q`
          by auto
      next
        case False
        have "\<forall>state'. (state', state) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
        proof
          fix state'
          show "(state', state) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
          proof
            assume "(state', state) \<in> lexLessState1 Vbl"
            hence "getSATFlag state = UNDEF"
              unfolding lexLessState1_def
              by simp
            hence "(getM state) \<in> ?Q1"
              using `state \<in> Q`
              by auto
            hence False
              using False
              by auto
            thus "state' \<notin> Q"
              by simp
          qed
        qed
        thus ?thesis
          using `state \<in> Q`
          by auto
      qed
    }
    thus ?thesis
      by auto
  qed
qed

definition 
"terminationLessState1 Vbl = {(state1::State, state2::State). 
  (state1, state2) \<in> satFlagLessState \<or> 
  (state1, state2) \<in> lexLessState1 Vbl}"

lemma wellFoundedTerminationLessState1:
  assumes "finite Vbl"
  shows "wf (terminationLessState1 Vbl)"
unfolding wf_eq_minimal
proof-
  show "\<forall> Q state. state \<in> Q \<longrightarrow> (\<exists> stateMin \<in> Q. \<forall> state'. (state', stateMin) \<in> terminationLessState1 Vbl \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q::"State set"
      fix state::"State"
      assume "state \<in> Q"
      have "\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> terminationLessState1 Vbl \<longrightarrow> state' \<notin> Q"
      proof-
        obtain state0
          where "state0 \<in> Q" "\<forall>state'. (state', state0) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q"
          using wellFoundedSatFlagLessState
          unfolding wf_eq_minimal
          using `state \<in> Q`
          by auto
        show ?thesis
        proof (cases "getSATFlag state0 = UNDEF")
          case False
          hence "\<forall>state'. (state', state0) \<in> terminationLessState1 Vbl \<longrightarrow> state' \<notin> Q"
            using `\<forall>state'. (state', state0) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q`
            unfolding terminationLessState1_def
            unfolding lexLessState1_def
            by simp
          thus ?thesis
            using `state0 \<in> Q`
            by auto
        next
          case True
          then obtain state1
            where "state1 \<in> Q" "\<forall>state'. (state', state1) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q"
            using `finite Vbl`
            using `state \<in> Q`
            using wellFoundedLexLessState1[of "Vbl"]
            unfolding wf_eq_minimal
            by auto

          have "\<forall>state'. (state', state1) \<in> terminationLessState1 Vbl \<longrightarrow> state' \<notin> Q"
            using `\<forall>state'. (state', state1) \<in> lexLessState1 Vbl \<longrightarrow> state' \<notin> Q`
            unfolding terminationLessState1_def
            using `\<forall>state'. (state', state0) \<in> satFlagLessState \<longrightarrow> state' \<notin> Q`
            using True
            unfolding satFlagLessState_def
            by simp
          thus ?thesis
            using `state1 \<in> Q`
            by auto
        qed
      qed
    }
    thus ?thesis
      by auto
  qed
qed

lemma transTerminationLessState1:
  "trans (terminationLessState1 Vbl)"
proof-
  {
    fix x::State and y::State and z::State
    assume "(x, y) \<in> terminationLessState1 Vbl" "(y, z) \<in> terminationLessState1 Vbl"
    have "(x, z) \<in> terminationLessState1 Vbl"
    proof (cases "(x, y) \<in> satFlagLessState")
      case True
      hence "getSATFlag x \<noteq> UNDEF" "getSATFlag y = UNDEF"
        unfolding satFlagLessState_def
        by auto
      hence "getSATFlag z = UNDEF"
        using `(y, z) \<in> terminationLessState1 Vbl`
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        unfolding lexLessState1_def
        by auto
      thus ?thesis
        using `getSATFlag x \<noteq> UNDEF`
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        by simp
    next
      case False
      with `(x, y) \<in> terminationLessState1 Vbl`
      have "getSATFlag x = UNDEF" "getSATFlag y = UNDEF" "(getM x, getM y) \<in> lexLessRestricted Vbl"
        unfolding terminationLessState1_def
        unfolding lexLessState1_def
        by auto
      hence "getSATFlag z = UNDEF" "(getM y, getM z) \<in> lexLessRestricted Vbl"
        using `(y, z) \<in> terminationLessState1 Vbl`
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        unfolding lexLessState1_def
        by auto
      thus ?thesis
        using `getSATFlag x = UNDEF` 
        using `(getM x, getM y) \<in> lexLessRestricted Vbl`
        using transLexLessRestricted[of "Vbl"]
        unfolding trans_def
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        unfolding lexLessState1_def
        by blast
    qed
  }
  thus ?thesis
    unfolding trans_def
    by blast
qed

lemma transTerminationLessState1I:
assumes 
  "(x, y) \<in> terminationLessState1 Vbl"
  "(y, z) \<in> terminationLessState1 Vbl"
shows
  "(x, z) \<in> terminationLessState1 Vbl"
using assms
using transTerminationLessState1[of "Vbl"]
unfolding trans_def
by blast


lemma TerminationLessAfterExhaustiveUnitPropagate:
assumes
  "exhaustiveUnitPropagate_dom state"
  "InvariantUniq (getM state)"
  "InvariantConsistent (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantUniqQ (getQ state)"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
  "finite Vbl"
  "getSATFlag state = UNDEF"
shows
"let state' = exhaustiveUnitPropagate state in
    state' = state \<or> (state', state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
using assms
proof (induct state rule: exhaustiveUnitPropagate_dom.induct)
  case (step state')
  note ih = this
  show ?case
  proof (cases "(getConflictFlag state') \<or> (getQ state') = []")
    case True
    with exhaustiveUnitPropagate.simps[of "state'"]
    have "exhaustiveUnitPropagate state' = state'"
      by simp
    thus ?thesis
      using True
      by (simp add: Let_def)
  next
    case False
    let ?state'' = "applyUnitPropagate state'"

    have "exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''"
      using exhaustiveUnitPropagate.simps[of "state'"]
      using False
      by simp
    have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
      using ih
      using WatchInvariantsAfterAssertLiteral[of "state'" "hd (getQ state')" "False"]
      unfolding applyUnitPropagate_def
      by (auto simp add: Let_def)
    moreover
    have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')"
      using ih
      using InvariantWatchCharacterizationAfterApplyUnitPropagate[of "state'"]
      unfolding InvariantQCharacterization_def
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantQCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')"
      using ih
      using InvariantConflictFlagCharacterizationAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniqQ (getQ ?state'')"
      using ih
      using InvariantUniqQAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantConsistent (getM ?state'')"
      using ih
      using InvariantConsistentAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantUniq (getM ?state'')"
      using ih
      using InvariantUniqAfterApplyUnitPropagate[of "state'"]
      using False
      by (simp add: Let_def)
    moreover
    have "InvariantVarsM (getM ?state'') F0 Vbl" "InvariantVarsQ (getQ ?state'') F0 Vbl"
      using ih
      using False
      using InvariantsVarsAfterApplyUnitPropagate[of "state'" "F0" "Vbl"]
      by (auto simp add: Let_def)
    moreover
    have "InvariantVarsF (getF ?state'') F0 Vbl"
      unfolding applyUnitPropagate_def
      using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
      using ih
      by (simp add: Let_def)
    moreover
    have "getSATFlag ?state'' = UNDEF"
      unfolding applyUnitPropagate_def
      using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state')`
      using `InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state')`
      using `getSATFlag state' = UNDEF`
      using assertLiteralEffect[of "state'" "hd (getQ state')" "False"]
      by (simp add: Let_def)
    ultimately
    have *: "exhaustiveUnitPropagate state' = applyUnitPropagate state' \<or> 
            (exhaustiveUnitPropagate state', applyUnitPropagate state') \<in> terminationLessState1 (vars F0 \<union> Vbl)"
      using ih
      using False
      using `exhaustiveUnitPropagate state' = exhaustiveUnitPropagate ?state''`
      by (simp add: Let_def)
    moreover
    have "(?state'', state') \<in> terminationLessState1 (vars F0 \<union> Vbl)"
      using applyUnitPropagateEffect[of "state'"]
      using lexLessAppend[of "[(hd (getQ state'), False)]" "getM state'"]
      using False
      using `InvariantUniq (getM state')`
      using `InvariantConsistent (getM state')`
      using `InvariantVarsM (getM state') F0 Vbl`
      using `InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state')`
      using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state')`
      using `InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state')`
      using `InvariantUniq (getM ?state'')`
      using `InvariantConsistent (getM ?state'')`
      using `InvariantVarsM (getM ?state'') F0 Vbl`
      using `getSATFlag state' = UNDEF`
      using `getSATFlag ?state'' = UNDEF`
      unfolding terminationLessState1_def
      unfolding lexLessState1_def
      unfolding lexLessRestricted_def
      unfolding InvariantUniq_def
      unfolding InvariantConsistent_def
      unfolding InvariantVarsM_def
      by (auto simp add: Let_def)
    ultimately
    show ?thesis
      using transTerminationLessState1I[of "exhaustiveUnitPropagate state'" "applyUnitPropagate state'" "vars F0 \<union> Vbl" "state'"]
      by (auto simp add: Let_def)
  qed
qed


lemma InvariantsAfterSolveLoopBody:
assumes
  "getSATFlag state = UNDEF"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantUniqQ (getQ state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)" and
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)" and
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))" and
  "InvariantEquivalentZL (getF state) (getM state) F0'" and
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)" and
  "finite Vbl"
  "vars F0' \<subseteq> vars F0"
  "vars F0 \<subseteq> Vbl"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
shows
  "let state' = solve_loop_body state Vbl in
    (InvariantConsistent (getM state') \<and> 
     InvariantUniq (getM state') \<and> 
     InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantWatchCharacterization (getF state') (getWatch1 state') (getWatch2 state') (getM state') \<and> 
     InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state') \<and> 
     InvariantWatchListsUniq (getWatchList state') \<and> 
     InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state') \<and> 
     InvariantConflictFlagCharacterization (getConflictFlag state') (getF state') (getM state') \<and> 
     InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state') \<and> 
     InvariantUniqQ (getQ state')) \<and> 
    (InvariantNoDecisionsWhenConflict (getF state') (getM state') (currentLevel (getM state')) \<and> 
     InvariantNoDecisionsWhenUnit (getF state') (getM state') (currentLevel (getM state'))) \<and>
     InvariantEquivalentZL (getF state') (getM state') F0' \<and>  
     InvariantGetReasonIsReason (getReason state') (getF state') (getM state') (set (getQ state')) \<and> 
     InvariantVarsM (getM state') F0 Vbl \<and> 
     InvariantVarsQ (getQ state') F0 Vbl \<and> 
     InvariantVarsF (getF state') F0 Vbl \<and> 
     (state', state) \<in> terminationLessState1 (vars F0 \<union> Vbl) \<and> 
    ((getSATFlag state' = FALSE \<longrightarrow> \<not> satisfiable F0') \<and> 
     (getSATFlag state' = TRUE  \<longrightarrow> satisfiable F0'))" 
     (is "let state' = solve_loop_body state Vbl in ?inv' state' \<and> ?inv'' state' \<and> _ ")
proof-
  let ?state_up = "exhaustiveUnitPropagate state"

  have "exhaustiveUnitPropagate_dom state"
    using exhaustiveUnitPropagateTermination[of "state" "F0" "Vbl"]
    using assms
    by simp

  have "?inv' ?state_up"
    using assms
    using `exhaustiveUnitPropagate_dom state`
    using InvariantsAfterExhaustiveUnitPropagate[of "state"]
    using InvariantConflictClauseCharacterizationAfterExhaustivePropagate[of "state"]
    by (simp add: Let_def)
  have "?inv'' ?state_up"
    using assms
    using `exhaustiveUnitPropagate_dom state`
    using InvariantsNoDecisionsWhenConflictNorUnitAfterExhaustivePropagate[of "state"]
    by (simp add: Let_def)
  have "InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'"
    using assms
    using `exhaustiveUnitPropagate_dom state`
    using InvariantEquivalentZLAfterExhaustiveUnitPropagate[of "state"]
    by (simp add: Let_def)
  have "InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up) (getM ?state_up) (set (getQ ?state_up))"
    using assms
    using `exhaustiveUnitPropagate_dom state`
    using InvariantGetReasonIsReasonAfterExhaustiveUnitPropagate[of "state"]
    by (simp add: Let_def)
  have "getSATFlag ?state_up = getSATFlag state"
    using exhaustiveUnitPropagatePreservedVariables[of "state"]
    using assms
    using `exhaustiveUnitPropagate_dom state`
    by (simp add: Let_def)
  have "getConflictFlag ?state_up \<or> getQ ?state_up = []"
    using conflictFlagOrQEmptyAfterExhaustiveUnitPropagate[of "state"]
    using `exhaustiveUnitPropagate_dom state`
    by (simp add: Let_def)
  have "InvariantVarsM (getM ?state_up) F0 Vbl" 
       "InvariantVarsQ (getQ ?state_up) F0 Vbl"
       "InvariantVarsF (getF ?state_up) F0 Vbl"
    using assms
    using `exhaustiveUnitPropagate_dom state`
    using InvariantsAfterExhaustiveUnitPropagate[of "state" "F0" "Vbl"]
    by (auto simp add: Let_def)

  have "?state_up = state \<or> (?state_up, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
    using assms
    using TerminationLessAfterExhaustiveUnitPropagate[of "state"]
    using `exhaustiveUnitPropagate_dom state`
    by (simp add: Let_def)
  
  show ?thesis
  proof(cases "getConflictFlag ?state_up")
    case True
    show ?thesis
    proof (cases "currentLevel (getM ?state_up) = 0")
      case True
      hence "prefixToLevel 0 (getM ?state_up) = (getM ?state_up)"
        using currentLevelZeroTrailEqualsItsPrefixToLevelZero[of "getM ?state_up"]
        by simp
      moreover
      have "formulaFalse (getF ?state_up) (elements (getM ?state_up))"
        using `getConflictFlag ?state_up`
        using `?inv' ?state_up`
        unfolding InvariantConflictFlagCharacterization_def
        by simp
      ultimately
      have "\<not> satisfiable F0'"
        using `InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'`
        unfolding InvariantEquivalentZL_def
        using soundnessForUNSAT[of "getF ?state_up" "elements (getM ?state_up)" "F0'"]
        by simp
      moreover
      let ?state' = "?state_up \<lparr> getSATFlag := FALSE \<rparr>"
      have "(?state', state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        using `getSATFlag state = UNDEF`
        by simp
      ultimately
      show ?thesis
        using `?inv' ?state_up`
        using `?inv'' ?state_up`
        using `InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'`
        using `InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up)  (getM ?state_up) (set (getQ ?state_up))`
        using `InvariantVarsM (getM ?state_up) F0 Vbl`
        using `InvariantVarsQ (getQ ?state_up) F0 Vbl`
        using `InvariantVarsF (getF ?state_up) F0 Vbl`
        using `getConflictFlag ?state_up`
        using `currentLevel (getM ?state_up) = 0`
        unfolding solve_loop_body_def
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof-
          (* APPLY CONFICT *)
        let ?state_c = "applyConflict ?state_up"

        have "?inv' ?state_c" 
          "?inv'' ?state_c"
          "getConflictFlag ?state_c"
          "InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'"
          "currentLevel (getM ?state_c) > 0"
          using `?inv' ?state_up` `?inv'' ?state_up`
          using `getConflictFlag ?state_up`
          using `InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'`
          using `currentLevel (getM ?state_up) \<noteq> 0`
          unfolding applyConflict_def
          unfolding setConflictAnalysisClause_def
          by (auto simp add: Let_def findLastAssertedLiteral_def countCurrentLevelLiterals_def)

        have "InvariantCFalse (getConflictFlag ?state_c) (getM ?state_c) (getC ?state_c)"
             "InvariantCEntailed (getConflictFlag ?state_c) F0' (getC ?state_c)"
             "InvariantClCharacterization (getCl ?state_c) (getC ?state_c) (getM ?state_c)"
             "InvariantCnCharacterization (getCn ?state_c) (getC ?state_c) (getM ?state_c)"
             "InvariantClCurrentLevel (getCl ?state_c) (getM ?state_c)"
             "InvariantUniqC (getC ?state_c)"
          using `getConflictFlag ?state_up`
          using `currentLevel (getM ?state_up) \<noteq> 0`
          using `?inv' ?state_up`
          using `?inv'' ?state_up`
          using `InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'`
          using InvariantsClAfterApplyConflict[of "?state_up"]
          by (auto simp only: Let_def)

        have "getSATFlag ?state_c = getSATFlag state"
          using `getSATFlag ?state_up = getSATFlag state`
          unfolding applyConflict_def
          unfolding setConflictAnalysisClause_def
          by (simp add: Let_def findLastAssertedLiteral_def countCurrentLevelLiterals_def)

        have "getReason ?state_c = getReason ?state_up"
          "getF ?state_c = getF ?state_up"
          "getM ?state_c = getM ?state_up"
          "getQ ?state_c = getQ ?state_up"
          unfolding applyConflict_def
          unfolding setConflictAnalysisClause_def
          by (auto simp add: Let_def findLastAssertedLiteral_def countCurrentLevelLiterals_def)
        hence "InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))"
          "InvariantVarsM (getM ?state_c) F0 Vbl" 
          "InvariantVarsQ (getQ ?state_c) F0 Vbl"
          "InvariantVarsF (getF ?state_c) F0 Vbl"         
          using `InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up) (getM ?state_up) (set (getQ ?state_up))`
          using `InvariantVarsM (getM ?state_up) F0 Vbl`
          using `InvariantVarsQ (getQ ?state_up) F0 Vbl`
          using `InvariantVarsF (getF ?state_up) F0 Vbl`
          by auto


        have "getM ?state_c = getM state \<or> (?state_c, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
          using `?state_up = state \<or> (?state_up, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)`
          using `getM ?state_c = getM ?state_up`
          using `getSATFlag ?state_c = getSATFlag state`
          using `InvariantUniq (getM state)`
          using `InvariantConsistent (getM state)`
          using `InvariantVarsM (getM state) F0 Vbl`
          using `?inv' ?state_up`
          using `InvariantVarsM (getM ?state_up) F0 Vbl`
          using `getSATFlag ?state_up = getSATFlag state`
          using `getSATFlag state = UNDEF`
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          unfolding InvariantVarsM_def
          unfolding terminationLessState1_def
          unfolding satFlagLessState_def
          unfolding lexLessState1_def
          unfolding lexLessRestricted_def
          by auto


          (*    APPLY EXPLAIN UIP    *)
          
        let ?state_euip = "applyExplainUIP ?state_c"
        let ?l' = "getCl ?state_euip"

        have "applyExplainUIP_dom ?state_c"
          using ApplyExplainUIPTermination[of "?state_c" "F0'"]
          using `getConflictFlag ?state_c`
          using `InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'`
          using `currentLevel (getM ?state_c) > 0`
          using `?inv' ?state_c`
          using `InvariantCFalse (getConflictFlag ?state_c) (getM ?state_c) (getC ?state_c)`
          using `InvariantCEntailed (getConflictFlag ?state_c) F0' (getC ?state_c)`
          using `InvariantClCharacterization (getCl ?state_c) (getC ?state_c) (getM ?state_c)`
          using `InvariantCnCharacterization (getCn ?state_c) (getC ?state_c) (getM ?state_c)`
          using `InvariantClCurrentLevel (getCl ?state_c) (getM ?state_c)`
          using `InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))`
          by simp
        
        
        have "?inv' ?state_euip" "?inv'' ?state_euip"
          using `?inv' ?state_c` `?inv'' ?state_c`
          using `applyExplainUIP_dom ?state_c`
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (auto simp add: Let_def)

        have "InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)"
          "InvariantCEntailed (getConflictFlag ?state_euip) F0' (getC ?state_euip)"
          "InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)"
          "InvariantCnCharacterization (getCn ?state_euip) (getC ?state_euip) (getM ?state_euip)"
          "InvariantClCurrentLevel (getCl ?state_euip) (getM ?state_euip)"
          "InvariantUniqC (getC ?state_euip)"
          using `?inv' ?state_c`
          using `InvariantCFalse (getConflictFlag ?state_c) (getM ?state_c) (getC ?state_c)`
          using `InvariantCEntailed (getConflictFlag ?state_c) F0' (getC ?state_c)`
          using `InvariantClCharacterization (getCl ?state_c) (getC ?state_c) (getM ?state_c)`
          using `InvariantCnCharacterization (getCn ?state_c) (getC ?state_c) (getM ?state_c)`
          using `InvariantClCurrentLevel (getCl ?state_c) (getM ?state_c)`
          using `InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'`
          using `InvariantUniqC (getC ?state_c)`
          using `getConflictFlag ?state_c`
          using `currentLevel (getM ?state_c) > 0`
          using `InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))`
          using `applyExplainUIP_dom ?state_c`
          using InvariantsClAfterExplainUIP[of "?state_c" "F0'"]
          by (auto simp only: Let_def)

        have "InvariantEquivalentZL (getF ?state_euip) (getM ?state_euip) F0'"
          using `InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'`
          using `applyExplainUIP_dom ?state_c`
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (simp only: Let_def)

        have "InvariantGetReasonIsReason (getReason ?state_euip) (getF ?state_euip) (getM ?state_euip) (set (getQ ?state_euip))"
          using `InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))`
          using `applyExplainUIP_dom ?state_c`
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (simp only: Let_def)

        have "getConflictFlag ?state_euip"
          using `getConflictFlag ?state_c`
          using `applyExplainUIP_dom ?state_c`
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (simp add: Let_def)

        hence "getSATFlag ?state_euip = getSATFlag state"
          using `getSATFlag ?state_c = getSATFlag state`
          using `applyExplainUIP_dom ?state_c`
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (simp add: Let_def)

        have "isUIP (opposite (getCl ?state_euip)) (getC ?state_euip) (getM ?state_euip)"
          using `applyExplainUIP_dom ?state_c`
          using `?inv' ?state_c`
          using `InvariantCFalse (getConflictFlag ?state_c) (getM ?state_c) (getC ?state_c)`
          using `InvariantCEntailed (getConflictFlag ?state_c) F0' (getC ?state_c)`
          using `InvariantClCharacterization (getCl ?state_c) (getC ?state_c) (getM ?state_c)`
          using `InvariantCnCharacterization (getCn ?state_c) (getC ?state_c) (getM ?state_c)`
          using `InvariantClCurrentLevel (getCl ?state_c) (getM ?state_c)`
          using `InvariantGetReasonIsReason (getReason ?state_c) (getF ?state_c) (getM ?state_c) (set (getQ ?state_c))`
          using `InvariantEquivalentZL (getF ?state_c) (getM ?state_c) F0'`
          using `getConflictFlag ?state_c`
          using `currentLevel (getM ?state_c) > 0`
          using isUIPApplyExplainUIP[of "?state_c"]
          by (simp add: Let_def)

        have "currentLevel (getM ?state_euip) > 0"
          using `applyExplainUIP_dom ?state_c`
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          using `currentLevel (getM ?state_c) > 0`
          by (simp add: Let_def)

        have "InvariantVarsM (getM ?state_euip) F0 Vbl" 
             "InvariantVarsQ (getQ ?state_euip) F0 Vbl"
             "InvariantVarsF (getF ?state_euip) F0 Vbl"
          using `InvariantVarsM (getM ?state_c) F0 Vbl`
          using `InvariantVarsQ (getQ ?state_c) F0 Vbl`
          using `InvariantVarsF (getF ?state_c) F0 Vbl`
          using `applyExplainUIP_dom ?state_c`
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          by (auto simp add: Let_def)

        have "getM ?state_euip = getM state \<or> (?state_euip, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
          using `getM ?state_c = getM state \<or> (?state_c, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)`
          using `applyExplainUIP_dom ?state_c`
          using ApplyExplainUIPPreservedVariables[of "?state_c"]
          unfolding terminationLessState1_def
          unfolding satFlagLessState_def
          unfolding lexLessState1_def
          unfolding lexLessRestricted_def
          by (simp add: Let_def)

            (*    APPLY LEARN    *)
        let ?state_l = "applyLearn ?state_euip"
        let ?l'' = "getCl ?state_l"

        have $: "getM ?state_l = getM ?state_euip \<and> 
                 getQ ?state_l = getQ ?state_euip \<and> 
                 getC ?state_l = getC ?state_euip \<and> 
                 getCl ?state_l = getCl ?state_euip \<and>
                 getConflictFlag ?state_l = getConflictFlag ?state_euip \<and> 
                 getConflictClause ?state_l = getConflictClause ?state_euip \<and> 
                 getF ?state_l = (if getC ?state_euip = [opposite ?l'] then 
                                     getF ?state_euip 
                                  else 
                                     (getF ?state_euip @ [getC ?state_euip])
                                 )"
          using applyLearnPreservedVariables[of "?state_euip"]
          by (simp add: Let_def)

        have "?inv' ?state_l"
        proof-
          have "InvariantConflictFlagCharacterization (getConflictFlag ?state_l) (getF ?state_l) (getM ?state_l)"
            using `?inv' ?state_euip`
            using `getConflictFlag ?state_euip`
            using InvariantConflictFlagCharacterizationAfterApplyLearn[of "?state_euip"]
            by (simp add: Let_def)
          moreover
          hence "InvariantQCharacterization (getConflictFlag ?state_l) (getQ ?state_l) (getF ?state_l) (getM ?state_l)"
            using `?inv' ?state_euip`
            using `getConflictFlag ?state_euip`
            using InvariantQCharacterizationAfterApplyLearn[of "?state_euip"]
            by (simp add: Let_def)
          moreover
          have "InvariantUniqQ (getQ ?state_l)"
            using `?inv' ?state_euip`
            using InvariantUniqQAfterApplyLearn[of "?state_euip"]
            by (simp add: Let_def)
          moreover
          have "InvariantConflictClauseCharacterization (getConflictFlag ?state_l) (getConflictClause ?state_l) (getF ?state_l) (getM ?state_l)"
            using `?inv' ?state_euip`
            using `getConflictFlag ?state_euip`
            using InvariantConflictClauseCharacterizationAfterApplyLearn[of "?state_euip"]
            by (simp only: Let_def)
          ultimately
          show ?thesis
            using `?inv' ?state_euip`
            using `getConflictFlag ?state_euip`
            using `InvariantUniqC (getC ?state_euip)`
            using `InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)`
            using `InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)`
            using `isUIP (opposite (getCl ?state_euip)) (getC ?state_euip) (getM ?state_euip)`
            using WatchInvariantsAfterApplyLearn[of "?state_euip"]
            using $
            by (auto simp only: Let_def)
        qed

        have "InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))"
             "InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))"
             "InvariantNoDecisionsWhenConflict [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)"
             "InvariantNoDecisionsWhenUnit [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)"
          using InvariantNoDecisionsWhenConflictNorUnitAfterApplyLearn[of "?state_euip"]
          using `?inv' ?state_euip`
          using `?inv'' ?state_euip`
          using `getConflictFlag ?state_euip`
          using `InvariantUniqC (getC ?state_euip)`
          using `InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)`
          using `InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)`
          using `InvariantClCurrentLevel (getCl ?state_euip) (getM ?state_euip)`
          using `isUIP (opposite (getCl ?state_euip)) (getC ?state_euip) (getM ?state_euip)`
          using `currentLevel (getM ?state_euip) > 0`
          by (auto simp only: Let_def)
        

        have "isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)"
          using `isUIP (opposite (getCl ?state_euip)) (getC ?state_euip) (getM ?state_euip)`
          using $
          by simp

        have "InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)"
          using `InvariantClCurrentLevel (getCl ?state_euip) (getM ?state_euip)`
          using $
          by simp

        have "InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)"
          using `InvariantCEntailed (getConflictFlag ?state_euip) F0' (getC ?state_euip)`
          using $
          unfolding InvariantCEntailed_def
          by simp

        have "InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)"
          using `InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)`
          using $
          by simp

        have "InvariantUniqC (getC ?state_l)"
          using `InvariantUniqC (getC ?state_euip)`
          using $
          by simp

        have "InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)"
          using `InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)`
          unfolding applyLearn_def
          unfolding setWatch1_def
          unfolding setWatch2_def
          by (auto simp add:Let_def)

        have "InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)"
          using `InvariantClCharacterization (getCl ?state_euip) (getC ?state_euip) (getM ?state_euip)`
            `InvariantUniqC (getC ?state_euip)`
            `InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)`
            `getConflictFlag ?state_euip`
            `?inv' ?state_euip`
          using InvariantCllCharacterizationAfterApplyLearn[of "?state_euip"]
          by (simp add: Let_def)

        have "InvariantEquivalentZL (getF ?state_l) (getM ?state_l) F0'"
          using `InvariantEquivalentZL (getF ?state_euip) (getM ?state_euip) F0'`
          using `getConflictFlag ?state_euip`
          using InvariantEquivalentZLAfterApplyLearn[of "?state_euip" "F0'"]
          using `InvariantCEntailed (getConflictFlag ?state_euip) F0' (getC ?state_euip)`
          by (simp add: Let_def)

        have "InvariantGetReasonIsReason (getReason ?state_l) (getF ?state_l) (getM ?state_l) (set (getQ ?state_l))"
          using `InvariantGetReasonIsReason (getReason ?state_euip) (getF ?state_euip) (getM ?state_euip) (set (getQ ?state_euip))`
          using InvariantGetReasonIsReasonAfterApplyLearn[of "?state_euip"]
          by (simp only: Let_def)

        have "InvariantVarsM (getM ?state_l) F0 Vbl" 
          "InvariantVarsQ (getQ ?state_l) F0 Vbl"
          "InvariantVarsF (getF ?state_l) F0 Vbl"
          using `InvariantVarsM (getM ?state_euip) F0 Vbl`
          using `InvariantVarsQ (getQ ?state_euip) F0 Vbl`
          using `InvariantVarsF (getF ?state_euip) F0 Vbl`
          using $
          using `InvariantCFalse (getConflictFlag ?state_euip) (getM ?state_euip) (getC ?state_euip)` 
          using `getConflictFlag ?state_euip`
          using InvariantVarsFAfterApplyLearn[of "?state_euip" "F0" "Vbl"]
          by auto

        have "getConflictFlag ?state_l"
          using `getConflictFlag ?state_euip`
          using $
          by simp

        have "getSATFlag ?state_l = getSATFlag state"
          using `getSATFlag ?state_euip = getSATFlag state`
          unfolding applyLearn_def
          unfolding setWatch2_def
          unfolding setWatch1_def
          by (simp add: Let_def)


        have "currentLevel (getM ?state_l) > 0"
          using `currentLevel (getM ?state_euip) > 0`
          using $
          by simp

        have "getM ?state_l = getM state \<or> (?state_l, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        proof (cases "getM ?state_euip = getM state")
          case True
          thus ?thesis
            using $
            by simp
        next
          case False
          with `getM ?state_euip = getM state \<or> (?state_euip, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)`
          have "(?state_euip, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
            by simp
          hence "(?state_l, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
            using $
            using `getSATFlag ?state_l = getSATFlag state`
            using `getSATFlag ?state_euip = getSATFlag state`
            unfolding terminationLessState1_def
            unfolding satFlagLessState_def
            unfolding lexLessState1_def
            unfolding lexLessRestricted_def
            by (simp add: Let_def)
          thus ?thesis
            by simp
        qed

      (*    APPLY BACKJUMP    *)
        let ?state_bj = "applyBackjump ?state_l"
        
        have "?inv' ?state_bj \<and> 
           InvariantVarsM (getM ?state_bj) F0 Vbl \<and> 
           InvariantVarsQ (getQ ?state_bj) F0 Vbl \<and> 
           InvariantVarsF (getF ?state_bj) F0 Vbl"
        proof (cases "getC ?state_l = [opposite ?l'']")
          case True
          thus ?thesis
            using WatchInvariantsAfterApplyBackjump[of "?state_l" "F0'"]
            using InvariantUniqAfterApplyBackjump[of "?state_l" "F0'"]
            using InvariantConsistentAfterApplyBackjump[of "?state_l" "F0'"]
            using invariantQCharacterizationAfterApplyBackjump_1[of "?state_l" "F0'"]
            using InvariantConflictFlagCharacterizationAfterApplyBackjump_1[of "?state_l" "F0'"]
            using InvariantUniqQAfterApplyBackjump[of "?state_l"]
            using InvariantConflictClauseCharacterizationAfterApplyBackjump[of "?state_l"]
            using InvariantsVarsAfterApplyBackjump[of "?state_l" "F0'" "F0" "Vbl"]
            using `?inv' ?state_l`
            using `getConflictFlag ?state_l`
            using `InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)`
            using `InvariantUniqC (getC ?state_l)`
            using `InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)`
            using `InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)`
            using `InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)`
            using `InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)`
            using `isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)`
            using `currentLevel (getM ?state_l) > 0`
            using `InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))`
            using `InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))`
            using `InvariantEquivalentZL (getF ?state_l) (getM ?state_l) F0'`
            using `InvariantVarsM (getM ?state_l) F0 Vbl`
            using `InvariantVarsQ (getQ ?state_l) F0 Vbl`
            using `InvariantVarsF (getF ?state_l) F0 Vbl`
            using `vars F0' \<subseteq> vars F0`
            using $
            by (simp add: Let_def)
        next
          case False
          thus ?thesis
            using WatchInvariantsAfterApplyBackjump[of "?state_l" "F0'"]
            using InvariantUniqAfterApplyBackjump[of "?state_l" "F0'"]
            using InvariantConsistentAfterApplyBackjump[of "?state_l" "F0'"]
            using invariantQCharacterizationAfterApplyBackjump_2[of "?state_l" "F0'"]
            using InvariantConflictFlagCharacterizationAfterApplyBackjump_2[of "?state_l" "F0'"]
            using InvariantUniqQAfterApplyBackjump[of "?state_l"]
            using InvariantConflictClauseCharacterizationAfterApplyBackjump[of "?state_l"]
            using InvariantsVarsAfterApplyBackjump[of "?state_l" "F0'" "F0" "Vbl"]
            using `?inv' ?state_l`
            using `getConflictFlag ?state_l`
            using `InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)`
            using `InvariantUniqC (getC ?state_l)`
            using `InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)`
            using `InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)`
            using `InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)`
            using `InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)`
            using `isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)`
            using `currentLevel (getM ?state_l) > 0`
            using `InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))`
            using `InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))`
            using `InvariantNoDecisionsWhenConflict [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)`
            using `InvariantNoDecisionsWhenUnit [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)`
            using $
            using `InvariantEquivalentZL (getF ?state_l) (getM ?state_l) F0'`
            using `InvariantVarsM (getM ?state_l) F0 Vbl`
            using `InvariantVarsQ (getQ ?state_l) F0 Vbl`
            using `InvariantVarsF (getF ?state_l) F0 Vbl`
            using `vars F0' \<subseteq> vars F0`
            by (simp add: Let_def)
        qed

        have "?inv'' ?state_bj"
        proof (cases "getC ?state_l = [opposite ?l'']")
          case True
          thus ?thesis
            using InvariantsNoDecisionsWhenConflictNorUnitAfterApplyBackjump_1[of "?state_l" "F0'"]
            using `?inv' ?state_l`
            using `getConflictFlag ?state_l`
            using `InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)`
            using `InvariantUniqC (getC ?state_l)`
            using `InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)`
            using `InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)`
            using `InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)`
            using `InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)`
            using `isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)`
            using `currentLevel (getM ?state_l) > 0`
            using `InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))`
            using `InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))`
            using $
            by (simp add: Let_def)
        next
          case False
          thus ?thesis
            using InvariantsNoDecisionsWhenConflictNorUnitAfterApplyBackjump_2[of "?state_l"]
            using `?inv' ?state_l`
            using `getConflictFlag ?state_l`
            using `InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)`
            using `InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)`
            using `InvariantUniqC (getC ?state_l)`
            using `InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)`
            using `InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)`
            using `InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)`
            using `isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)`
            using `currentLevel (getM ?state_l) > 0`
            using `InvariantNoDecisionsWhenConflict (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))`
            using `InvariantNoDecisionsWhenUnit (getF ?state_euip) (getM ?state_l) (currentLevel (getM ?state_l))`
            using `InvariantNoDecisionsWhenConflict [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)`
            using `InvariantNoDecisionsWhenUnit [getC ?state_euip] (getM ?state_l) (getBackjumpLevel ?state_l)`
            using $
            by (simp add: Let_def)
        qed

        

        have "getBackjumpLevel ?state_l > 0 \<longrightarrow> (getF ?state_l) \<noteq> [] \<and> (last (getF ?state_l) = (getC ?state_l))"
        proof (cases "getC ?state_l = [opposite ?l'']")
          case True
          thus ?thesis
            unfolding getBackjumpLevel_def
            by simp
        next
          case False
          thus ?thesis
            using $
            by simp
        qed
        hence "InvariantGetReasonIsReason (getReason ?state_bj) (getF ?state_bj) (getM ?state_bj) (set (getQ ?state_bj))"
          using `InvariantGetReasonIsReason (getReason ?state_l) (getF ?state_l) (getM ?state_l) (set (getQ ?state_l))`
          using `?inv' ?state_l`
          using `getConflictFlag ?state_l`
          using `isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)`
          using `InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)`
          using `InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)`
          using `InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)`
          using `InvariantUniqC (getC ?state_l)`
          using `InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)`
          using `InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)`
          using `currentLevel (getM ?state_l) > 0`
          using InvariantGetReasonIsReasonAfterApplyBackjump[of "?state_l" "F0'"]
          by (simp only: Let_def)

        have "InvariantEquivalentZL (getF ?state_bj) (getM ?state_bj) F0'"
          using `InvariantEquivalentZL (getF ?state_l) (getM ?state_l) F0'`
          using `?inv' ?state_l`
          using `getConflictFlag ?state_l`
          using `isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)`
          using `InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)`
          using `InvariantUniqC (getC ?state_l)`
          using `InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)`
          using `InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)`
          using `InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)`
          using `InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)`
          using InvariantEquivalentZLAfterApplyBackjump[of "?state_l" "F0'"]
          using `currentLevel (getM ?state_l) > 0`
          by (simp only: Let_def)


        have "getSATFlag ?state_bj = getSATFlag state"
          using `getSATFlag ?state_l = getSATFlag state`
          using `?inv' ?state_l`
          using applyBackjumpPreservedVariables[of "?state_l"]
          by (simp only: Let_def)

        let ?level = "getBackjumpLevel ?state_l"
        let ?prefix = "prefixToLevel ?level (getM ?state_l)"
        let ?l = "opposite (getCl ?state_l)"

        have "isMinimalBackjumpLevel (getBackjumpLevel ?state_l) (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)"
          using isMinimalBackjumpLevelGetBackjumpLevel[of "?state_l"]
          using `?inv' ?state_l`
          using `InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)`
          using `InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)`
          using `InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)`
          using `InvariantUniqC (getC ?state_l)`
          using `InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)`
          using `InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)`
          using `isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)`
          using `getConflictFlag ?state_l`
          using `currentLevel (getM ?state_l) > 0`
          by (simp add: Let_def)
        hence "getBackjumpLevel ?state_l < elementLevel (getCl ?state_l) (getM ?state_l)"
          unfolding isMinimalBackjumpLevel_def
          unfolding isBackjumpLevel_def
          by simp
        hence "getBackjumpLevel ?state_l < currentLevel (getM ?state_l)"
          using elementLevelLeqCurrentLevel[of "getCl ?state_l" "getM ?state_l"]
          by simp
        hence "(?state_bj, ?state_l) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
          using applyBackjumpEffect[of "?state_l" "F0'"]
          using `?inv' ?state_l`
          using `getConflictFlag ?state_l`
          using `isUIP (opposite (getCl ?state_l)) (getC ?state_l) (getM ?state_l)`
          using `InvariantClCurrentLevel (getCl ?state_l) (getM ?state_l)`
          using `InvariantCEntailed (getConflictFlag ?state_l) F0' (getC ?state_l)`
          using `InvariantCFalse (getConflictFlag ?state_l) (getM ?state_l) (getC ?state_l)`
          using `InvariantUniqC (getC ?state_l)`
          using `InvariantClCharacterization (getCl ?state_l) (getC ?state_l) (getM ?state_l)`
          using `InvariantCllCharacterization (getCl ?state_l) (getCll ?state_l) (getC ?state_l) (getM ?state_l)`
          using `currentLevel (getM ?state_l) > 0`
          using lexLessBackjump[of "?prefix" "?level" "getM ?state_l" "?l"]
          using `getSATFlag ?state_bj = getSATFlag state`
          using `getSATFlag ?state_l = getSATFlag state`
          using `getSATFlag state = UNDEF`
          using `?inv' ?state_l`
          using `InvariantVarsM (getM ?state_l) F0 Vbl`
          using `?inv' ?state_bj \<and> InvariantVarsM (getM ?state_bj) F0 Vbl \<and> 
           InvariantVarsQ (getQ ?state_bj) F0 Vbl \<and> 
           InvariantVarsF (getF ?state_bj) F0 Vbl`
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          unfolding InvariantVarsM_def
          unfolding terminationLessState1_def
          unfolding satFlagLessState_def
          unfolding lexLessState1_def
          unfolding lexLessRestricted_def
          by (simp add: Let_def)
        hence "(?state_bj, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
          using `getM ?state_l = getM state \<or> (?state_l, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)`
          using `getSATFlag state = UNDEF`
          using `getSATFlag ?state_bj = getSATFlag state`
          using `getSATFlag ?state_l = getSATFlag state`
          using transTerminationLessState1I[of "?state_bj" "?state_l" "vars F0 \<union> Vbl" "state"]
          unfolding terminationLessState1_def
          unfolding satFlagLessState_def
          unfolding lexLessState1_def
          unfolding lexLessRestricted_def
          by auto

        show ?thesis
          using `?inv' ?state_bj \<and> InvariantVarsM (getM ?state_bj) F0 Vbl \<and> 
           InvariantVarsQ (getQ ?state_bj) F0 Vbl \<and> 
           InvariantVarsF (getF ?state_bj) F0 Vbl`
          using `?inv'' ?state_bj`
          using `InvariantEquivalentZL (getF ?state_bj) (getM ?state_bj) F0'`
          using `InvariantGetReasonIsReason (getReason ?state_bj) (getF ?state_bj) (getM ?state_bj) (set (getQ ?state_bj))`
          using `getSATFlag state = UNDEF`
          using `getSATFlag ?state_bj = getSATFlag state`
          using `getConflictFlag ?state_up`
          using `currentLevel (getM ?state_up) \<noteq> 0`
          using `(?state_bj, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)`
          unfolding solve_loop_body_def
          by (auto simp add: Let_def)
      qed
    qed
  next
    case False
    show ?thesis
    proof (cases "vars (elements (getM ?state_up)) \<supseteq> Vbl")
      case True
      hence "satisfiable F0'"
        using soundnessForSat[of "F0'" "Vbl" "getF ?state_up" "getM ?state_up"]
        using `InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'`
        using `?inv' ?state_up`
        using `InvariantVarsF (getF ?state_up) F0 Vbl`
        using `\<not> getConflictFlag ?state_up`
        using `vars F0 \<subseteq> Vbl`
        using `vars F0' \<subseteq> vars F0`
        using True
        unfolding InvariantConflictFlagCharacterization_def
        unfolding satisfiable_def
        unfolding InvariantVarsF_def
        by blast
      moreover
      let ?state' = "?state_up \<lparr> getSATFlag := TRUE \<rparr>"
      have "(?state', state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        using `getSATFlag state = UNDEF`
        unfolding terminationLessState1_def
        unfolding satFlagLessState_def
        by simp
      ultimately
      show ?thesis
        using `vars (elements (getM ?state_up)) \<supseteq> Vbl`
        using `?inv' ?state_up`
        using `?inv'' ?state_up`
        using `InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'`
        using `InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up)  (getM ?state_up) (set (getQ ?state_up))`
        using `InvariantVarsM (getM ?state_up) F0 Vbl`
        using `InvariantVarsQ (getQ ?state_up) F0 Vbl`
        using `InvariantVarsF (getF ?state_up) F0 Vbl`
        using `\<not> getConflictFlag ?state_up`
        unfolding solve_loop_body_def
        by (simp add: Let_def)
    next
      case False
      let ?literal = "selectLiteral ?state_up Vbl"
      let ?state_d = "applyDecide ?state_up Vbl"
      
      have "InvariantConsistent (getM ?state_d)"
        using InvariantConsistentAfterApplyDecide [of "Vbl" "?state_up"]
        using False
        using `?inv' ?state_up`
        by (simp add: Let_def)
      moreover
      have "InvariantUniq (getM ?state_d)"
        using InvariantUniqAfterApplyDecide [of "Vbl" "?state_up"]
        using False
        using `?inv' ?state_up`
        by (simp add: Let_def)
      moreover
      have "InvariantQCharacterization (getConflictFlag ?state_d) (getQ ?state_d) (getF ?state_d) (getM ?state_d)"
        using InvariantQCharacterizationAfterApplyDecide [of "Vbl" "?state_up"]
        using False
        using `?inv' ?state_up`
        using `\<not> getConflictFlag ?state_up`
        using `exhaustiveUnitPropagate_dom state`
        using conflictFlagOrQEmptyAfterExhaustiveUnitPropagate[of "state"]
        by (simp add: Let_def)
      moreover
      have "InvariantConflictFlagCharacterization (getConflictFlag ?state_d) (getF ?state_d) (getM ?state_d)"
        using `InvariantConsistent (getM ?state_d)`
        using `InvariantUniq (getM ?state_d)`
        using InvariantConflictFlagCharacterizationAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using `?inv' ?state_up`
        using assertLiteralEffect
        unfolding applyDecide_def
        by (simp only: Let_def)
      moreover
      have "InvariantConflictClauseCharacterization (getConflictFlag ?state_d) (getConflictClause ?state_d) (getF ?state_d) (getM ?state_d)"
        using InvariantConflictClauseCharacterizationAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using `?inv' ?state_up`
        using assertLiteralEffect
        unfolding applyDecide_def
        by (simp only: Let_def)
      moreover
      have "InvariantNoDecisionsWhenConflict (getF ?state_d) (getM ?state_d) (currentLevel (getM ?state_d))"
        "InvariantNoDecisionsWhenUnit (getF ?state_d) (getM ?state_d) (currentLevel (getM ?state_d))"
        using `exhaustiveUnitPropagate_dom state`
        using conflictFlagOrQEmptyAfterExhaustiveUnitPropagate[of "state"]
        using `\<not> getConflictFlag ?state_up` 
        using `?inv' ?state_up`
        using `?inv'' ?state_up`
        using InvariantsNoDecisionsWhenConflictNorUnitAfterAssertLiteral[of "?state_up" "True" "?literal"]
        unfolding applyDecide_def
        by (auto simp add: Let_def)
      moreover
      have "InvariantEquivalentZL (getF ?state_d) (getM ?state_d) F0'"
        using InvariantEquivalentZLAfterApplyDecide[of "?state_up" "F0'" "Vbl"]
        using `?inv' ?state_up`
        using `InvariantEquivalentZL (getF ?state_up) (getM ?state_up) F0'`
        by (simp add: Let_def)
      moreover
      have "InvariantGetReasonIsReason (getReason ?state_d) (getF ?state_d) (getM ?state_d) (set (getQ ?state_d))"
        using InvariantGetReasonIsReasonAfterApplyDecide[of "Vbl" "?state_up"]
        using `?inv' ?state_up`
        using `InvariantGetReasonIsReason (getReason ?state_up) (getF ?state_up) (getM ?state_up) (set (getQ ?state_up))`
        using False
        using `\<not> getConflictFlag ?state_up` 
        using `getConflictFlag ?state_up \<or> getQ ?state_up = []`
        by (simp add: Let_def)
      moreover
      have "getSATFlag ?state_d = getSATFlag state"
        unfolding applyDecide_def
        using `getSATFlag ?state_up = getSATFlag state`
        using assertLiteralEffect[of "?state_up" "selectLiteral ?state_up Vbl" "True"]
        using `?inv' ?state_up`
        by (simp only: Let_def)
      moreover
      have "InvariantVarsM (getM ?state_d) F0 Vbl"
        "InvariantVarsF (getF ?state_d) F0 Vbl"
        "InvariantVarsQ (getQ ?state_d) F0 Vbl"
        using InvariantsVarsAfterApplyDecide[of "Vbl" "?state_up"]
        using False
        using `?inv' ?state_up`
        using `\<not> getConflictFlag ?state_up`
        using `getConflictFlag ?state_up \<or> getQ ?state_up = []`
        using `InvariantVarsM (getM ?state_up) F0 Vbl`
        using `InvariantVarsQ (getQ ?state_up) F0 Vbl`
        using `InvariantVarsF (getF ?state_up) F0 Vbl`
        by (auto simp only: Let_def)
      moreover
      have "(?state_d, ?state_up) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        using `getSATFlag ?state_up = getSATFlag state`
        using assertLiteralEffect[of "?state_up" "selectLiteral ?state_up Vbl" "True"]
        using `?inv' ?state_up`
        using `InvariantVarsM (getM state) F0 Vbl`
        using `InvariantVarsM (getM ?state_up) F0 Vbl`
        using `InvariantVarsM (getM ?state_d) F0 Vbl`
        using `getSATFlag state = UNDEF`
        using `?inv' ?state_up`
        using `InvariantConsistent (getM ?state_d)`
        using `InvariantUniq (getM ?state_d)`
        using lexLessAppend[of "[(selectLiteral ?state_up Vbl, True)]""getM ?state_up"]
        unfolding applyDecide_def
        unfolding terminationLessState1_def
        unfolding lexLessState1_def
        unfolding lexLessRestricted_def
        unfolding InvariantVarsM_def
        unfolding InvariantUniq_def
        unfolding InvariantConsistent_def
        by (simp add: Let_def)
      hence "(?state_d, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)"
        using `?state_up = state \<or> (?state_up, state) \<in> terminationLessState1 (vars F0 \<union> Vbl)`
        using transTerminationLessState1I[of "?state_d" "?state_up" "vars F0 \<union> Vbl" "state"]
        by auto
      ultimately
      show ?thesis
        using `?inv' ?state_up`
        using `getSATFlag state = UNDEF`
        using `\<not> getConflictFlag ?state_up`
        using False
        using WatchInvariantsAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using InvariantWatchCharacterizationAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using InvariantUniqQAfterAssertLiteral[of "?state_up" "?literal" "True"]
        using assertLiteralEffect[of "?state_up" "?literal" "True"]
        unfolding solve_loop_body_def
        unfolding applyDecide_def
        unfolding selectLiteral_def
        by (simp add: Let_def)
    qed
  qed
qed


(*****************************************************************************)
(*        S O L V E    L O O P                                               *)
(*****************************************************************************)

lemma SolveLoopTermination:
assumes
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantUniqQ (getQ state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)" and
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)" and
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))" and
  "getSATFlag state = UNDEF \<longrightarrow> InvariantEquivalentZL (getF state) (getM state) F0'" and
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)" and
  "finite Vbl"
  "vars F0' \<subseteq> vars F0"
  "vars F0 \<subseteq> Vbl"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
shows
  "solve_loop_dom state Vbl"
using assms
proof (induct rule: wf_induct[of "terminationLessState1 (vars F0 \<union> Vbl)"])
  case 1
  thus ?case
    using `finite Vbl`
    using finiteVarsFormula[of "F0"]
    using wellFoundedTerminationLessState1[of "vars F0 \<union> Vbl"]
    by simp
next
  case (2 state')
  note ih = this
  show ?case
  proof (cases "getSATFlag state' = UNDEF")
    case False
    show ?thesis
      apply (rule solve_loop_dom.intros)
      using False
      by simp
  next
    case True
    let ?state'' = "solve_loop_body state' Vbl"
    have
      "InvariantConsistent (getM ?state'')"
      "InvariantUniq (getM ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and 
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and 
      "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')" and 
      "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantUniqQ (getQ ?state'')" and
      "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')" and
      "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')" and
      "InvariantNoDecisionsWhenConflict (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))" and
      "InvariantNoDecisionsWhenUnit (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))" and
      "InvariantConflictClauseCharacterization (getConflictFlag ?state'') (getConflictClause ?state'') (getF ?state'') (getM ?state'')"
      "InvariantGetReasonIsReason (getReason ?state'') (getF ?state'') (getM ?state'') (set (getQ ?state''))"
      "InvariantEquivalentZL (getF ?state'') (getM ?state'') F0'"
      "InvariantVarsM (getM ?state'') F0 Vbl"
      "InvariantVarsQ (getQ ?state'') F0 Vbl"
      "InvariantVarsF (getF ?state'') F0 Vbl"
      "getSATFlag ?state'' = FALSE \<longrightarrow> \<not> satisfiable F0'"
      "getSATFlag ?state'' = TRUE  \<longrightarrow> satisfiable F0'"
      "(?state'', state') \<in> terminationLessState1 (vars F0 \<union> Vbl)"
     using InvariantsAfterSolveLoopBody[of "state'" "F0'" "Vbl" "F0"]
     using ih(2) ih(3) ih(4) ih(5) ih(6) ih(7) ih(8) ih(9) ih(10) ih(11) ih(12) ih(13) ih(14) ih(15)
           ih(16) ih(17) ih(18) ih(19) ih(20) ih(21) ih(22) ih(23)
     using True
     by (auto simp only: Let_def)
   hence "solve_loop_dom ?state'' Vbl"
     using ih
     by auto
   thus ?thesis
     using solve_loop_dom.intros[of "state'" "Vbl"]
     using True
     by simp
 qed
qed


lemma SATFlagAfterSolveLoop:
assumes
  "solve_loop_dom state Vbl"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantUniqQ (getQ state)" and
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)" and
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)" and
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))" and
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))" and
  "getSATFlag state = UNDEF \<longrightarrow> InvariantEquivalentZL (getF state) (getM state) F0'" and
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
  "getSATFlag state = FALSE \<longrightarrow> \<not> satisfiable F0'"
  "getSATFlag state = TRUE  \<longrightarrow> satisfiable F0'"
  "finite Vbl"
  "vars F0' \<subseteq> vars F0"
  "vars F0 \<subseteq> Vbl"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
shows
  "let state' = solve_loop state Vbl in 
         (getSATFlag state' = FALSE \<and> \<not> satisfiable F0') \<or> (getSATFlag state' = TRUE  \<and> satisfiable F0')"
using assms
proof (induct state Vbl rule: solve_loop_dom.induct)
  case (step state' Vbl)
  note ih = this
  show ?case
  proof (cases "getSATFlag state' = UNDEF")
    case False
    with solve_loop.simps[of "state'"]
    have "solve_loop state' Vbl = state'"
      by simp
    thus ?thesis
      using False
      using ih(19) ih(20)
      using ExtendedBool.nchotomy
      by (auto simp add: Let_def)
  next
    case True
    let ?state'' = "solve_loop_body state' Vbl"
    have "solve_loop state' Vbl = solve_loop ?state'' Vbl"
      using solve_loop.simps[of "state'"]
      using True
      by (simp add: Let_def)
    moreover
    have "InvariantEquivalentZL (getF state') (getM state') F0'"
      using True
      using ih(17)
      by simp
    hence
      "InvariantConsistent (getM ?state'')"
      "InvariantUniq (getM ?state'')"
      "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and 
      "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and 
      "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') (getM ?state'')" and 
      "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')" and
      "InvariantWatchListsUniq (getWatchList ?state'')" and
      "InvariantWatchListsCharacterization (getWatchList ?state'') (getWatch1 ?state'') (getWatch2 ?state'')" and
      "InvariantUniqQ (getQ ?state'')" and
      "InvariantQCharacterization (getConflictFlag ?state'') (getQ ?state'') (getF ?state'') (getM ?state'')" and
      "InvariantConflictFlagCharacterization (getConflictFlag ?state'') (getF ?state'') (getM ?state'')" and
      "InvariantNoDecisionsWhenConflict (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))" and
      "InvariantNoDecisionsWhenUnit (getF ?state'') (getM ?state'') (currentLevel (getM ?state''))" and
      "InvariantConflictClauseCharacterization (getConflictFlag ?state'') (getConflictClause ?state'') (getF ?state'') (getM ?state'')"
      "InvariantGetReasonIsReason (getReason ?state'') (getF ?state'') (getM ?state'') (set (getQ ?state''))"
      "InvariantEquivalentZL (getF ?state'') (getM ?state'') F0'"
      "InvariantVarsM (getM ?state'') F0 Vbl"
      "InvariantVarsQ (getQ ?state'') F0 Vbl"
      "InvariantVarsF (getF ?state'') F0 Vbl"
      "getSATFlag ?state'' = FALSE \<longrightarrow> \<not> satisfiable F0'"
      "getSATFlag ?state'' = TRUE  \<longrightarrow> satisfiable F0'"
      using ih(1) ih(3) ih(4) ih(5) ih(6) ih(7) ih(8) ih(9) ih(10) ih(11) ih(12) ih(13) ih(14)
            ih(15) ih(16) ih(18) ih(21) ih(22) ih(23) ih(24) ih(25) ih(26)
      using InvariantsAfterSolveLoopBody[of "state'" "F0'" "Vbl" "F0"]
      using True
      by (auto simp only: Let_def)
    ultimately
    show ?thesis
      using True
      using ih(2)
      using ih(21)
      using ih(22)
      using ih(23)
      by (simp add: Let_def)
  qed
qed

      

end