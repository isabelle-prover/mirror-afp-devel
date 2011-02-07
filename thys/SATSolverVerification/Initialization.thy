theory Initialization
imports UnitPropagate
begin


(*********************************************************************************)
(*    A D D    C L A U S E                                                       *)
(*********************************************************************************)

lemma InvariantsAfterAddClause:
fixes state::State and clause :: Clause and Vbl :: "Variable set"
assumes
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantUniqQ (getQ state)"
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))"
  "currentLevel (getM state) = 0"
  "(getConflictFlag state) \<or> (getQ state) = []"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
  "finite Vbl"
  "vars clause \<subseteq> vars F0"
shows
  "let state' = (addClause clause state) in
      InvariantConsistent (getM state') \<and> 
      InvariantUniq (getM state') \<and> 
      InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state') \<and> 
      InvariantWatchListsUniq (getWatchList state') \<and> 
      InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and> 
      InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state') \<and> 
      InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state') \<and> 
      InvariantWatchCharacterization (getF state') (getWatch1 state') (getWatch2 state') (getM state') \<and> 
      InvariantConflictFlagCharacterization (getConflictFlag state') (getF state') (getM state') \<and> 
      InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state') \<and> 
      InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state') \<and> 
      InvariantGetReasonIsReason (getReason state') (getF state') (getM state') (set (getQ state')) \<and> 
      InvariantUniqQ (getQ state') \<and> 
      InvariantVarsQ (getQ state') F0 Vbl \<and> 
      InvariantVarsM (getM state') F0 Vbl \<and> 
      InvariantVarsF (getF state') F0 Vbl \<and> 
      currentLevel (getM state') = 0 \<and> 
      ((getConflictFlag state') \<or> (getQ state') = [])
"
proof-
  let ?clause' = "remdups (removeFalseLiterals clause (elements (getM state)))"

  have *: "\<forall> l. l el ?clause' \<longrightarrow> \<not> literalFalse l (elements (getM state))"
    unfolding removeFalseLiterals_def
    by auto

  have "vars ?clause' \<subseteq> vars clause"
    using varsSubsetValuation[of "?clause'" "clause"]
    unfolding removeFalseLiterals_def
    by auto
  hence "vars ?clause' \<subseteq> vars F0"
    using `vars clause \<subseteq> vars F0`
    by simp

  show ?thesis
  proof (cases "clauseTrue ?clause' (elements (getM state))")
    case True
    thus ?thesis
      using assms
      unfolding addClause_def
      by simp
  next
    case False
    show ?thesis
    proof (cases "?clause' = []")
      case True
      thus ?thesis
        using assms
        using `\<not> clauseTrue ?clause' (elements (getM state))`
        unfolding addClause_def
        by simp
    next
      case False
      thus ?thesis
      proof (cases "length ?clause' = 1")
        case True
        let ?state' = "assertLiteral (hd ?clause') False state"
        have "addClause clause state = exhaustiveUnitPropagate ?state'"
          using `\<not> clauseTrue ?clause' (elements (getM state))`
          using `\<not> ?clause' = []`
          using `length ?clause' = 1`
          unfolding addClause_def
          by (simp add: Let_def)
        moreover
        from `?clause' \<noteq> []`
        have "hd ?clause' \<in> set ?clause'"
          using hd_in_set[of "?clause'"]
          by simp
        with *
        have "\<not> literalFalse (hd ?clause') (elements (getM state))"
          by simp
        hence "consistent (elements ((getM state) @ [(hd ?clause', False)]))"
          using assms
          unfolding InvariantConsistent_def
          using consistentAppendElement[of "elements (getM state)" "hd ?clause'"]
          by simp
        hence "consistent (elements (getM ?state'))"
          using assms
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          by simp
        moreover
        from `\<not> clauseTrue ?clause' (elements (getM state))`
        have "uniq (elements (getM ?state'))"
          using assms
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          using `hd ?clause' \<in> set ?clause'`
          unfolding InvariantUniq_def
          by (simp add: uniqAppendIff clauseTrueIffContainsTrueLiteral)
        moreover
        have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state') (getF ?state')" and
          "InvariantWatchListsUniq (getWatchList ?state')" and
          "InvariantWatchListsCharacterization (getWatchList ?state') (getWatch1 ?state') (getWatch2 ?state')"
          "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')" and
          "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
          using assms
          using WatchInvariantsAfterAssertLiteral[of "state" "hd ?clause'" "False"]
          by (auto simp add: Let_def)
        moreover
        have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') (getM ?state')"
          using assms
          using InvariantWatchCharacterizationAfterAssertLiteral[of "state" "hd ?clause'" "False"]
          using `uniq (elements (getM ?state'))`
          using `consistent (elements (getM ?state'))`
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          by (simp add: Let_def)
        moreover
        have "InvariantConflictFlagCharacterization (getConflictFlag ?state') (getF ?state') (getM ?state')"
          using assms
          using InvariantConflictFlagCharacterizationAfterAssertLiteral[of "state" "hd ?clause'" "False"]
          using `consistent (elements (getM ?state'))`
          unfolding InvariantConsistent_def
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          by (simp add: Let_def)
        moreover
        have "InvariantConflictClauseCharacterization (getConflictFlag ?state') (getConflictClause ?state') (getF ?state') (getM ?state')"
          using assms
          using InvariantConflictClauseCharacterizationAfterAssertLiteral[of "state" "hd ?clause'" "False"]
          by (simp add: Let_def)
        moreover
        let ?state'' = "?state'\<lparr> getM := (getM ?state') @ [(hd ?clause', False)] \<rparr>"
        have "InvariantQCharacterization (getConflictFlag ?state') (getQ ?state') (getF ?state') (getM ?state')"
        proof (cases "getConflictFlag state")
          case True
          hence "getConflictFlag ?state'"
            using assms
            using assertLiteralConflictFlagEffect[of "state" "hd ?clause'" "False"]
            using `uniq (elements (getM ?state'))`
            using `consistent (elements (getM ?state'))`
            unfolding InvariantConsistent_def
            unfolding InvariantUniq_def
            using assertLiteralEffect[of "state" "hd ?clause'" "False"]
            by (auto simp add: Let_def)
          thus ?thesis
            using assms
            unfolding InvariantQCharacterization_def
            by simp
        next
          case False
          with `(getConflictFlag state) \<or> (getQ state) = []`
          have "getQ state = []"
            by simp
          thus ?thesis
            using InvariantQCharacterizationAfterAssertLiteralNotInQ[of "state" "hd ?clause'" "False"]
            using assms
            using `uniq (elements (getM ?state'))`
            using `consistent (elements (getM ?state'))`
            unfolding InvariantConsistent_def
            unfolding InvariantUniq_def
            using assertLiteralEffect[of "state" "hd ?clause'" "False"]
            by (auto simp add: Let_def)
        qed
        moreover
        have "InvariantUniqQ (getQ ?state')"
          using assms
          using InvariantUniqQAfterAssertLiteral[of "state" "hd ?clause'" "False"]
          by (simp add: Let_def)
        moreover
        have "currentLevel (getM ?state') = 0"
          using assms
          using `\<not> clauseTrue ?clause' (elements (getM state))`
          using `\<not> ?clause' = []`
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          unfolding addClause_def
          unfolding currentLevel_def
          by (simp add:Let_def markedElementsAppend)
        moreover
        hence "InvariantGetReasonIsReason (getReason ?state') (getF ?state') (getM ?state') (set (getQ ?state'))"
          unfolding InvariantGetReasonIsReason_def
          using elementLevelLeqCurrentLevel[of _ "getM ?state'"]
          by auto
        moreover
        have "var (hd ?clause') \<in> vars F0"
          using `?clause' \<noteq> []`
          using hd_in_set[of "?clause'"]
          using `vars ?clause' \<subseteq> vars F0`
          using clauseContainsItsLiteralsVariable[of "hd ?clause'" "?clause'"]
          by auto
        hence "InvariantVarsQ (getQ ?state') F0 Vbl"
          "InvariantVarsM (getM ?state') F0 Vbl"
          "InvariantVarsF (getF ?state') F0 Vbl"
          using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)`
          using `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
          using `InvariantWatchListsUniq (getWatchList state)`
          using `InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)`
          using `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
          using `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)`
          using `InvariantVarsF (getF state) F0 Vbl`
          using `InvariantVarsM (getM state) F0 Vbl`
          using `InvariantVarsQ (getQ state) F0 Vbl`
          using `consistent (elements (getM ?state'))`
          using `uniq (elements (getM ?state'))`
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          using varsAppendValuation[of "elements (getM state)" "[hd ?clause']"]
          using InvariantVarsQAfterAssertLiteral[of "state" "hd ?clause'" "False" "F0" "Vbl"]
          unfolding InvariantVarsM_def
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          by (auto simp add: Let_def)
        moreover
        have "exhaustiveUnitPropagate_dom ?state'"
          using exhaustiveUnitPropagateTermination[of "?state'" "F0" "Vbl"]
          using `InvariantUniqQ (getQ ?state')`
          using `InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state') (getF ?state')`
          using `InvariantWatchListsUniq (getWatchList ?state')`
          using `InvariantWatchListsCharacterization (getWatchList ?state') (getWatch1 ?state') (getWatch2 ?state')`
          using `InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')`
          using `InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')`
          using `InvariantQCharacterization (getConflictFlag ?state') (getQ ?state') (getF ?state') (getM ?state')`
          using `InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') (getM ?state')`
          using `InvariantConflictFlagCharacterization (getConflictFlag ?state') (getF ?state') (getM ?state')`
          using `consistent (elements (getM ?state'))`
          using `uniq (elements (getM ?state'))`
          using `finite Vbl`
          using `InvariantVarsQ (getQ ?state') F0 Vbl`
          using `InvariantVarsM (getM ?state') F0 Vbl`
          using `InvariantVarsF (getF ?state') F0 Vbl`
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          by simp
        ultimately
        show ?thesis
          using `exhaustiveUnitPropagate_dom ?state'`
          using InvariantsAfterExhaustiveUnitPropagate[of "?state'"]
          using InvariantConflictClauseCharacterizationAfterExhaustivePropagate[of "?state'"]
          using conflictFlagOrQEmptyAfterExhaustiveUnitPropagate[of "?state'"]
          using exhaustiveUnitPropagatePreservesCurrentLevel[of "?state'"]
          using InvariantGetReasonIsReasonAfterExhaustiveUnitPropagate[of "?state'"]
          using assms
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          by (auto simp only:Let_def)
      next
        case False
        thus ?thesis
        proof (cases "clauseTautology ?clause'")
          case True
          thus ?thesis
            using assms
            using `\<not> ?clause' = []`
            using `\<not> clauseTrue ?clause' (elements (getM state))`
            using `length ?clause' \<noteq> 1`
            unfolding addClause_def
            by simp
        next
          case False
          from `\<not> ?clause' = []` `length ?clause' \<noteq> 1`
          have "length ?clause' > 1"
            by (induct (?clause')) auto

          hence "nth ?clause' 0 \<noteq> nth ?clause' 1"
            using distinct_remdups[of "?clause'"]
            using nth_eq_iff_index_eq[of "?clause'" "0" "1"]
            using `\<not> ?clause' = []`
            by auto

          let ?state' = "let clauseIndex = length (getF state) in
                         let state'   = state\<lparr> getF := (getF state) @ [?clause']\<rparr> in
                         let state''  = setWatch1 clauseIndex (nth ?clause' 0) state' in
                         let state''' = setWatch2 clauseIndex (nth ?clause' 1) state'' in
                         state'''"

          have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
            using `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
            using `length ?clause' > 1`
            using `?clause' \<noteq> []`
            using nth_mem[of "0" "?clause'"]
            using nth_mem[of "1" "?clause'"]
            unfolding InvariantWatchesEl_def
            unfolding setWatch1_def
            unfolding setWatch2_def
            by (auto simp add: Let_def nth_append)
          moreover
          have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
            using `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
            using `nth ?clause' 0 \<noteq> nth ?clause' 1`
            unfolding InvariantWatchesDiffer_def
            unfolding setWatch1_def
            unfolding setWatch2_def
            by (auto simp add: Let_def)
          moreover
          have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state') (getF ?state')"
            using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)`
            unfolding InvariantWatchListsContainOnlyClausesFromF_def
            unfolding setWatch1_def
            unfolding setWatch2_def
            by (auto simp add:Let_def) (force)+
          moreover
          have "InvariantWatchListsCharacterization (getWatchList ?state') (getWatch1 ?state') (getWatch2 ?state')"
            using `InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)`
            using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)`
            using `nth ?clause' 0 \<noteq> nth ?clause' 1`
            unfolding InvariantWatchListsCharacterization_def
            unfolding InvariantWatchListsContainOnlyClausesFromF_def
            unfolding setWatch1_def
            unfolding setWatch2_def
            by (auto simp add:Let_def)
          moreover
          have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') (getM ?state')"
          proof-
            {
              fix c
              assume "0 \<le> c \<and> c < length (getF ?state')"
              fix www1 www2
              assume "Some www1 = (getWatch1 ?state' c)" "Some www2 = (getWatch2 ?state' c)"
              have "watchCharacterizationCondition www1 www2 (getM ?state') (nth (getF ?state') c) \<and> 
                    watchCharacterizationCondition www2 www1 (getM ?state') (nth (getF ?state') c)"
              proof (cases "c < length (getF state)")
                case True
                hence "(nth (getF ?state') c) = (nth (getF state) c)"
                  unfolding setWatch1_def
                  unfolding setWatch2_def
                  by (auto simp add: Let_def nth_append)
                have "Some www1 = (getWatch1 state c)" "Some www2 = (getWatch2 state c)"
                  using True
                  using `Some www1 = (getWatch1 ?state' c)` `Some www2 = (getWatch2 ?state' c)`
                  unfolding setWatch1_def
                  unfolding setWatch2_def
                  by (auto simp add: Let_def)
                thus ?thesis
                  using `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)`
                  unfolding InvariantWatchCharacterization_def
                  using `(nth (getF ?state') c) = (nth (getF state) c)`
                  using True
                  unfolding setWatch1_def
                  unfolding setWatch2_def
                  by (auto simp add: Let_def)
              next
                case False
                with `0 \<le> c \<and> c < length (getF ?state')`
                have "c = length (getF state)"
                  unfolding setWatch1_def
                  unfolding setWatch2_def
                  by (auto simp add: Let_def)
                from `InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')`
                obtain w1 w2 
                  where 
                  "w1 el ?clause'" "w2 el ?clause'"
                  "getWatch1 ?state' (length (getF state)) = Some w1"
                  "getWatch2 ?state' (length (getF state)) = Some w2"
                  unfolding InvariantWatchesEl_def
                  unfolding setWatch2_def
                  unfolding setWatch1_def
                  by (auto simp add: Let_def)
                hence "w1 = www1" and "w2 = www2"
                  using `Some www1 = (getWatch1 ?state' c)` `Some www2 = (getWatch2 ?state' c)`
                  using `c = length (getF state)`
                  by auto
                have "\<not> literalFalse  w1 (elements (getM ?state'))" 
                  "\<not> literalFalse w2 (elements (getM ?state'))"
                  using `w1 el ?clause'` `w2 el ?clause'`
                  using *
                  unfolding setWatch2_def
                  unfolding setWatch1_def
                  by (auto simp add: Let_def)
                thus ?thesis
                  using `w1 = www1` `w2 = www2`
                  unfolding watchCharacterizationCondition_def
                  unfolding setWatch2_def
                  unfolding setWatch1_def
                  by (auto simp add: Let_def)
              qed
            } thus ?thesis
              unfolding InvariantWatchCharacterization_def
              by auto
          qed
          moreover 
          have "\<forall> l. length (getF state) \<notin> set (getWatchList state l)"
            using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)`            
            unfolding InvariantWatchListsContainOnlyClausesFromF_def
            by auto
          hence "InvariantWatchListsUniq (getWatchList ?state')"
            using `InvariantWatchListsUniq (getWatchList state)`
            using `nth ?clause' 0 \<noteq> nth ?clause' 1`
            unfolding InvariantWatchListsUniq_def
            unfolding setWatch1_def
            unfolding setWatch2_def
            by (auto simp add:Let_def uniqAppendIff)
          moreover
          from * 
          have "\<not> clauseFalse ?clause' (elements (getM state))"
            using `?clause' \<noteq> []`
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          hence "InvariantConflictFlagCharacterization (getConflictFlag ?state') (getF ?state') (getM ?state')"
            using `InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)`
            unfolding InvariantConflictFlagCharacterization_def
            unfolding setWatch1_def
            unfolding setWatch2_def
            by (auto simp add: Let_def formulaFalseIffContainsFalseClause)
          moreover
          have "\<not> (\<exists> l. isUnitClause ?clause' l (elements (getM state)))"
          proof-
            {
              assume "\<not> ?thesis"
              then obtain l
                where "isUnitClause ?clause' l (elements (getM state))"
                by auto
              hence "l el ?clause'"
                unfolding isUnitClause_def
                by simp
              have "\<exists> l'. l' el ?clause' \<and> l \<noteq> l'"
              proof-
                from `length ?clause' > 1`
                obtain a1::Literal and a2::Literal
                  where "a1 el ?clause'" "a2 el ?clause'" "a1 \<noteq> a2"
                  using lengthGtOneTwoDistinctElements[of "?clause'"]
                  by (auto simp add: uniqDistinct) (force)
                thus ?thesis
                proof (cases "a1 = l")
                  case True
                  thus ?thesis
                    using `a1 \<noteq> a2` `a2 el ?clause'`
                    by auto
                next
                  case False
                  thus ?thesis
                    using `a1 el ?clause'`
                    by auto
                qed
              qed
              then obtain l'::Literal
                where "l \<noteq> l'" "l' el ?clause'"
                by auto
              with * 
              have "\<not> literalFalse l' (elements (getM state))"
                by simp
              hence "False"
                using `isUnitClause ?clause' l (elements (getM state))`
                using `l \<noteq> l'` `l' el ?clause'`
                unfolding isUnitClause_def
                by auto
            } thus ?thesis
              by auto
          qed
          hence "InvariantQCharacterization (getConflictFlag ?state') (getQ ?state') (getF ?state') (getM ?state')"
            using assms
            unfolding InvariantQCharacterization_def
            unfolding setWatch2_def
            unfolding setWatch1_def
            by (auto simp add: Let_def)
          moreover
          have "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state @ [?clause']) (getM state)"
          proof (cases "getConflictFlag state")
            case False
            thus ?thesis
              unfolding InvariantConflictClauseCharacterization_def
              by simp
          next
            case True
            hence "getConflictClause state < length (getF state)"
              using `InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)`
              unfolding InvariantConflictClauseCharacterization_def
              by (auto simp add: Let_def)
            hence "nth ((getF state) @ [?clause']) (getConflictClause state) = 
                   nth (getF state) (getConflictClause state)"
              by (simp add: nth_append)
            thus ?thesis
              using `InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)`
              unfolding InvariantConflictClauseCharacterization_def
              by (auto simp add: Let_def clauseFalseAppendValuation)
          qed
          moreover
          have "InvariantGetReasonIsReason (getReason ?state') (getF ?state') (getM ?state') (set (getQ ?state'))"
            using `currentLevel (getM state) = 0`
            using elementLevelLeqCurrentLevel[of _ "getM state"]
            unfolding setWatch1_def
            unfolding setWatch2_def
            unfolding InvariantGetReasonIsReason_def
            by (simp add: Let_def)
          moreover
          have "InvariantVarsF (getF ?state') F0 Vbl"
            using `InvariantVarsF (getF state) F0 Vbl`
            using `vars ?clause' \<subseteq> vars F0`
            using varsAppendFormulae[of "getF state" "[?clause']"]
            unfolding setWatch2_def
            unfolding setWatch1_def
            unfolding InvariantVarsF_def
            by (auto simp add: Let_def)
          ultimately
          show ?thesis
            using assms
            using `length ?clause' > 1`
            using `\<not> ?clause' = []`
            using `\<not> clauseTrue ?clause' (elements (getM state))`
            using `length ?clause' \<noteq> 1`
            using `\<not> clauseTautology ?clause'`
            unfolding addClause_def
            unfolding setWatch1_def
            unfolding setWatch2_def
            by (auto simp add: Let_def)
        qed
      qed
    qed
  qed
qed


lemma InvariantEquivalentZLAfterAddClause:
fixes Phi :: Formula and clause :: Clause and state :: State and Vbl :: "Variable set"
assumes 
*:"(getSATFlag state = UNDEF \<and> InvariantEquivalentZL (getF state) (getM state) Phi) \<or> 
   (getSATFlag state = FALSE \<and> \<not> satisfiable Phi)"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantUniqQ (getQ state)"
  "(getConflictFlag state) \<or> (getQ state) = []"
  "currentLevel (getM state) = 0"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
  "finite Vbl"
  "vars clause \<subseteq> vars F0"
shows
"let state' = addClause clause state in
 let Phi' = Phi @ [clause] in
 let Phi'' = (if (clauseTautology clause) then Phi else Phi') in
 (getSATFlag state' = UNDEF \<and> InvariantEquivalentZL (getF state') (getM state') Phi'') \<or> 
 (getSATFlag state' = FALSE \<and> \<not>satisfiable Phi'')"
proof-
  let ?clause' = "remdups (removeFalseLiterals clause (elements (getM state)))"

  from `currentLevel (getM state) = 0` 
  have "getM state = prefixToLevel 0 (getM state)"
    by (rule currentLevelZeroTrailEqualsItsPrefixToLevelZero)

  have **: "\<forall> l. l el ?clause' \<longrightarrow> \<not> literalFalse l (elements (getM state))"
    unfolding removeFalseLiterals_def
    by auto

  have "vars ?clause' \<subseteq> vars clause"
    using varsSubsetValuation[of "?clause'" "clause"]
    unfolding removeFalseLiterals_def
    by auto
  hence "vars ?clause' \<subseteq> vars F0"
    using `vars clause \<subseteq> vars F0`
    by simp

  show ?thesis
  proof (cases "clauseTrue ?clause' (elements (getM state))")
    case True
    show ?thesis
    proof-
      from True 
      have "clauseTrue clause (elements (getM state))"
        using clauseTrueRemoveDuplicateLiterals
        [of "removeFalseLiterals clause (elements (getM state))" "elements (getM state)"]
        using clauseTrueRemoveFalseLiterals
        [of "elements (getM state)" "clause"]
        using `InvariantConsistent (getM state)`
        unfolding InvariantConsistent_def
        by simp
      show ?thesis
      proof (cases "getSATFlag state = UNDEF")
        case True
        thus ?thesis
          using *
          using `clauseTrue clause (elements (getM state))`
          using `getM state = prefixToLevel 0 (getM state)`
          using satisfiedClauseCanBeRemoved
          [of "getF state" "(elements (prefixToLevel 0 (getM state)))" "Phi" "clause"]
          using `clauseTrue ?clause' (elements (getM state))`
          unfolding addClause_def
          unfolding InvariantEquivalentZL_def
          by auto
      next
        case False
        thus ?thesis
          using *
          using `clauseTrue ?clause' (elements (getM state))`
          using satisfiableAppend[of "Phi" "[clause]"]
          unfolding addClause_def
          by force
      qed
    qed
  next
    case False
    show ?thesis
    proof (cases "?clause' = []")
      case True
      show ?thesis
      proof (cases "getSATFlag state = UNDEF")
        case True
        thus ?thesis
          using *
          using falseAndDuplicateLiteralsCanBeRemoved
          [of "getF state" "(elements (prefixToLevel 0 (getM state)))" "[]" "Phi" "clause"]
          using `getM state = prefixToLevel 0 (getM state)`
          using formulaWithEmptyClauseIsUnsatisfiable[of "(getF state @ val2form (elements (getM state)) @ [[]])"]
          using satisfiableEquivalent
          using `?clause' = []`
          unfolding addClause_def
          unfolding InvariantEquivalentZL_def
          using satisfiableAppendTautology
          by auto
      next
        case False
        thus ?thesis
          using `?clause' = []`
          using *
          using satisfiableAppend[of "Phi" "[clause]"]
          unfolding addClause_def
          by force
      qed
    next
      case False
      thus ?thesis
      proof (cases "length ?clause' = 1")
        case True
        from `length ?clause' = 1`
        have "[hd ?clause'] = ?clause'"
          using lengthOneCharacterisation[of "?clause'"]
          by simp

        with `length ?clause' = 1`
        have "val2form (elements (getM state)) @ [?clause'] = val2form ((elements (getM state)) @ ?clause')"
          using val2formAppend[of "elements (getM state)" "?clause'"]
          using val2formOfSingleLiteralValuation[of "?clause'"]
          by auto

        let ?state' = "assertLiteral (hd ?clause') False state"
        have "addClause clause state = exhaustiveUnitPropagate ?state'"
          using `\<not> clauseTrue ?clause' (elements (getM state))`
          using `\<not> ?clause' = []`
          using `length ?clause' = 1`
          unfolding addClause_def
          by (simp add: Let_def)
        moreover
        from `?clause' \<noteq> []`
        have "hd ?clause' \<in> set ?clause'"
          using hd_in_set[of "?clause'"]
          by simp
        with **
        have "\<not> literalFalse (hd ?clause') (elements (getM state))"
          by simp
        hence "consistent (elements ((getM state) @ [(hd ?clause', False)]))"
          using assms
          unfolding InvariantConsistent_def
          using consistentAppendElement[of "elements (getM state)" "hd ?clause'"]
          by simp
        hence "consistent (elements (getM ?state'))"
          using assms
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          by simp
        moreover
        from `\<not> clauseTrue ?clause' (elements (getM state))`
        have "uniq (elements (getM ?state'))"
          using assms
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          using `hd ?clause' \<in> set ?clause'`
          unfolding InvariantUniq_def
          by (simp add: uniqAppendIff clauseTrueIffContainsTrueLiteral)
        moreover
        have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state') (getF ?state')" and
          "InvariantWatchListsUniq (getWatchList ?state')" and
          "InvariantWatchListsCharacterization (getWatchList ?state') (getWatch1 ?state') (getWatch2 ?state')"
          "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')" and
          "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
          using assms
          using WatchInvariantsAfterAssertLiteral[of "state" "hd ?clause'" "False"]
          by (auto simp add: Let_def)
        moreover
        have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') (getM ?state')"
          using assms
          using InvariantWatchCharacterizationAfterAssertLiteral[of "state" "hd ?clause'" "False"]
          using `uniq (elements (getM ?state'))`
          using `consistent (elements (getM ?state'))`
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          by (simp add: Let_def)
        moreover
        have "InvariantConflictFlagCharacterization (getConflictFlag ?state') (getF ?state') (getM ?state')"
          using assms
          using InvariantConflictFlagCharacterizationAfterAssertLiteral[of "state" "hd ?clause'" "False"]
          using `consistent (elements (getM ?state'))`
          unfolding InvariantConsistent_def
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          by (simp add: Let_def)
        moreover
        have "InvariantQCharacterization (getConflictFlag ?state') (getQ ?state') (getF ?state') (getM ?state')"
        proof (cases "getConflictFlag state")
          case True
          hence "getConflictFlag ?state'"
            using assms
            using assertLiteralConflictFlagEffect[of "state" "hd ?clause'" "False"]
            using `uniq (elements (getM ?state'))`
            using `consistent (elements (getM ?state'))`
            unfolding InvariantConsistent_def
            unfolding InvariantUniq_def
            using assertLiteralEffect[of "state" "hd ?clause'" "False"]
            by (auto simp add: Let_def)
          thus ?thesis
            using assms
            unfolding InvariantQCharacterization_def
            by simp
        next
          case False
          with `(getConflictFlag state) \<or> (getQ state) = []`
          have "getQ state = []"
            by simp
          thus ?thesis
            using InvariantQCharacterizationAfterAssertLiteralNotInQ[of "state" "hd ?clause'" "False"]
            using assms
            using `uniq (elements (getM ?state'))`
            using `consistent (elements (getM ?state'))`
            unfolding InvariantConsistent_def
            unfolding InvariantUniq_def
            using assertLiteralEffect[of "state" "hd ?clause'" "False"]
            by (auto simp add: Let_def)
        qed
        moreover
        have"InvariantUniqQ (getQ ?state')"
          using assms
          using InvariantUniqQAfterAssertLiteral[of "state" "hd ?clause'" "False"]
          by (simp add: Let_def)
        moreover
        have "currentLevel (getM ?state') = 0"
          using assms
          using `\<not> clauseTrue ?clause' (elements (getM state))`
          using `\<not> ?clause' = []`
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          unfolding addClause_def
          unfolding currentLevel_def
          by (simp add:Let_def markedElementsAppend)
        moreover
        have "var (hd ?clause') \<in> vars F0"
          using `?clause' \<noteq> []`
          using hd_in_set[of "?clause'"]
          using `vars ?clause' \<subseteq> vars F0`
          using clauseContainsItsLiteralsVariable[of "hd ?clause'" "?clause'"]
          by auto
        hence "InvariantVarsM (getM ?state') F0 Vbl"
          "InvariantVarsQ (getQ ?state') F0 Vbl"
          "InvariantVarsF (getF ?state') F0 Vbl"
          using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)`
          using `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
          using `InvariantWatchListsUniq (getWatchList state)`
          using `InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)`
          using `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
          using `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)`
          using `InvariantVarsF (getF state) F0 Vbl`
          using `InvariantVarsM (getM state) F0 Vbl`
          using `InvariantVarsQ (getQ state) F0 Vbl`
          using `consistent (elements (getM ?state'))`
          using `uniq (elements (getM ?state'))`
          using assertLiteralEffect[of "state" "hd ?clause'" "False"]
          using varsAppendValuation[of "elements (getM state)" "[hd ?clause']"]
          using InvariantVarsQAfterAssertLiteral[of "state" "hd ?clause'" "False" "F0" "Vbl"]
          unfolding InvariantVarsM_def
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          by (auto simp add: Let_def)
        moreover
        have "exhaustiveUnitPropagate_dom ?state'"
          using exhaustiveUnitPropagateTermination[of "?state'" "F0" "Vbl"]
          using `InvariantUniqQ (getQ ?state')`
          using `InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state') (getF ?state')`
          using `InvariantWatchListsUniq (getWatchList ?state')`
          using `InvariantWatchListsCharacterization (getWatchList ?state') (getWatch1 ?state') (getWatch2 ?state')`
          using `InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')`
          using `InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')`
          using `InvariantQCharacterization (getConflictFlag ?state') (getQ ?state') (getF ?state') (getM ?state')`
          using `InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') (getM ?state')`
          using `InvariantConflictFlagCharacterization (getConflictFlag ?state') (getF ?state') (getM ?state')`
          using `consistent (elements (getM ?state'))`
          using `uniq (elements (getM ?state'))`
          using `finite Vbl`
          using `InvariantVarsM (getM ?state') F0 Vbl`
          using `InvariantVarsQ (getQ ?state') F0 Vbl`
          using `InvariantVarsF (getF ?state') F0 Vbl`
          unfolding InvariantConsistent_def
          unfolding InvariantUniq_def
          by simp
        moreover
        have "\<not> clauseTautology clause"
        proof-
          {
            assume "\<not> ?thesis"
            then obtain l'
              where "l' el clause" "opposite l' el clause"
              by (auto simp add: clauseTautologyCharacterization)
            have False
            proof (cases "l' el ?clause'")
              case True
              have "opposite l' el ?clause'"
              proof-
                {
                  assume "\<not> ?thesis"
                  hence "literalFalse l' (elements (getM state))"
                    using `l' el clause`
                    using `opposite l' el clause`
                    using `\<not> clauseTrue ?clause' (elements (getM state))`
                    using clauseTrueIffContainsTrueLiteral[of "?clause'" "elements (getM state)"]
                    unfolding removeFalseLiterals_def
                    by auto
                  hence False
                    using `l' el ?clause'`
                    unfolding removeFalseLiterals_def
                    by auto
                } thus ?thesis
                  by auto
              qed
              have "\<forall> x. x el ?clause' \<longrightarrow> x = l'"
                using `l' el ?clause'`
                using `length ?clause' = 1`
                using lengthOneImpliesOnlyElement[of "?clause'" "l'"]
                by simp
              thus ?thesis
                using `opposite l' el ?clause'`
                by auto
            next
              case False
              hence "literalFalse l' (elements (getM state))"
                using `l' el clause`
                unfolding removeFalseLiterals_def
                by simp
              hence "\<not> literalFalse (opposite l') (elements (getM state))"
                using `InvariantConsistent (getM state)`
                unfolding InvariantConsistent_def
                by (auto simp add: inconsistentCharacterization)
              hence "opposite l' el ?clause'"
                using `opposite l' el clause`
                unfolding removeFalseLiterals_def
                by auto
              thus ?thesis
                using `literalFalse l' (elements (getM state))`
                using `\<not> clauseTrue ?clause' (elements (getM state))`
                by (simp add: clauseTrueIffContainsTrueLiteral)
            qed
          } thus ?thesis
            by auto
        qed
        moreover
        note clc = calculation

        show ?thesis
        proof (cases "getSATFlag state = UNDEF")
          case True
          hence "InvariantEquivalentZL (getF state) (getM state) Phi"
            using assms
            by simp
          hence "InvariantEquivalentZL (getF ?state') (getM ?state') (Phi @ [clause])"
            using *
            using falseAndDuplicateLiteralsCanBeRemoved
            [of "getF state" "(elements (prefixToLevel 0 (getM state)))" "[]" "Phi" "clause"]
            using `[hd ?clause'] = ?clause'`
            using `getM state = prefixToLevel 0 (getM state)`
            using `currentLevel (getM state) = 0`
            using prefixToLevelAppend[of "0" "getM state" "[(hd ?clause', False)]"]
            using `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
            using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)`
            using assertLiteralEffect[of "state" "hd ?clause'" "False"]
            using `val2form (elements (getM state)) @ [?clause'] = val2form ((elements (getM state)) @ ?clause')`
            using `\<not> ?clause' = []`
            using `\<not> clauseTrue ?clause' (elements (getM state))`
            using `length ?clause' = 1`
            using `getSATFlag state = UNDEF`
            unfolding addClause_def
            unfolding InvariantEquivalentZL_def
            by (simp add: Let_def)
          hence "let state'' = addClause clause state in
            InvariantEquivalentZL (getF state'') (getM state'') (Phi @ [clause]) \<and> 
            getSATFlag state'' = getSATFlag state"
            using clc
            using InvariantEquivalentZLAfterExhaustiveUnitPropagate[of "?state'" "Phi @ [clause]"]
            using exhaustiveUnitPropagatePreservedVariables[of "?state'"]
            using assms
            unfolding InvariantConsistent_def
            unfolding InvariantUniq_def
            using assertLiteralEffect[of "state" "hd ?clause'" "False"]
            by (auto simp only: Let_def)
          thus ?thesis
            using True
            using `\<not> clauseTautology clause`
            by (auto simp only: Let_def split: split_if) 
        next
          case False
          hence "getSATFlag state = FALSE" "\<not> satisfiable Phi"
            using *
            by auto
          hence "getSATFlag ?state' = FALSE"
            using assertLiteralEffect[of "state" "hd ?clause'" "False"]
            using assms
            by simp
          hence "getSATFlag (exhaustiveUnitPropagate ?state') = FALSE" 
            using clc
            using exhaustiveUnitPropagatePreservedVariables[of "?state'"]
            by (auto simp only: Let_def)
          moreover
          have "\<not> satisfiable (Phi @ [clause])"
            using satisfiableAppend[of "Phi" "[clause]"]
            using `\<not> satisfiable Phi`
            by auto
          ultimately
          show ?thesis
            using clc
            using `\<not> clauseTautology clause`
            by (simp only: Let_def) simp
        qed
      next
        case False
        thus ?thesis
        proof (cases "clauseTautology ?clause'")
          case True
          moreover
          hence "clauseTautology clause"
            unfolding removeFalseLiterals_def
            by (auto simp add: clauseTautologyCharacterization)
          ultimately
          show ?thesis
            using *
            using `\<not> ?clause' = []`
            using `\<not> clauseTrue ?clause' (elements (getM state))`
            using `length ?clause' \<noteq> 1`
            using satisfiableAppend[of "Phi" "[clause]"]
            unfolding addClause_def
            (* Tautology problem *)
            by (auto simp add: Let_def)
        next
          case False
          have "\<not> clauseTautology clause"
          proof-
            {
              assume "\<not> ?thesis"
              then obtain l' 
                where "l' el clause" "opposite l' el clause"
                by (auto simp add: clauseTautologyCharacterization)
              have False
              proof (cases "l' el ?clause'")
                case True
                hence "\<not> opposite l' el ?clause'"
                  using `\<not> clauseTautology ?clause'`
                  by (auto simp add: clauseTautologyCharacterization)
                hence "literalFalse (opposite l') (elements (getM state))"
                  using `opposite l' el clause`
                  unfolding removeFalseLiterals_def
                  by auto
                thus ?thesis
                  using `\<not> clauseTrue ?clause' (elements (getM state))`
                  using `l' el ?clause'`
                  by (simp add: clauseTrueIffContainsTrueLiteral)
              next
                case False
                hence "literalFalse l' (elements (getM state))"
                  using `l' el clause`
                  unfolding removeFalseLiterals_def
                  by auto
                hence "\<not> literalFalse (opposite l') (elements (getM state))"
                  using `InvariantConsistent (getM state)`
                  unfolding InvariantConsistent_def
                  by (auto simp add: inconsistentCharacterization)
                hence "opposite l' el ?clause'"
                  using `opposite l' el clause`
                  unfolding removeFalseLiterals_def
                  by auto
                thus ?thesis
                  using `\<not> clauseTrue ?clause' (elements (getM state))`
                  using `literalFalse l' (elements (getM state))`
                  by (simp add: clauseTrueIffContainsTrueLiteral)
              qed
            } thus ?thesis
              by auto
          qed
          show ?thesis
          proof (cases "getSATFlag state = UNDEF")
            case True
            show ?thesis
              using *
              using falseAndDuplicateLiteralsCanBeRemoved
              [of "getF state" "(elements (prefixToLevel 0 (getM state)))" "[]" "Phi" "clause"]
              using `getM state = prefixToLevel 0 (getM state)`
              using `\<not> ?clause' = []`
              using `\<not> clauseTrue ?clause' (elements (getM state))`
              using `length ?clause' \<noteq> 1`
              using `\<not> clauseTautology ?clause'`
              using `\<not> clauseTautology clause`
              using `getSATFlag state = UNDEF`
              unfolding addClause_def
              unfolding InvariantEquivalentZL_def
              unfolding setWatch1_def
              unfolding setWatch2_def
              using clauseOrderIrrelevant[of "getF state" "[?clause']" "val2form (elements (getM state))" "[]"]
              using equivalentFormulaeTransitivity[of 
                "getF state @ remdups (removeFalseLiterals clause (elements (getM state))) # val2form (elements (getM state))" 
                "getF state @ val2form (elements (getM state)) @ [remdups (removeFalseLiterals clause (elements (getM state)))]"
                "Phi @ [clause]"]
              by (auto simp add: Let_def)
          next
            case False
            thus ?thesis
              using *
              using satisfiableAppend[of "Phi" "[clause]"]
              using `\<not> clauseTrue ?clause' (elements (getM state))`
              using `length ?clause' \<noteq> 1`
              using `\<not> clauseTautology ?clause'`
              using `\<not> clauseTautology clause`
              unfolding addClause_def
              unfolding setWatch1_def
              unfolding setWatch2_def
              by (auto simp add: Let_def)
          qed
        qed
      qed
    qed
  qed
qed

(*********************************************************************************)
(*    I N I T I A L I Z E                                                        *)
(*********************************************************************************)

lemma InvariantsAfterInitializationStep:
fixes
  state :: State and Phi :: Formula and Vbl::"Variable set"
assumes
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))"
  "InvariantUniqQ (getQ state)"
  "(getConflictFlag state) \<or> (getQ state) = []"
  "currentLevel (getM state) = 0"
  "finite Vbl"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
  "state' = initialize Phi state"
  "set Phi \<subseteq> set F0"
shows
  "InvariantConsistent (getM state') \<and> 
   InvariantUniq (getM state') \<and> 
   InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state') \<and> 
   InvariantWatchListsUniq (getWatchList state') \<and> 
   InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and> 
   InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state') \<and> 
   InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state') \<and> 
   InvariantWatchCharacterization (getF state') (getWatch1 state') (getWatch2 state') (getM state') \<and> 
   InvariantConflictFlagCharacterization (getConflictFlag state') (getF state') (getM state') \<and> 
   InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state') \<and> 
   InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state') \<and> 
   InvariantUniqQ (getQ state') \<and> 
   InvariantGetReasonIsReason (getReason state') (getF state') (getM state') (set (getQ state')) \<and> 
   InvariantVarsM (getM state') F0 Vbl \<and> 
   InvariantVarsQ (getQ state') F0 Vbl \<and> 
   InvariantVarsF (getF state') F0 Vbl \<and> 
   ((getConflictFlag state') \<or> (getQ state') = []) \<and> 
   currentLevel (getM state') = 0" (is "?Inv state'")
using assms
proof (induct Phi arbitrary: state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Phi')
  let ?state' = "addClause clause state"
  have "?Inv ?state'"
    using Cons
    using InvariantsAfterAddClause[of "state" "F0" "Vbl" "clause"]
    using formulaContainsItsClausesVariables[of "clause" "F0"]
    by (simp add: Let_def)
  thus ?case
    using Cons(1)[of "?state'"] `finite Vbl` Cons(18) Cons(19) Cons(20) Cons(21) Cons(22)
    by (simp add: Let_def)
qed

lemma InvariantEquivalentZLAfterInitializationStep:
fixes Phi :: Formula
assumes
  "(getSATFlag state = UNDEF \<and> InvariantEquivalentZL (getF state) (getM state) (filter (\<lambda> c. \<not> clauseTautology c) Phi)) \<or> 
   (getSATFlag state = FALSE \<and> \<not> satisfiable (filter (\<lambda> c. \<not> clauseTautology c) Phi))"
  "InvariantConsistent (getM state)"
  "InvariantUniq (getM state)"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))"
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))"
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) (set (getQ state))"
  "InvariantUniqQ (getQ state)"
  "finite Vbl"
  "InvariantVarsM (getM state) F0 Vbl"
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
  "(getConflictFlag state) \<or> (getQ state) = []"
  "currentLevel (getM state) = 0"
  "F0 = Phi @ Phi'"
shows
  "let state' = initialize Phi' state in
     (getSATFlag state' = UNDEF \<and> InvariantEquivalentZL (getF state') (getM state') (filter (\<lambda> c. \<not> clauseTautology c) F0)) \<or> 
     (getSATFlag state' = FALSE \<and> \<not>satisfiable (filter (\<lambda> c. \<not> clauseTautology c) F0))"
using assms
proof (induct Phi' arbitrary: state Phi)
  case Nil
  thus ?case
    unfolding prefixToLevel_def equivalentFormulae_def
    by simp
next
  case (Cons clause Phi'')
  let ?filt = "\<lambda> F. (filter (\<lambda> c. \<not> clauseTautology c) F)"
  let ?state' = "addClause clause state"
  let ?Phi' = "?filt Phi @ [clause]"
  let ?Phi'' = "if clauseTautology clause then ?filt Phi else ?Phi'"
  from Cons
  have "getSATFlag ?state' = UNDEF \<and> InvariantEquivalentZL (getF ?state') (getM ?state') (?filt ?Phi'') \<or> 
        getSATFlag ?state' = FALSE \<and> \<not> satisfiable (?filt ?Phi'')"
    using formulaContainsItsClausesVariables[of "clause" "F0"]
    using InvariantEquivalentZLAfterAddClause[of "state" "?filt Phi" "F0" "Vbl" "clause"]
    by (simp add:Let_def)
  hence "getSATFlag ?state' = UNDEF \<and> InvariantEquivalentZL (getF ?state') (getM ?state') (?filt (Phi @ [clause])) \<or>
         getSATFlag ?state' = FALSE \<and> \<not> satisfiable (?filt (Phi @ [clause]))"
    by auto
  moreover
  from Cons
  have "InvariantConsistent (getM ?state') \<and> 
   InvariantUniq (getM ?state') \<and> 
   InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state') (getF ?state') \<and> 
   InvariantWatchListsUniq (getWatchList ?state') \<and> 
   InvariantWatchListsCharacterization (getWatchList ?state') (getWatch1 ?state') (getWatch2 ?state') \<and> 
   InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state') \<and> 
   InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state') \<and> 
   InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') (getM ?state') \<and> 
   InvariantConflictFlagCharacterization (getConflictFlag ?state') (getF ?state') (getM ?state') \<and> 
   InvariantConflictClauseCharacterization (getConflictFlag ?state') (getConflictClause ?state') (getF ?state') (getM ?state') \<and> 
   InvariantQCharacterization (getConflictFlag ?state') (getQ ?state') (getF ?state') (getM ?state') \<and> 
   InvariantGetReasonIsReason (getReason ?state') (getF ?state') (getM ?state') (set (getQ ?state')) \<and> 
   InvariantUniqQ (getQ ?state') \<and> 
   InvariantVarsM (getM ?state') F0 Vbl \<and> 
   InvariantVarsQ (getQ ?state') F0 Vbl \<and> 
   InvariantVarsF (getF ?state') F0 Vbl \<and> 
   ((getConflictFlag ?state') \<or> (getQ ?state') = []) \<and> 
   currentLevel (getM ?state') = 0"
    using formulaContainsItsClausesVariables[of "clause" "F0"]
    using InvariantsAfterAddClause
    by (simp add: Let_def)
  moreover
  hence "InvariantNoDecisionsWhenConflict (getF ?state') (getM ?state') (currentLevel (getM ?state'))"
    "InvariantNoDecisionsWhenUnit (getF ?state') (getM ?state') (currentLevel (getM ?state'))"
    unfolding InvariantNoDecisionsWhenConflict_def
    unfolding InvariantNoDecisionsWhenUnit_def
    by auto
  ultimately
  show ?case
    using Cons(1)[of "?state'" "Phi @ [clause]"] `finite Vbl` Cons(23) Cons(24)
    by (simp add: Let_def)
qed

lemma InvariantsAfterInitialization:
shows
  "let state' = (initialize F0 initialState) in
       InvariantConsistent (getM state') \<and> 
       InvariantUniq (getM state') \<and> 
       InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state') \<and> 
       InvariantWatchListsUniq (getWatchList state') \<and> 
       InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and> 
       InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state') \<and> 
       InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state') \<and> 
       InvariantWatchCharacterization (getF state') (getWatch1 state') (getWatch2 state') (getM state') \<and> 
       InvariantConflictFlagCharacterization (getConflictFlag state') (getF state') (getM state') \<and> 
       InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state') \<and> 
       InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state') \<and> 
       InvariantNoDecisionsWhenConflict (getF state') (getM state') (currentLevel (getM state')) \<and> 
       InvariantNoDecisionsWhenUnit (getF state') (getM state') (currentLevel (getM state')) \<and> 
       InvariantGetReasonIsReason (getReason state') (getF state') (getM state') (set (getQ state')) \<and> 
       InvariantUniqQ (getQ state') \<and> 
       InvariantVarsM (getM state') F0 {} \<and> 
       InvariantVarsQ (getQ state') F0 {} \<and> 
       InvariantVarsF (getF state') F0 {} \<and> 
       ((getConflictFlag state') \<or> (getQ state') = []) \<and> 
       currentLevel (getM state') = 0"
using assms
using InvariantsAfterInitializationStep[of "initialState" "{}" "F0" "initialize F0 initialState" "F0"]
unfolding initialState_def
unfolding InvariantConsistent_def
unfolding InvariantUniq_def
unfolding InvariantWatchListsContainOnlyClausesFromF_def
unfolding InvariantWatchListsUniq_def
unfolding InvariantWatchListsCharacterization_def
unfolding InvariantWatchesEl_def
unfolding InvariantWatchesDiffer_def
unfolding InvariantWatchCharacterization_def
unfolding watchCharacterizationCondition_def
unfolding InvariantConflictFlagCharacterization_def
unfolding InvariantConflictClauseCharacterization_def
unfolding InvariantQCharacterization_def
unfolding InvariantUniqQ_def
unfolding InvariantNoDecisionsWhenConflict_def
unfolding InvariantNoDecisionsWhenUnit_def
unfolding InvariantGetReasonIsReason_def
unfolding InvariantVarsM_def
unfolding InvariantVarsQ_def
unfolding InvariantVarsF_def
unfolding currentLevel_def
by (simp) (force)

lemma InvariantEquivalentZLAfterInitialization:
fixes F0 :: Formula
shows
  "let state' = (initialize F0 initialState) in
   let F0' = (filter (\<lambda> c. \<not> clauseTautology c) F0) in
     (getSATFlag state' = UNDEF \<and> InvariantEquivalentZL (getF state') (getM state') F0') \<or> 
     (getSATFlag state' = FALSE \<and> \<not> satisfiable F0')"
using InvariantEquivalentZLAfterInitializationStep[of "initialState" "[]" "{}" "F0" "F0"]
unfolding initialState_def
unfolding InvariantEquivalentZL_def
unfolding InvariantConsistent_def
unfolding InvariantUniq_def
unfolding InvariantWatchesEl_def
unfolding InvariantWatchesDiffer_def
unfolding InvariantWatchListsContainOnlyClausesFromF_def
unfolding InvariantWatchListsUniq_def
unfolding InvariantWatchListsCharacterization_def
unfolding InvariantWatchCharacterization_def
unfolding InvariantConflictFlagCharacterization_def
unfolding InvariantConflictClauseCharacterization_def
unfolding InvariantQCharacterization_def
unfolding InvariantNoDecisionsWhenConflict_def
unfolding InvariantNoDecisionsWhenUnit_def
unfolding InvariantGetReasonIsReason_def
unfolding InvariantVarsM_def
unfolding InvariantVarsQ_def
unfolding InvariantVarsF_def
unfolding watchCharacterizationCondition_def
unfolding InvariantUniqQ_def
unfolding prefixToLevel_def
unfolding equivalentFormulae_def
unfolding currentLevel_def
by (auto simp add: Let_def)

end