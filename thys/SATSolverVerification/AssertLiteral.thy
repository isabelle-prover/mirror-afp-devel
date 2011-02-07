(*    Title:              SatSolverVerification/AssertLiteral.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

theory AssertLiteral
imports SatSolverCode
begin

(*****************************************************************************)
(*   G E T   N O N   W A T C H E D  U N F A L S I F I E D   L I T E R A L    *)
(*****************************************************************************)

lemma getNonWatchedUnfalsifiedLiteralSomeCharacterization:
fixes clause :: Clause and w1 :: Literal and w2 :: Literal and M :: LiteralTrail and l :: Literal
assumes 
  "getNonWatchedUnfalsifiedLiteral clause w1 w2 M = Some l"
shows 
  "l el clause" "l \<noteq> w1" "l \<noteq> w2" "\<not> literalFalse l (elements M)"
using assms
by (induct clause) (auto split: split_if_asm)

lemma getNonWatchedUnfalsifiedLiteralNoneCharacterization:
fixes clause :: Clause and w1 :: Literal and w2 :: Literal and M :: LiteralTrail
assumes 
  "getNonWatchedUnfalsifiedLiteral clause w1 w2 M = None"
shows 
  "\<forall> l. l el clause \<and> l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements M)"
using assms
by (induct clause) (auto split: split_if_asm)

(*****************************************************************************)
(*   S W A P   W A T C H E S                                                 *)
(*****************************************************************************)

lemma swapWatchesEffect:
fixes clause::nat and state::State and clause'::nat
shows
  "getWatch1 (swapWatches clause state) clause' = (if clause = clause' then getWatch2 state clause' else getWatch1 state clause')" and
  "getWatch2 (swapWatches clause state) clause' = (if clause = clause' then getWatch1 state clause' else getWatch2 state clause')"
unfolding swapWatches_def
by auto

(*****************************************************************************)
(*    N O T I F Y    W A T C H E S                                           *)
(*****************************************************************************)

lemma notifyWatchesLoopPreservedVariables:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
   (getM state') = (getM state) \<and> 
   (getF state') = (getF state) \<and> 
   (getSATFlag state') = (getSATFlag state) \<and> 
   isPrefix (getQ state) (getQ state')
  " 
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    unfolding isPrefix_def
    by simp
next
  case (Cons clause Wl')
  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state \<and> 
        getSATFlag ?state' = getSATFlag state \<and> 
        getQ ?state' = getQ state
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(3)
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `Some literal = getWatch1 state clause`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state \<and> 
          getQ ?state'' = getQ state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state \<and> 
            getQ ?state'' = getQ state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state \<and> 
            getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            unfolding isPrefix_def
            by (auto simp add: Let_def split: split_if_asm)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state')) clause`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state \<and> 
          getQ ?state'' = getQ state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''"]
          using Cons(3)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state \<and> 
            getQ ?state'' = getQ state"
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state \<and>
            getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            unfolding isPrefix_def
            by (auto simp add: Let_def split: split_if_asm)
        qed
      qed
    qed
  qed
qed


lemma notifyWatchesStartQIreleveant:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF stateA) (getWatch1 stateA) (getWatch2 stateA)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF stateA)" and
  "getM stateA = getM stateB" and
  "getF stateA = getF stateB" and
  "getWatch1 stateA = getWatch1 stateB" and
  "getWatch2 stateA = getWatch2 stateB" and
  "getConflictFlag stateA = getConflictFlag stateB" and
  "getSATFlag stateA = getSATFlag stateB"
shows
  "let state' = (notifyWatches_loop literal Wl newWl stateA) in
   let state'' = (notifyWatches_loop literal Wl newWl stateB) in
     (getM state') = (getM state'') \<and> 
     (getF state') = (getF state'') \<and> 
     (getSATFlag state') = (getSATFlag state'') \<and> 
     (getConflictFlag state') = (getConflictFlag state'')
  " 
using assms
proof (induct Wl arbitrary: newWl stateA stateB)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF stateA)`
  have "0 \<le> clause \<and> clause < length (getF stateA)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 stateA clause = Some wa" and "getWatch2 stateA clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 stateA clause")
    case True
    hence "Some literal = getWatch1 stateB clause"
      using `getWatch1 stateA = getWatch1 stateB`
      by simp

    let ?state'A = "swapWatches clause stateA"
    let ?state'B = "swapWatches clause stateB"

    have 
      "getM ?state'A = getM ?state'B"
      "getF ?state'A = getF ?state'B"
      "getWatch1 ?state'A = getWatch1 ?state'B"
      "getWatch2 ?state'A = getWatch2 ?state'B"
      "getConflictFlag ?state'A = getConflictFlag ?state'B"
      "getSATFlag ?state'A = getSATFlag ?state'B"
      using Cons
      unfolding swapWatches_def
      by auto

    let ?w1 = wb
    have "getWatch1 ?state'A clause = Some ?w1"
      using `getWatch2 stateA clause = Some wb`
      unfolding swapWatches_def
      by auto
    hence "getWatch1 ?state'B clause = Some ?w1"
      using `getWatch1 ?state'A = getWatch1 ?state'B`
      by simp
    let ?w2 = wa
    have "getWatch2 ?state'A clause = Some ?w2"
      using `getWatch1 stateA clause = Some wa`
      unfolding swapWatches_def
      by auto    
    hence "getWatch2 ?state'B clause = Some ?w2"
      using `getWatch2 ?state'A = getWatch2 ?state'B`
      by simp

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'A))")
      case True
      hence "literalTrue ?w1 (elements (getM ?state'B))"
        using `getM ?state'A = getM ?state'B`
        by simp
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state'A) (getWatch1 ?state'A) (getWatch2 ?state'A)"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state'A = getM stateA \<and> 
        getF ?state'A = getF stateA \<and> 
        getSATFlag ?state'A = getSATFlag stateA \<and> 
        getQ ?state'A = getQ stateA
        "
        unfolding swapWatches_def
        by simp
      moreover
      have "getM ?state'B = getM stateB \<and> 
        getF ?state'B = getF stateB \<and> 
        getSATFlag ?state'B = getSATFlag stateB \<and> 
        getQ ?state'B = getQ stateB
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'A" "?state'B" "clause # newWl"]
        using `getM ?state'A = getM ?state'B`
        using `getF ?state'A = getF ?state'B`
        using `getWatch1 ?state'A = getWatch1 ?state'B`
        using `getWatch2 ?state'A = getWatch2 ?state'B`
        using `getConflictFlag ?state'A = getConflictFlag ?state'B`
        using `getSATFlag ?state'A = getSATFlag ?state'B`
        using Cons(3)
        using `getWatch1 ?state'A clause = Some ?w1`
        using `getWatch2 ?state'A clause = Some ?w2`
        using `getWatch1 ?state'B clause = Some ?w1`
        using `getWatch2 ?state'B clause = Some ?w2`
        using `Some literal = getWatch1 stateA clause`
        using `Some literal = getWatch1 stateB clause`
        using `literalTrue ?w1 (elements (getM ?state'A))`
        using `literalTrue ?w1 (elements (getM ?state'B))`
        by (simp add:Let_def)
    next
      case False
      hence "\<not> literalTrue ?w1 (elements (getM ?state'B))"
        using `getM ?state'A = getM ?state'B`
        by simp
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A)")
        case (Some l')
        hence "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = Some l'"
          using `getF ?state'A = getF ?state'B`
          using `getM ?state'A = getM ?state'B`
          by simp

        have "l' el (nth (getF ?state'A) clause)"
          using Some
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp
        hence "l' el (nth (getF ?state'B) clause)"
          using `getF ?state'A = getF ?state'B`
          by simp


        let ?state''A = "setWatch2 clause l' ?state'A"
        let ?state''B = "setWatch2 clause l' ?state'B"

        have 
          "getM ?state''A = getM ?state''B"
          "getF ?state''A = getF ?state''B"
          "getWatch1 ?state''A = getWatch1 ?state''B"
          "getWatch2 ?state''A = getWatch2 ?state''B"
          "getConflictFlag ?state''A = getConflictFlag ?state''B"
          "getSATFlag ?state''A = getSATFlag ?state''B"
          using Cons
          unfolding setWatch2_def
          unfolding swapWatches_def
          by auto


        from Cons(2)
        have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
          using `l' el (nth (getF ?state'A) clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state''A = getM stateA \<and>
          getF ?state''A = getF stateA \<and> 
          getSATFlag ?state''A = getSATFlag stateA \<and> 
          getQ ?state''A = getQ stateA"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state''B = getM stateB \<and> 
          getF ?state''B = getF stateB \<and> 
          getSATFlag ?state''B = getSATFlag stateB \<and> 
          getQ ?state''B = getQ stateB
          "
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''A" "?state''B" "newWl"]
          using `getM ?state''A = getM ?state''B`
          using `getF ?state''A = getF ?state''B`
          using `getWatch1 ?state''A = getWatch1 ?state''B`
          using `getWatch2 ?state''A = getWatch2 ?state''B`
          using `getConflictFlag ?state''A = getConflictFlag ?state''B`
          using `getSATFlag ?state''A = getSATFlag ?state''B`
          using Cons(3)
          using `getWatch1 ?state'A clause = Some ?w1`
          using `getWatch2 ?state'A clause = Some ?w2`
          using `getWatch1 ?state'B clause = Some ?w1`
          using `getWatch2 ?state'B clause = Some ?w2`
          using `Some literal = getWatch1 stateA clause`
          using `Some literal = getWatch1 stateB clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'A))`
          using `\<not> literalTrue ?w1 (elements (getM ?state'B))`
          using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = Some l'`
          using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = Some l'`
          by (simp add:Let_def)
      next
        case None
        hence "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None"
          using `getF ?state'A = getF ?state'B` `getM ?state'A = getM ?state'B`
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'A))")
          case True
          hence "literalFalse ?w1 (elements (getM ?state'B))"
            using `getM ?state'A = getM ?state'B`
            by simp

          let ?state''A = "?state'A\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          let ?state''B = "?state'B\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          have 
            "getM ?state''A = getM ?state''B"
            "getF ?state''A = getF ?state''B"
            "getWatch1 ?state''A = getWatch1 ?state''B"
            "getWatch2 ?state''A = getWatch2 ?state''B"
            "getConflictFlag ?state''A = getConflictFlag ?state''B"
            "getSATFlag ?state''A = getSATFlag ?state''B"
            using Cons
            unfolding swapWatches_def
            by auto
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state''A = getM stateA \<and>
          getF ?state''A = getF stateA \<and> 
          getSATFlag ?state''A = getSATFlag stateA \<and> 
            getQ ?state''A = getQ stateA"
            unfolding swapWatches_def
            by simp
          moreover
          have "getM ?state''B = getM stateB \<and>
          getF ?state''B = getF stateB \<and> 
          getSATFlag ?state''B = getSATFlag stateB \<and> 
            getQ ?state''B = getQ stateB"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(4) Cons(5)
            using Cons(1)[of "?state''A" "?state''B" "clause # newWl"]
            using `getM ?state''A = getM ?state''B`
            using `getF ?state''A = getF ?state''B`
            using `getWatch1 ?state''A = getWatch1 ?state''B`
            using `getWatch2 ?state''A = getWatch2 ?state''B`
            using `getConflictFlag ?state''A = getConflictFlag ?state''B`
            using `getSATFlag ?state''A = getSATFlag ?state''B`
            using Cons(3)
            using `getWatch1 ?state'A clause = Some ?w1`
            using `getWatch2 ?state'A clause = Some ?w2`
            using `getWatch1 ?state'B clause = Some ?w1`
            using `getWatch2 ?state'B clause = Some ?w2`
            using `Some literal = getWatch1 stateA clause`
            using `Some literal = getWatch1 stateB clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'A))`
            using `\<not> literalTrue ?w1 (elements (getM ?state'B))`
            using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = None`
            using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None`
            using `literalFalse ?w1 (elements (getM ?state'A))`
            using `literalFalse ?w1 (elements (getM ?state'B))`
            by (simp add:Let_def)
        next
          case False
          hence "\<not> literalFalse ?w1 (elements (getM ?state'B))"
            using `getM ?state'A = getM ?state'B`
            by simp
          let ?state''A = "setReason ?w1 clause (?state'A\<lparr>getQ := (if ?w1 el (getQ ?state'A) then (getQ ?state'A) else (getQ ?state'A) @ [?w1])\<rparr>)"
          let ?state''B = "setReason ?w1 clause (?state'B\<lparr>getQ := (if ?w1 el (getQ ?state'B) then (getQ ?state'B) else (getQ ?state'B) @ [?w1])\<rparr>)"
          
          have 
            "getM ?state''A = getM ?state''B"
            "getF ?state''A = getF ?state''B"
            "getWatch1 ?state''A = getWatch1 ?state''B"
            "getWatch2 ?state''A = getWatch2 ?state''B"
            "getConflictFlag ?state''A = getConflictFlag ?state''B"
            "getSATFlag ?state''A = getSATFlag ?state''B"
            using Cons
            unfolding setReason_def
            unfolding swapWatches_def
            by auto

          from Cons(2)
          have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state''A = getM stateA \<and>
            getF ?state''A = getF stateA \<and> 
            getSATFlag ?state''A = getSATFlag stateA \<and> 
            getQ ?state''A = (if ?w1 el (getQ stateA) then (getQ stateA) else (getQ stateA) @ [?w1])"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state''B = getM stateB \<and>
            getF ?state''B = getF stateB \<and> 
            getSATFlag ?state''B = getSATFlag stateB \<and> 
            getQ ?state''B = (if ?w1 el (getQ stateB) then (getQ stateB) else (getQ stateB) @ [?w1])"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(4) Cons(5)
            using Cons(1)[of "?state''A" "?state''B" "clause # newWl"]
            using `getM ?state''A = getM ?state''B`
            using `getF ?state''A = getF ?state''B`
            using `getWatch1 ?state''A = getWatch1 ?state''B`
            using `getWatch2 ?state''A = getWatch2 ?state''B`
            using `getConflictFlag ?state''A = getConflictFlag ?state''B`
            using `getSATFlag ?state''A = getSATFlag ?state''B`
            using Cons(3)
            using `getWatch1 ?state'A clause = Some ?w1`
            using `getWatch2 ?state'A clause = Some ?w2`
            using `getWatch1 ?state'B clause = Some ?w1`
            using `getWatch2 ?state'B clause = Some ?w2`
            using `Some literal = getWatch1 stateA clause`
            using `Some literal = getWatch1 stateB clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'A))`
            using `\<not> literalTrue ?w1 (elements (getM ?state'B))`
            using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = None`
            using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None`
            using `\<not> literalFalse ?w1 (elements (getM ?state'A))`
            using `\<not> literalFalse ?w1 (elements (getM ?state'B))`
            by (simp add:Let_def)
        qed
      qed
    qed
  next
    case False
    hence "Some literal \<noteq> getWatch1 stateB clause"
      using Cons
      by simp

    let ?state'A = stateA
    let ?state'B = stateB

    have 
      "getM ?state'A = getM ?state'B"
      "getF ?state'A = getF ?state'B"
      "getWatch1 ?state'A = getWatch1 ?state'B"
      "getWatch2 ?state'A = getWatch2 ?state'B"
      "getConflictFlag ?state'A = getConflictFlag ?state'B"
      "getSATFlag ?state'A = getSATFlag ?state'B"
      using Cons
      by auto

    let ?w1 = wa
    have "getWatch1 ?state'A clause = Some ?w1"
      using `getWatch1 stateA clause = Some wa`
      by auto
    hence "getWatch1 ?state'B clause = Some ?w1"
      using Cons
      by simp
    let ?w2 = wb
    have "getWatch2 ?state'A clause = Some ?w2"
      using `getWatch2 stateA clause = Some wb`
      by auto
    hence "getWatch2 ?state'B clause = Some ?w2"
      using Cons
      by simp

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'A))")
      case True
      hence "literalTrue ?w1 (elements (getM ?state'B))"
        using Cons
        by simp

      show ?thesis
        using Cons(1)[of "?state'A" "?state'B" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7) Cons(8) Cons(9)
        using `\<not> Some literal = getWatch1 stateA clause`
        using `\<not> Some literal = getWatch1 stateB clause`
        using `getWatch1 ?state'A clause = Some ?w1`
        using `getWatch1 ?state'B clause = Some ?w1`
        using `getWatch2 ?state'A clause = Some ?w2`
        using `getWatch2 ?state'B clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'A))`
        using `literalTrue ?w1 (elements (getM ?state'B))`
        by (simp add:Let_def)
    next
      case False
      hence "\<not> literalTrue ?w1 (elements (getM ?state'B))"
        using `getM ?state'A = getM ?state'B`
        by simp
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A)")
        case (Some l')
        hence "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = Some l'"
          using `getF ?state'A = getF ?state'B`
          using `getM ?state'A = getM ?state'B`
          by simp

        have "l' el (nth (getF ?state'A) clause)"
          using Some
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp
        hence "l' el (nth (getF ?state'B) clause)"
          using `getF ?state'A = getF ?state'B`
          by simp

        let ?state''A = "setWatch2 clause l' ?state'A"
        let ?state''B = "setWatch2 clause l' ?state'B"

        have 
          "getM ?state''A = getM ?state''B"
          "getF ?state''A = getF ?state''B"
          "getWatch1 ?state''A = getWatch1 ?state''B"
          "getWatch2 ?state''A = getWatch2 ?state''B"
          "getConflictFlag ?state''A = getConflictFlag ?state''B"
          "getSATFlag ?state''A = getSATFlag ?state''B"
          using Cons
          unfolding setWatch2_def
          by auto


        from Cons(2)
        have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
          using `l' el (nth (getF ?state'A) clause)`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state''A = getM stateA \<and>
          getF ?state''A = getF stateA \<and> 
          getSATFlag ?state''A = getSATFlag stateA \<and> 
          getQ ?state''A = getQ stateA"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''A" "?state''B" "newWl"]
          using `getM ?state''A = getM ?state''B`
          using `getF ?state''A = getF ?state''B`
          using `getWatch1 ?state''A = getWatch1 ?state''B`
          using `getWatch2 ?state''A = getWatch2 ?state''B`
          using `getConflictFlag ?state''A = getConflictFlag ?state''B`
          using `getSATFlag ?state''A = getSATFlag ?state''B`
          using Cons(3)
          using `getWatch1 ?state'A clause = Some ?w1`
          using `getWatch2 ?state'A clause = Some ?w2`
          using `getWatch1 ?state'B clause = Some ?w1`
          using `getWatch2 ?state'B clause = Some ?w2`
          using `\<not> Some literal = getWatch1 stateA clause`
          using `\<not> Some literal = getWatch1 stateB clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'A))`
          using `\<not> literalTrue ?w1 (elements (getM ?state'B))`
          using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = Some l'`
          using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = Some l'`
          by (simp add:Let_def)
      next
        case None
        hence "getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None"
          using `getF ?state'A = getF ?state'B` `getM ?state'A = getM ?state'B`
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'A))")
          case True
          hence "literalFalse ?w1 (elements (getM ?state'B))"
            using `getM ?state'A = getM ?state'B`
            by simp

          let ?state''A = "?state'A\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          let ?state''B = "?state'B\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          have 
            "getM ?state''A = getM ?state''B"
            "getF ?state''A = getF ?state''B"
            "getWatch1 ?state''A = getWatch1 ?state''B"
            "getWatch2 ?state''A = getWatch2 ?state''B"
            "getConflictFlag ?state''A = getConflictFlag ?state''B"
            "getSATFlag ?state''A = getSATFlag ?state''B"
            using Cons
            by auto
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state''A = getM stateA \<and>
          getF ?state''A = getF stateA \<and> 
          getSATFlag ?state''A = getSATFlag stateA \<and> 
            getQ ?state''A = getQ stateA"
            by simp
          ultimately
          show ?thesis
            using Cons(4) Cons(5)
            using Cons(1)[of "?state''A" "?state''B" "clause # newWl"]
            using `getM ?state''A = getM ?state''B`
            using `getF ?state''A = getF ?state''B`
            using `getWatch1 ?state''A = getWatch1 ?state''B`
            using `getWatch2 ?state''A = getWatch2 ?state''B`
            using `getConflictFlag ?state''A = getConflictFlag ?state''B`
            using `getSATFlag ?state''A = getSATFlag ?state''B`
            using Cons(3)
            using `getWatch1 ?state'A clause = Some ?w1`
            using `getWatch2 ?state'A clause = Some ?w2`
            using `getWatch1 ?state'B clause = Some ?w1`
            using `getWatch2 ?state'B clause = Some ?w2`
            using `\<not> Some literal = getWatch1 stateA clause`
            using `\<not> Some literal = getWatch1 stateB clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'A))`
            using `\<not> literalTrue ?w1 (elements (getM ?state'B))`
            using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = None`
            using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None`
            using `literalFalse ?w1 (elements (getM ?state'A))`
            using `literalFalse ?w1 (elements (getM ?state'B))`
            by (simp add:Let_def)
        next
          case False
          hence "\<not> literalFalse ?w1 (elements (getM ?state'B))"
            using `getM ?state'A = getM ?state'B`
            by simp
          let ?state''A = "setReason ?w1 clause (?state'A\<lparr>getQ := (if ?w1 el (getQ ?state'A) then (getQ ?state'A) else (getQ ?state'A) @ [?w1])\<rparr>)"
          let ?state''B = "setReason ?w1 clause (?state'B\<lparr>getQ := (if ?w1 el (getQ ?state'B) then (getQ ?state'B) else (getQ ?state'B) @ [?w1])\<rparr>)"
          
          have 
            "getM ?state''A = getM ?state''B"
            "getF ?state''A = getF ?state''B"
            "getWatch1 ?state''A = getWatch1 ?state''B"
            "getWatch2 ?state''A = getWatch2 ?state''B"
            "getConflictFlag ?state''A = getConflictFlag ?state''B"
            "getSATFlag ?state''A = getSATFlag ?state''B"
            using Cons
            unfolding setReason_def
            by auto

          from Cons(2)
          have "InvariantWatchesEl (getF ?state''A) (getWatch1 ?state''A) (getWatch2 ?state''A)"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state''A = getM stateA \<and>
            getF ?state''A = getF stateA \<and> 
            getSATFlag ?state''A = getSATFlag stateA \<and> 
            getQ ?state''A = (if ?w1 el (getQ stateA) then (getQ stateA) else (getQ stateA) @ [?w1])"
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(4) Cons(5)
            using Cons(1)[of "?state''A" "?state''B" "clause # newWl"]
            using `getM ?state''A = getM ?state''B`
            using `getF ?state''A = getF ?state''B`
            using `getWatch1 ?state''A = getWatch1 ?state''B`
            using `getWatch2 ?state''A = getWatch2 ?state''B`
            using `getConflictFlag ?state''A = getConflictFlag ?state''B`
            using `getSATFlag ?state''A = getSATFlag ?state''B`
            using Cons(3)
            using `getWatch1 ?state'A clause = Some ?w1`
            using `getWatch2 ?state'A clause = Some ?w2`
            using `getWatch1 ?state'B clause = Some ?w1`
            using `getWatch2 ?state'B clause = Some ?w2`
            using `\<not> Some literal = getWatch1 stateA clause`
            using `\<not> Some literal = getWatch1 stateB clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'A))`
            using `\<not> literalTrue ?w1 (elements (getM ?state'B))`
            using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'A) clause) ?w1 ?w2 (getM ?state'A) = None`
            using `getNonWatchedUnfalsifiedLiteral (nth (getF ?state'B) clause) ?w1 ?w2 (getM ?state'B) = None`
            using `\<not> literalFalse ?w1 (elements (getM ?state'A))`
            using `\<not> literalFalse ?w1 (elements (getM ?state'B))`
            by (simp add:Let_def)
        qed
      qed
    qed
  qed
qed

lemma notifyWatchesLoopPreservedWatches:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     \<forall> c. c \<notin> set Wl \<longrightarrow> (getWatch1 state' c) = (getWatch1 state c) \<and> (getWatch2 state' c) = (getWatch2 state c)
  " 
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state"
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(3)
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `Some literal = getWatch1 state clause`
        using `literalTrue ?w1 (elements (getM ?state'))`
        apply (simp add:Let_def)
        unfolding swapWatches_def
        by simp
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          apply (simp add: Let_def)
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            apply (simp add: Let_def)
            unfolding swapWatches_def
            by simp
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            apply (simp add: Let_def)
            unfolding setReason_def
            unfolding swapWatches_def
            by simp
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state')) clause`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''"]
          using Cons(3)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          apply (simp add: Let_def)
          unfolding setWatch2_def
          by simp
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state"
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state"
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            apply (simp add: Let_def)
            unfolding setReason_def
            by simp
        qed
      qed
    qed
  qed
qed

lemma InvariantWatchesElNotifyWatchesLoop:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause" and "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getF ?state' = getF state"
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons
        using `Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getF ?state'' = getF state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getF ?state'' = getF state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding setReason_def
            by simp       
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed

lemma InvariantWatchesDifferNotifyWatchesLoop:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause" and "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(3)
      have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesDiffer_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getF ?state' = getF state"
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(4)
        using `Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> literal" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          unfolding swapWatches_def
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' \<noteq> ?w1`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          unfolding InvariantWatchesDiffer_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getF ?state'' = getF state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto       
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          unfolding swapWatches_def
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' \<noteq> ?w1`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          unfolding InvariantWatchesDiffer_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getF ?state'' = getF state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding setReason_def
            by simp       
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed


lemma InvariantWatchListsContainOnlyClausesFromFNotifyWatchesLoop:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<or> c \<in> set newWl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    by simp
next
  case (Cons clause Wl')
  from `\<forall>c. c \<in> set (clause # Wl') \<or> c \<in> set newWl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause" and "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      from Cons(2)
      have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state') (getF ?state')"
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(3)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "(getF state) = (getF ?state')"
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons
        using `Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
          using `clause < length (getF state)`
          unfolding InvariantWatchListsContainOnlyClausesFromF_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "(getF state) = (getF ?state'')"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "(getF state) = (getF ?state'')"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
          using `clause < length (getF state)`
          unfolding setWatch2_def
          unfolding InvariantWatchListsContainOnlyClausesFromF_def
          by auto
        moreover 
        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "(getF state) = (getF ?state'')"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchListsContainOnlyClausesFromF (getWatchList ?state'') (getF ?state'')"
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getF ?state'' = getF state"
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed

lemma InvariantWatchListsCharacterizationNotifyWatchesLoop:
  fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
  assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)"
  "\<forall> (c::nat) (l::Literal). l \<noteq> literal \<longrightarrow>
             (c \<in> set (getWatchList state l)) = (Some l = getWatch1 state c \<or> Some l = getWatch2 state c)"
  "\<forall> (c::nat). (c \<in> set newWl \<or> c \<in> set Wl) = (Some literal = (getWatch1 state c) \<or> Some literal = (getWatch2 state c))"
  "set Wl \<inter> set newWl = {}"
  "uniq Wl"
  "uniq newWl"
  shows
  "let state' = (notifyWatches_loop literal Wl newWl state) in
     InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and>
     InvariantWatchListsUniq (getWatchList state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsUniq_def
    by simp
next
  case (Cons clause Wl')
  from `uniq (clause # Wl')`
  have "clause \<notin> set Wl'"
    by (simp add:uniqAppendIff)

  have "set Wl' \<inter> set (clause # newWl) = {}"
    using Cons(8)
    using `clause \<notin> set Wl'`
    by simp

  have "uniq Wl'"
    using Cons(9)
    using uniqAppendIff
    by simp
  
  have "uniq (clause # newWl)"
    using Cons(10) Cons(8)
    using uniqAppendIff
    by force

  from `\<forall>c. c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause" and "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(3)
      have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesDiffer_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(4)
      have "InvariantWatchListsUniq (getWatchList ?state')"
        unfolding InvariantWatchListsUniq_def
        unfolding swapWatches_def
        by auto
      moreover
      have "(getF ?state') = (getF state)" and "(getWatchList ?state') = (getWatchList state)"
        unfolding swapWatches_def
        by auto
      moreover 
      have "\<forall>c l. l \<noteq> literal \<longrightarrow>
        (c \<in> set (getWatchList ?state' l)) =
        (Some l = getWatch1 ?state' c \<or> Some l = getWatch2 ?state' c)"
        using Cons(6)
        using `(getWatchList ?state') = (getWatchList state)`
        using swapWatchesEffect
        by auto
      moreover 
      have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
        (Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c)"
        using Cons(7)
        using swapWatchesEffect
        by auto
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(5)
        using `Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq Wl'`
        using `uniq (clause # newWl)`
        using `set Wl' \<inter> set (clause # newWl) = {}`
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> literal" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          unfolding swapWatches_def
          by auto
        
        let ?state'' = "setWatch2 clause l' ?state'"
        
        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `getWatch1 ?state' clause = Some ?w1`
          using `l' \<noteq> ?w1`
          unfolding InvariantWatchesDiffer_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        moreover
        have "clause \<notin> set (getWatchList state l')"
          using `l' \<noteq> literal`
          using `l' \<noteq> ?w1` `l' \<noteq> ?w2`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using Cons(6)
          unfolding swapWatches_def
          by simp
        with Cons(4)
        have "InvariantWatchListsUniq (getWatchList ?state'')"
          unfolding InvariantWatchListsUniq_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          using uniqAppendIff
          by force
        moreover
        have "(getF ?state'') = (getF state)" and 
          "(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover 
        have "\<forall>c l. l \<noteq> literal \<longrightarrow>
          (c \<in> set (getWatchList ?state'' l)) =
          (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
        proof-
          {
            fix c::nat and l::Literal
            assume "l \<noteq> literal"
            have "(c \<in> set (getWatchList ?state'' l)) = (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            proof (cases "c = clause")
              case True
              show ?thesis
              proof (cases "l = l'")
                case True
                thus ?thesis
                  using `c = clause`
                  unfolding setWatch2_def
                  by simp
              next
                case False
                show ?thesis
                  using Cons(6)
                  using `(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))`
                  using `l \<noteq> l'`
                  using `l \<noteq> literal`
                  using `getWatch1 ?state' clause = Some ?w1`
                  using `getWatch2 ?state' clause = Some ?w2`
                  using `Some literal = getWatch1 state clause`
                  using `c = clause`
                  using swapWatchesEffect
                  unfolding swapWatches_def
                  unfolding setWatch2_def
                  by simp
              qed
            next
              case False
              thus ?thesis
                using Cons(6)
                using `l \<noteq> literal`
                using `(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))`
                using `c \<noteq> clause`
                unfolding setWatch2_def
                using swapWatchesEffect[of "clause" "state" "c"]
                by auto
            qed
          }
          thus ?thesis
            by simp
        qed
        moreover
        have "\<forall>c. (c \<in> set newWl \<or> c \<in> set Wl') =
          (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
        proof-
          show ?thesis
          proof
            fix c :: nat
            show "(c \<in> set newWl \<or> c \<in> set Wl') =
              (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            proof
              assume "c \<in> set newWl \<or> c \<in> set Wl'"
              show "Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
              proof-
                from `c \<in> set newWl \<or> c \<in> set Wl'`
                have "Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c"
                  using Cons(7)
                  by auto
                
                from Cons(8) `clause \<notin> set Wl'` `c \<in> set newWl \<or> c \<in> set Wl'`
                have "c \<noteq> clause"
                  by auto
                
                show ?thesis
                  using `Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c`
                  using `c \<noteq> clause`
                  using swapWatchesEffect
                  unfolding setWatch2_def
                  by simp
              qed
            next
              assume "Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
              show "c \<in> set newWl \<or> c \<in> set Wl'"
              proof-
                have "Some literal \<noteq> getWatch1 ?state'' clause \<and>  Some literal \<noteq> getWatch2 ?state'' clause"
                  using `l' \<noteq> literal`
                  using `clause < length (getF state)`
                  using `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
                  using `getWatch1 ?state' clause = Some ?w1`
                  using `getWatch2 ?state' clause = Some ?w2`
                  using `Some literal = getWatch1 state clause`
                  unfolding InvariantWatchesDiffer_def
                  unfolding setWatch2_def
                  unfolding swapWatches_def
                  by auto
                thus ?thesis
                  using `Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c`
                  using Cons(7)
                  using swapWatchesEffect
                  unfolding setWatch2_def
                  by (auto split: split_if_asm)
              qed
            qed
          qed
        qed
        moreover
        have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
          (Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c)"
          using Cons(7)
          using swapWatchesEffect
          by auto
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(5)
          using `uniq Wl'`
          using `uniq newWl`
          using `set Wl' \<inter> set (clause # newWl) = {}`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def fun_upd_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchListsUniq (getWatchList ?state'')"
            unfolding InvariantWatchListsUniq_def
            unfolding swapWatches_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')" and "(getWatchList state) = (getWatchList ?state'')" 
            unfolding swapWatches_def
            by auto
          moreover
          have "\<forall>c l. l \<noteq> literal \<longrightarrow>
            (c \<in> set (getWatchList ?state'' l)) =
            (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            using Cons(6)
            using `(getWatchList state) = (getWatchList ?state'')`
            using swapWatchesEffect
            by auto
          moreover 
          have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
            (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            using Cons(7)
            using swapWatchesEffect
            by auto
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(5)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            using `uniq (clause # newWl)`
            using `set Wl' \<inter> set (clause # newWl) = {}`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchListsUniq (getWatchList ?state'')"
            unfolding InvariantWatchListsUniq_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')" and "(getWatchList state) = (getWatchList ?state'')" 
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "\<forall>c l. l \<noteq> literal \<longrightarrow>
            (c \<in> set (getWatchList ?state'' l)) =
            (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            using Cons(6)
            using `(getWatchList state) = (getWatchList ?state'')`
            using swapWatchesEffect
            unfolding setReason_def
            by auto
          moreover 
          have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
            (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            using Cons(7)
            using swapWatchesEffect
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(5)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            using `uniq (clause # newWl)`
            using `set Wl' \<inter> set (clause # newWl) = {}`
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto    

    have "Some literal = getWatch2 state clause"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `Some literal \<noteq> getWatch1 state clause`
      using Cons(7)
      by force

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      from Cons(7) have
        "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
        (Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c)"
        by auto
      thus ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6)
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq (clause # newWl)`
        using `uniq Wl'`
        using `set Wl' \<inter> set (clause # newWl) = {}`
        by simp
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> literal" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          using `Some literal = getWatch2 state clause`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `getWatch1 ?state' clause = Some ?w1`
          using `l' \<noteq> ?w1`
          unfolding InvariantWatchesDiffer_def
          unfolding setWatch2_def
          by simp
        moreover
        have "clause \<notin> set (getWatchList state l')"
          using `l' \<noteq> literal`
          using `l' \<noteq> ?w1` `l' \<noteq> ?w2`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using Cons(6)
          by simp
        with Cons(4)
        have "InvariantWatchListsUniq (getWatchList ?state'')"
          unfolding InvariantWatchListsUniq_def
          unfolding setWatch2_def
          using uniqAppendIff
          by force
        moreover
        have "(getF ?state'') = (getF state)" and 
          "(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))"
          unfolding setWatch2_def
          by auto
        moreover 
        have "\<forall>c l. l \<noteq> literal \<longrightarrow>
          (c \<in> set (getWatchList ?state'' l)) =
          (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
        proof-
          {
            fix c::nat and l::Literal
            assume "l \<noteq> literal"
            have "(c \<in> set (getWatchList ?state'' l)) = (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            proof (cases "c = clause")
              case True
              show ?thesis
              proof (cases "l = l'")
                case True
                thus ?thesis
                  using `c = clause`
                  unfolding setWatch2_def
                  by simp
              next
                case False
                show ?thesis
                  using Cons(6)
                  using `(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))`
                  using `l \<noteq> l'`
                  using `l \<noteq> literal`
                  using `getWatch1 ?state' clause = Some ?w1`
                  using `getWatch2 ?state' clause = Some ?w2`
                  using `Some literal = getWatch2 state clause`
                  using `c = clause`
                  unfolding setWatch2_def
                  by simp
              qed
            next
              case False
              thus ?thesis
                using Cons(6)
                using `l \<noteq> literal`
                using `(getWatchList ?state'') = (getWatchList state)(l' := clause # (getWatchList state l'))`
                using `c \<noteq> clause`
                unfolding setWatch2_def
                by auto
            qed
          }
          thus ?thesis
            by simp
        qed
        moreover
        have "\<forall>c. (c \<in> set newWl \<or> c \<in> set Wl') =
          (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
        proof-
          show ?thesis
          proof
            fix c :: nat
            show "(c \<in> set newWl \<or> c \<in> set Wl') =
              (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            proof
              assume "c \<in> set newWl \<or> c \<in> set Wl'"
              show "Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
              proof-
                from `c \<in> set newWl \<or> c \<in> set Wl'`
                have "Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c"
                  using Cons(7)
                  by auto
                
                from Cons(8) `clause \<notin> set Wl'` `c \<in> set newWl \<or> c \<in> set Wl'`
                have "c \<noteq> clause"
                  by auto
                
                show ?thesis
                  using `Some literal = getWatch1 state c \<or> Some literal = getWatch2 state c`
                  using `c \<noteq> clause`
                  unfolding setWatch2_def
                  by simp
              qed
            next
              assume "Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
              show "c \<in> set newWl \<or> c \<in> set Wl'"
              proof-
                have "Some literal \<noteq> getWatch1 ?state'' clause \<and>  Some literal \<noteq> getWatch2 ?state'' clause"
                  using `l' \<noteq> literal`
                  using `clause < length (getF state)`
                  using `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
                  using `getWatch1 ?state' clause = Some ?w1`
                  using `getWatch2 ?state' clause = Some ?w2`
                  using `Some literal = getWatch2 state clause`
                  unfolding InvariantWatchesDiffer_def
                  unfolding setWatch2_def
                  by auto
                thus ?thesis
                  using `Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c`
                  using Cons(7)
                  unfolding setWatch2_def
                  by (auto split: split_if_asm)
              qed
            qed
          qed
        qed
        moreover
        have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
          (Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c)"
          using Cons(7)
          by auto
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(5)
          using `uniq Wl'`
          using `uniq newWl`
          using `set Wl' \<inter> set (clause # newWl) = {}`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def fun_upd_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchListsUniq (getWatchList ?state'')"
            unfolding InvariantWatchListsUniq_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')"
            by auto
          moreover
          have "\<forall>c l. l \<noteq> literal \<longrightarrow>
            (c \<in> set (getWatchList ?state'' l)) =
            (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            using Cons(6)
            by simp
          moreover 
          have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
            (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            using Cons(7)
            by auto
          ultimately
          have "let state' = notifyWatches_loop literal Wl' (clause # newWl) ?state'' in 
                      InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and>
                      InvariantWatchListsUniq (getWatchList state')"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(5)
            using `uniq Wl'`
            using `uniq (clause # newWl)`
            using `set Wl' \<inter> set (clause # newWl) = {}`
            apply (simp only: Let_def)
            by (simp (no_asm_use)) (simp)
          thus ?thesis
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal \<noteq>  getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"


          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchListsUniq (getWatchList ?state'')"
            unfolding InvariantWatchListsUniq_def
            unfolding setReason_def
            by auto
          moreover 
          have "(getF state) = (getF ?state'')"
            unfolding setReason_def
            by auto
          moreover
          have "\<forall>c l. l \<noteq> literal \<longrightarrow>
            (c \<in> set (getWatchList ?state'' l)) =
            (Some l = getWatch1 ?state'' c \<or> Some l = getWatch2 ?state'' c)"
            using Cons(6)
            unfolding setReason_def
            by auto
          moreover 
          have "\<forall>c. (c \<in> set (clause # newWl) \<or> c \<in> set Wl') =
            (Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c)"
            using Cons(7)
            unfolding setReason_def
            by auto
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(5)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            using `uniq (clause # newWl)`
            using `set Wl' \<inter> set (clause # newWl) = {}`
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed

lemma NotifyWatchesLoopWatchCharacterizationEffect:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantConsistent (getM state)" and
  "InvariantUniq (getM state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M"
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "getM state = M @ [(opposite literal, decision)]"
  "uniq Wl"
  "\<forall>  (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)"

shows
  "let state' = notifyWatches_loop literal Wl newWl state in
     \<forall> (c::nat). c \<in> set Wl \<longrightarrow> (\<forall> w1 w2.(Some w1 = (getWatch1 state' c) \<and> Some w2 = (getWatch2 state' c)) \<longrightarrow> 
      (watchCharacterizationCondition w1 w2 (getM state') (nth (getF state') c)  \<and> 
       watchCharacterizationCondition w2 w1 (getM state') (nth (getF state') c))
     )"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  have "uniq Wl'" "clause \<notin> set Wl'"
    using Cons(9)
    by (auto simp add: uniqAppendIff)
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    with True have
      "?w2 = literal"
      unfolding swapWatches_def
      by simp

    from `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `0 \<le> clause \<and> clause < length (getF state)`
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    from `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 \<noteq> ?w2"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `0 \<le> clause \<and> clause < length (getF state)`
      unfolding InvariantWatchesDiffer_def
      unfolding swapWatches_def
      by auto

    have "\<not> literalFalse ?w2 (elements M)"
      using `?w2 = literal`
      using Cons(5)
      using Cons(8)
      unfolding InvariantUniq_def
      by (simp add: uniqAppendIff)

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state'"

      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(3)
      have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesDiffer_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(4)
      have "InvariantConsistent (getM ?state')"
        unfolding InvariantConsistent_def
        unfolding swapWatches_def
        by simp
      moreover
      from Cons(5)
      have "InvariantUniq (getM ?state')"
        unfolding InvariantUniq_def
        unfolding swapWatches_def
        by simp
      moreover
      from Cons(6)
      have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') M"
        unfolding swapWatches_def
        unfolding InvariantWatchCharacterization_def
        unfolding watchCharacterizationCondition_def
        by simp
      moreover
      have "getM ?state' = getM state"
        "getF ?state' = getF state"
        unfolding swapWatches_def
        by auto
      moreover 
      have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state' c)  \<or> Some literal = (getWatch2 ?state' c)"
        using Cons(10)
        unfolding swapWatches_def
        by auto
      moreover
      have "getWatch1 ?fState clause = getWatch1 ?state' clause \<and> getWatch2 ?fState clause = getWatch2 ?state' clause"
        using `clause \<notin> set Wl'`
        using `InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')` `getF ?state' = getF state`
        using Cons(7)
        using notifyWatchesLoopPreservedWatches[of "?state'" "Wl'" "literal" "clause # newWl" ]
        by (simp add: Let_def)
      moreover
      have "watchCharacterizationCondition ?w1 ?w2 (getM ?fState) (getF ?fState ! clause) \<and>
            watchCharacterizationCondition ?w2 ?w1 (getM ?fState) (getF ?fState ! clause)"
      proof-
        have "(getM ?fState) = (getM state) \<and> (getF ?fState = getF state)"
          using notifyWatchesLoopPreservedVariables[of "?state'" "Wl'" "literal" "clause # newWl"]
          using `InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')` `getF ?state' = getF state`
          using Cons(7)
          unfolding swapWatches_def
          by (simp add: Let_def)
        moreover
        have "\<not> literalFalse ?w1 (elements M)"
          using `literalTrue ?w1 (elements (getM ?state'))` `?w1 \<noteq> ?w2` `?w2 = literal`
          using Cons(4) Cons(8)
          unfolding InvariantConsistent_def
          unfolding swapWatches_def
          by (auto simp add: inconsistentCharacterization)
        moreover 
        have "elementLevel (opposite ?w2) (getM ?state') = currentLevel (getM ?state')"
          using `?w2 = literal`
          using Cons(5) Cons(8)
          unfolding InvariantUniq_def
          unfolding swapWatches_def
          by (auto simp add: uniqAppendIff elementOnCurrentLevel)
        ultimately
        show ?thesis
          using `getWatch1 ?fState clause = getWatch1 ?state' clause \<and> getWatch2 ?fState clause = getWatch2 ?state' clause`
          using `?w2 = literal` `?w1 \<noteq> ?w2`
          using `?w1 el (nth (getF state) clause)`
          using `literalTrue ?w1 (elements (getM ?state'))`
          unfolding watchCharacterizationCondition_def
          using elementLevelLeqCurrentLevel[of "?w1" "getM ?state'"]
          using notifyWatchesLoopPreservedVariables[of "?state'" "Wl'" "literal" "clause # newWl"]
          using `InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')` `getF ?state' = getF state`
          using Cons(7) 
          using Cons(8)
          unfolding swapWatches_def
          by (auto simp add: Let_def)
      qed
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(7) Cons(8)
        using `uniq Wl'`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `Some literal = getWatch1 state clause`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> ?w1" "l' \<noteq> ?w2" "\<not> literalFalse l' (elements (getM ?state'))"
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"
        let ?fState = "notifyWatches_loop literal Wl' newWl ?state''"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' \<noteq> ?w1`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          unfolding InvariantWatchesDiffer_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantConsistent (getM ?state'')"
          unfolding InvariantConsistent_def
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
        moreover
        from Cons(5)
        have "InvariantUniq (getM ?state'')"
          unfolding InvariantUniq_def
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
        moreover
        have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
        proof-
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww1 (elements M)"
              
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww1) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww1) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                unfolding setWatch2_def
                by simp
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using `getWatch1 ?state' clause = Some ?w1`
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              
              have "\<not> (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(8)
                using `l' \<noteq> ?w1` and `l' \<noteq> ?w2` `l' el (nth (getF ?state') clause)`
                using `\<not> literalFalse l' (elements (getM ?state'))`
                using a and b
                using `c = clause`
                unfolding swapWatches_def
                unfolding setWatch2_def
                by auto
              moreover
              have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> 
                elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                using `0 \<le> clause \<and> clause < length (getF state)`
                using `getWatch1 ?state' clause = Some ?w1`[THEN sym]
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                using `literalFalse ww1 (elements M)`
                using `ww1 = ?w1`
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              ultimately
              show ?thesis
                using `ww1 = ?w1`
                using `c = clause`
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
            qed
          }
          moreover 
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww2 (elements M)"
            
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww2) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww2) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using `getWatch1 ?state' clause = Some ?w1`
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              with `\<not> literalFalse l' (elements (getM ?state'))` b
                Cons(8)
              have False
                unfolding swapWatches_def
                by simp
              thus ?thesis
                by simp
            qed
          }
          ultimately
          show ?thesis
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by blast
        qed
        moreover 
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(10)
          using `clause \<notin> set Wl'`
          using swapWatchesEffect[of "clause" "state"]
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state"
          "getF ?state'' = getF state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getWatch1 ?state'' clause = Some ?w1" "getWatch2 ?state'' clause = Some l'"
          using `getWatch1 ?state' clause = Some ?w1`
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        hence "getWatch1 ?fState clause = getWatch1 ?state'' clause \<and> getWatch2 ?fState clause = Some l'"
          using `clause \<notin> set Wl'`
          using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
          using Cons(7)
          using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "newWl"]
          by (simp add: Let_def)
        moreover
        have "watchCharacterizationCondition ?w1 l' (getM ?fState) (getF ?fState ! clause) \<and>
          watchCharacterizationCondition l' ?w1 (getM ?fState) (getF ?fState ! clause)"
        proof-
          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "newWl"]
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            unfolding setWatch2_def
            unfolding swapWatches_def
            by (auto simp add: Let_def)
          
          have "literalFalse ?w1 (elements M) \<longrightarrow> 
            (\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M)"
          proof
            assume "literalFalse ?w1 (elements M)"
            show "\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M"
            proof-
              have "\<not> (\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using `l' el (nth (getF ?state') clause)` `l' \<noteq> ?w1` `l' \<noteq> ?w2` `\<not> literalFalse l' (elements (getM ?state'))`
                using Cons(8)
                unfolding swapWatches_def
                by auto

              from `literalFalse ?w1 (elements M)` Cons(6)
              have
                "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                 (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M)"
                using `0 \<le> clause \<and> clause < length (getF state)`
                using `getWatch1 ?state' clause = Some ?w1`[THEN sym]
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                by simp
              with `\<not> (\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))`
              have "\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M"
                by auto
              thus ?thesis
                unfolding setWatch2_def
                unfolding swapWatches_def
                by simp
            qed
          qed
          
          have "watchCharacterizationCondition l' ?w1 (getM ?fState) (getF ?fState ! clause)"
            using `\<not> literalFalse l' (elements (getM ?state'))`
            using `getM ?fState = getM state` 
            unfolding swapWatches_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "watchCharacterizationCondition ?w1 l' (getM ?fState) (getF ?fState ! clause)"
          proof (cases "literalFalse ?w1 (elements (getM ?fState))")
            case True
            hence "literalFalse ?w1 (elements M)"
              using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "newWl"]
              using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
              using Cons(7) Cons(8)
              using `?w1 \<noteq> ?w2` `?w2 = literal`
              unfolding setWatch2_def
              unfolding swapWatches_def
              by (simp add: Let_def)
            with `literalFalse ?w1 (elements M) \<longrightarrow> 
              (\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M)`
            obtain l::Literal
              where "l el (nth (getF ?state'') clause)" and 
              "literalTrue l (elements M)" and 
              "elementLevel l M \<le> elementLevel (opposite ?w1) M"
              by auto
            hence "elementLevel l (getM state) \<le> elementLevel (opposite ?w1) (getM state)"
              using Cons(8)
              using `literalTrue l (elements M)` `literalFalse ?w1 (elements M)`
              using elementLevelAppend[of "l" "M" "[(opposite literal, decision)]"]
              using elementLevelAppend[of "opposite ?w1" "M" "[(opposite literal, decision)]"]
              by auto
            thus ?thesis
              using `l el (nth (getF ?state'') clause)` `literalTrue l (elements M)`
              using `getM ?fState = getM state` `getF ?fState = getF state` `getM ?state'' = getM state` `getF ?state'' = getF state`
              using Cons(8)
              unfolding watchCharacterizationCondition_def
              by auto
          next
            case False
            thus ?thesis
              unfolding watchCharacterizationCondition_def
              by simp
          qed
          ultimately
          show ?thesis
            by simp
        qed
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(7) Cons(8)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using `getWatch1 ?state'' clause = Some ?w1`
          using `getWatch2 ?state'' clause = Some l'`
          using Some
          using `uniq Wl'`
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state')"
            unfolding InvariantConsistent_def
            unfolding swapWatches_def
            by simp
          moreover
          from Cons(5)
          have "InvariantUniq (getM ?state')"
            unfolding InvariantUniq_def
            unfolding swapWatches_def
            by simp
          moreover
          from Cons(6)
          have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') M"
            unfolding swapWatches_def
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(10)
            using `clause \<notin> set Wl'`
            using swapWatchesEffect[of "clause" "state"]
            by simp
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            unfolding swapWatches_def
            by auto
          moreover
          have "getWatch1 ?fState clause = getWatch1 ?state'' clause \<and> getWatch2 ?fState clause = getWatch2 ?state'' clause"
            using `clause \<notin> set Wl'`
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "clause # newWl" ]
            by (simp add: Let_def)
          moreover
          have "literalFalse ?w1 (elements M)"
            using `literalFalse ?w1 (elements (getM ?state'))`
              `?w1 \<noteq> ?w2` `?w2 = literal` Cons(8)
            unfolding swapWatches_def
            by auto

          have "\<not> literalTrue ?w2 (elements M)"
            using Cons(4)
            using Cons(8)
            using `?w2 = literal`
            using inconsistentCharacterization[of "elements M @ [opposite literal]"]
            unfolding InvariantConsistent_def
            by force

          have *: "\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
            literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M"
          proof-
            have "\<not> (\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M))"
            proof
              assume "\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M)"
              show "False"
              proof-
                from `\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M)`
                obtain l 
                  where "l el (nth (getF state) clause)" "literalTrue l (elements M)"
                  by auto
                hence "l \<noteq> ?w1" "l \<noteq> ?w2"
                  using `\<not> literalTrue ?w1 (elements (getM ?state'))`
                  using `\<not> literalTrue ?w2 (elements M)`
                  unfolding swapWatches_def
                  using Cons(8)
                  by auto
                with `l el (nth (getF state) clause)`
                have "literalFalse l (elements (getM ?state'))"
                  using `getWatch1 ?state' clause = Some ?w1`
                  using `getWatch2 ?state' clause = Some ?w2`
                  using None
                  using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
                  unfolding swapWatches_def
                  by simp
                with `l \<noteq> ?w2` `?w2 = literal` Cons(8)
                have "literalFalse l (elements M)"
                  unfolding swapWatches_def
                  by simp
                with Cons(4) `literalTrue l (elements M)`
                show ?thesis
                  unfolding InvariantConsistent_def
                  using Cons(8)
                  by (auto simp add: inconsistentCharacterization)
              qed
            qed
            with `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M`
            show ?thesis
              unfolding InvariantWatchCharacterization_def
              using `literalFalse ?w1 (elements M)`
              using `getWatch1 ?state' clause = Some ?w1`[THEN sym]
              using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
              using `0 \<le> clause \<and> clause < length (getF state)`
              unfolding watchCharacterizationCondition_def
              unfolding swapWatches_def
              by (simp) (blast)
          qed
          
          have **: "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements (getM ?state'')) \<and> 
                      elementLevel (opposite l) (getM ?state'') \<le> elementLevel (opposite ?w1) (getM ?state'')"
          proof-
            {

              fix l::Literal
              assume "l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2"


              have "literalFalse l (elements (getM ?state'')) \<and> 
                    elementLevel (opposite l) (getM ?state'') \<le> elementLevel (opposite ?w1) (getM ?state'')"
              proof-
                from * `l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2`
                have "literalFalse l (elements M)" "elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M"
                  unfolding swapWatches_def
                  by auto
                thus ?thesis
                  using elementLevelAppend[of "opposite l" "M" "[(opposite literal, decision)]"]
                  using `literalFalse ?w1 (elements M)`
                  using elementLevelAppend[of "opposite ?w1" "M" "[(opposite literal, decision)]"]
                  using Cons(8)
                  unfolding swapWatches_def
                  by simp
              qed
            }
            thus ?thesis
              by simp
          qed

          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            unfolding swapWatches_def
            by (auto simp add: Let_def)
          hence "\<forall> l. l el (nth (getF ?fState) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements (getM ?fState)) \<and> 
                      elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w1) (getM ?fState)"
            using **
            using `getM ?state'' = getM state`
            using `getF ?state'' = getF state`
            by simp
          moreover
          have "\<forall> l. literalFalse l (elements (getM ?fState)) \<longrightarrow> 
                     elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w2) (getM ?fState)"
          proof-
            have "elementLevel (opposite ?w2) (getM ?fState) = currentLevel (getM ?fState)"
              using Cons(8)
              using `(getM ?fState) = (getM state)`
              using `\<not> literalFalse ?w2 (elements M)`
              using `?w2 = literal`
              using elementOnCurrentLevel[of "opposite ?w2" "M" "decision"]
              by simp
            thus ?thesis
              by (simp add: elementLevelLeqCurrentLevel)
          qed
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(7) Cons(8)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            unfolding watchCharacterizationCondition_def
            by (simp add: Let_def)
        next
          case False

          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding InvariantConsistent_def
            unfolding setReason_def
            unfolding swapWatches_def
            by simp
          moreover
          from Cons(5)
          have "InvariantUniq (getM ?state'')"
            unfolding InvariantUniq_def
            unfolding setReason_def
            unfolding swapWatches_def
            by simp
          moreover
          from Cons(6)
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            unfolding swapWatches_def
            unfolding setReason_def
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(10)
            using `clause \<notin> set Wl'`
            using swapWatchesEffect[of "clause" "state"]
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getWatch1 ?state'' clause = Some ?w1" "getWatch2 ?state'' clause = Some ?w2"
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getWatch1 ?fState clause = Some ?w1" "getWatch2 ?fState clause = Some ?w2"
            using `getWatch1 ?state'' clause = Some ?w1` `getWatch2 ?state'' clause = Some ?w2`
            using `clause \<notin> set Wl'`
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "clause # newWl" ]
            by (auto simp add: Let_def)
          moreover
          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            unfolding setReason_def
            unfolding swapWatches_def
            by (auto simp add: Let_def)
          ultimately 
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> (\<forall>w1 w2. Some w1 = getWatch1 ?fState c \<and> Some w2 = getWatch2 ?fState c \<longrightarrow>
               watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! c) \<and>
               watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! c))" and
               "?fState = notifyWatches_loop literal (clause # Wl') newWl state"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(7) Cons(8)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (auto simp add: Let_def)
          moreover
          have *: "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state''))"
            using None
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
            using Cons(8)
            unfolding setReason_def
            unfolding swapWatches_def
            by auto

          have**: "\<forall> l. l el (nth (getF ?fState) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?fState))"
            using `(getM ?fState) = (getM state)` `(getF ?fState) = (getF state)`
            using *
            using `getM ?state'' = getM state`
            using `getF ?state'' = getF state`
            unfolding swapWatches_def
            by auto

          have ***: "\<forall> l. literalFalse l (elements (getM ?fState)) \<longrightarrow> 
                     elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w2) (getM ?fState)"
          proof-
            have "elementLevel (opposite ?w2) (getM ?fState) = currentLevel (getM ?fState)"
              using Cons(8)
              using `(getM ?fState) = (getM state)`
              using `\<not> literalFalse ?w2 (elements M)`
              using `?w2 = literal`
              using elementOnCurrentLevel[of "opposite ?w2" "M" "decision"]
              by simp
            thus ?thesis
              by (simp add: elementLevelLeqCurrentLevel)
          qed

          have "(\<forall>w1 w2. Some w1 = getWatch1 ?fState clause \<and> Some w2 = getWatch2 ?fState clause \<longrightarrow>
            watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! clause) \<and>
            watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! clause))"
          proof-
            {
              fix w1 w2
              assume "Some w1 = getWatch1 ?fState clause \<and> Some w2 = getWatch2 ?fState clause"
              hence "w1 = ?w1" "w2 = ?w2"
                using `getWatch1 ?fState clause = Some ?w1`
                using `getWatch2 ?fState clause = Some ?w2`
                by auto
              hence "watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! clause) \<and>
                watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! clause)"
                unfolding watchCharacterizationCondition_def
                using ** ***
                unfolding watchCharacterizationCondition_def
                using `(getM ?fState) = (getM state)` `(getF ?fState) = (getF state)`
                using `\<not> literalFalse ?w1 (elements (getM ?state'))`
                unfolding swapWatches_def
                by simp
            }
            thus ?thesis
              by auto
          qed
          ultimately
          show ?thesis
            by simp
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      by auto
    
    from `\<not> Some literal = getWatch1 state clause`
      `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)`
    have "Some literal = getWatch2 state clause"
      by auto
    hence "?w2 = literal"
      using `getWatch2 ?state' clause = Some ?w2`
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(8)
      by simp

    from `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `0 \<le> clause \<and> clause < length (getF state)`
      unfolding InvariantWatchesEl_def
      by auto

    from `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 \<noteq> ?w2"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `0 \<le> clause \<and> clause < length (getF state)`
      unfolding InvariantWatchesDiffer_def
      by auto

    have "\<not> literalFalse ?w2 (elements M)"
      using `?w2 = literal`
      using Cons(5)
      using Cons(8)
      unfolding InvariantUniq_def
      by (simp add: uniqAppendIff)

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state'"

      have "getWatch1 ?fState clause = getWatch1 ?state' clause \<and> getWatch2 ?fState clause = getWatch2 ?state' clause"
        using `clause \<notin> set Wl'`
        using Cons(2) 
        using Cons(7)
        using notifyWatchesLoopPreservedWatches[of "?state'" "Wl'" "literal" "clause # newWl" ]
        by (simp add: Let_def)
      moreover
      have "watchCharacterizationCondition ?w1 ?w2 (getM ?fState) (getF ?fState ! clause) \<and>
            watchCharacterizationCondition ?w2 ?w1 (getM ?fState) (getF ?fState ! clause)"
      proof-
        have "(getM ?fState) = (getM state) \<and> (getF ?fState = getF state)"
          using notifyWatchesLoopPreservedVariables[of "?state'" "Wl'" "literal" "clause # newWl"]
          using Cons(2)
          using Cons(7)
          by (simp add: Let_def)
        moreover
        have "\<not> literalFalse ?w1 (elements M)"
          using `literalTrue ?w1 (elements (getM ?state'))` `?w1 \<noteq> ?w2` `?w2 = literal`
          using Cons(4) Cons(8)
          unfolding InvariantConsistent_def
          by (auto simp add: inconsistentCharacterization)
        moreover 
        have "elementLevel (opposite ?w2) (getM ?state') = currentLevel (getM ?state')"
          using `?w2 = literal`
          using Cons(5) Cons(8)
          unfolding InvariantUniq_def
          by (auto simp add: uniqAppendIff elementOnCurrentLevel)
        ultimately
        show ?thesis
          using `getWatch1 ?fState clause = getWatch1 ?state' clause \<and> getWatch2 ?fState clause = getWatch2 ?state' clause`
          using `?w2 = literal` `?w1 \<noteq> ?w2`
          using `?w1 el (nth (getF state) clause)`
          using `literalTrue ?w1 (elements (getM ?state'))`
          unfolding watchCharacterizationCondition_def
          using elementLevelLeqCurrentLevel[of "?w1" "getM ?state'"]
          using notifyWatchesLoopPreservedVariables[of "?state'" "Wl'" "literal" "clause # newWl"]
          using `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)` 
          using Cons(7) 
          using Cons(8)
          by (auto simp add: Let_def)
      qed
      ultimately
      show ?thesis
        using assms
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7) Cons(8) Cons(9) Cons(10)
        using `uniq Wl'`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `Some literal = getWatch2 state clause`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `?w1 \<noteq> ?w2`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "l' \<noteq> ?w1" "l' \<noteq> ?w2" "\<not> literalFalse l' (elements (getM ?state'))"
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"
        let ?fState = "notifyWatches_loop literal Wl' newWl ?state''"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(3)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' \<noteq> ?w1`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          unfolding InvariantWatchesDiffer_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantConsistent (getM ?state'')"
          unfolding InvariantConsistent_def
          unfolding setWatch2_def
          by simp
        moreover
        from Cons(5)
        have "InvariantUniq (getM ?state'')"
          unfolding InvariantUniq_def
          unfolding setWatch2_def
          by simp
        moreover
        have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
        proof-
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww1 (elements M)"
              
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww1) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                        literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww1) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding setWatch2_def
                by simp
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using `getWatch1 ?state' clause = Some ?w1`
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding setWatch2_def
                by auto
              
              have "\<not> (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(8)
                using `l' \<noteq> ?w1` and `l' \<noteq> ?w2` `l' el (nth (getF ?state') clause)`
                using `\<not> literalFalse l' (elements (getM ?state'))`
                using a and b
                using `c = clause`
                unfolding setWatch2_def
                by auto
              moreover
              have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> 
                elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                using `0 \<le> clause \<and> clause < length (getF state)`
                using `getWatch1 ?state' clause = Some ?w1`[THEN sym]
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                using `literalFalse ww1 (elements M)`
                using `ww1 = ?w1`
                unfolding setWatch2_def
                by auto
              ultimately
              show ?thesis
                using `ww1 = ?w1`
                using `c = clause`
                unfolding setWatch2_def
                by auto
            qed
          }
          moreover 
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww2 (elements M)"
            
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww2) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww2) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(6)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using `getWatch1 ?state' clause = Some ?w1`
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding setWatch2_def
                by auto
              with `\<not> literalFalse l' (elements (getM ?state'))` b
                Cons(8)
              have False
                by simp
              thus ?thesis
                by simp
            qed
          }
          ultimately
          show ?thesis
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by blast
        qed
        moreover
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(10)
          using `clause \<notin> set Wl'`
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state"
          "getF ?state'' = getF state"
          unfolding setWatch2_def
          by auto
        moreover
        have "getWatch1 ?state'' clause = Some ?w1" "getWatch2 ?state'' clause = Some l'"
          using `getWatch1 ?state' clause = Some ?w1`
          unfolding setWatch2_def
          by auto
        hence "getWatch1 ?fState clause = getWatch1 ?state'' clause \<and> getWatch2 ?fState clause = Some l'"
          using `clause \<notin> set Wl'`
          using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
          using Cons(7)
          using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "newWl"]
          by (simp add: Let_def)
        moreover
        have "watchCharacterizationCondition ?w1 l' (getM ?fState) (getF ?fState ! clause) \<and>
          watchCharacterizationCondition l' ?w1 (getM ?fState) (getF ?fState ! clause)"
        proof-
          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "newWl"]
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            unfolding setWatch2_def
            by (auto simp add: Let_def)
          
          have "literalFalse ?w1 (elements M) \<longrightarrow> 
            (\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M)"
          proof
            assume "literalFalse ?w1 (elements M)"
            show "\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M"
            proof-
              have "\<not> (\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using `l' el (nth (getF ?state') clause)` `l' \<noteq> ?w1` `l' \<noteq> ?w2` `\<not> literalFalse l' (elements (getM ?state'))`
                using Cons(8)
                unfolding swapWatches_def
                by auto

              from `literalFalse ?w1 (elements M)` Cons(6)
              have
                "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                 (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M)"
                using `0 \<le> clause \<and> clause < length (getF state)`
                using `getWatch1 ?state' clause = Some ?w1`[THEN sym]
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                by simp
              with `\<not> (\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))`
              have "\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M"
                by auto
              thus ?thesis
                unfolding setWatch2_def
                by simp
            qed
          qed
          moreover
          have "watchCharacterizationCondition l' ?w1 (getM ?fState) (getF ?fState ! clause)"
            using `\<not> literalFalse l' (elements (getM ?state'))`
            using `getM ?fState = getM state` 
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "watchCharacterizationCondition ?w1 l' (getM ?fState) (getF ?fState ! clause)"
          proof (cases "literalFalse ?w1 (elements (getM ?fState))")
            case True
            hence "literalFalse ?w1 (elements M)"
              using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "newWl"]
              using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
              using Cons(7) Cons(8)
              using `?w1 \<noteq> ?w2` `?w2 = literal`
              unfolding setWatch2_def
              by (simp add: Let_def)
            with `literalFalse ?w1 (elements M) \<longrightarrow> 
              (\<exists> l. l el (nth (getF ?state'') clause) \<and> literalTrue l (elements M) \<and>  elementLevel l M \<le> elementLevel (opposite ?w1) M)`
            obtain l::Literal
              where "l el (nth (getF ?state'') clause)" and 
              "literalTrue l (elements M)" and 
              "elementLevel l M \<le> elementLevel (opposite ?w1) M"
              by auto
            hence "elementLevel l (getM state) \<le> elementLevel (opposite ?w1) (getM state)"
              using Cons(8)
              using `literalTrue l (elements M)` `literalFalse ?w1 (elements M)`
              using elementLevelAppend[of "l" "M" "[(opposite literal, decision)]"]
              using elementLevelAppend[of "opposite ?w1" "M" "[(opposite literal, decision)]"]
              by auto
            thus ?thesis
              using `l el (nth (getF ?state'') clause)` `literalTrue l (elements M)`
              using `getM ?fState = getM state` `getF ?fState = getF state` `getM ?state'' = getM state` `getF ?state'' = getF state`
              using Cons(8)
              unfolding watchCharacterizationCondition_def
              by auto
          next
            case False
            thus ?thesis
              unfolding watchCharacterizationCondition_def
              by simp
          qed
          ultimately
          show ?thesis
            by simp
        qed
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(7) Cons(8)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch2 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using `getWatch1 ?state'' clause = Some ?w1`
          using `getWatch2 ?state'' clause = Some l'`
          using Some
          using `uniq Wl'`
          using `?w1 \<noteq> ?w2`
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
            unfolding InvariantWatchesDiffer_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state')"
            unfolding InvariantConsistent_def
            by simp
          moreover
          from Cons(5)
          have "InvariantUniq (getM ?state')"
            unfolding InvariantUniq_def
            by simp
          moreover
          from Cons(6)
          have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') M"
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(10)
            using `clause \<notin> set Wl'`
            by simp
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            by auto
          moreover
          have "getWatch1 ?fState clause = getWatch1 ?state'' clause \<and> getWatch2 ?fState clause = getWatch2 ?state'' clause"
            using `clause \<notin> set Wl'`
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "clause # newWl" ]
            by (simp add: Let_def)
          moreover
          have "literalFalse ?w1 (elements M)"
            using `literalFalse ?w1 (elements (getM ?state'))`
              `?w1 \<noteq> ?w2` `?w2 = literal` Cons(8)
            by auto

          have "\<not> literalTrue ?w2 (elements M)"
            using Cons(4)
            using Cons(8)
            using `?w2 = literal`
            using inconsistentCharacterization[of "elements M @ [opposite literal]"]
            unfolding InvariantConsistent_def
            by force

          have *: "\<forall> l. l el (nth (getF state) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
            literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M"
          proof-
            have "\<not> (\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M))"
            proof
              assume "\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M)"
              show "False"
              proof-
                from `\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements M)`
                obtain l 
                  where "l el (nth (getF state) clause)" "literalTrue l (elements M)"
                  by auto
                hence "l \<noteq> ?w1" "l \<noteq> ?w2"
                  using `\<not> literalTrue ?w1 (elements (getM ?state'))`
                  using `\<not> literalTrue ?w2 (elements M)`
                  using Cons(8)
                  by auto
                with `l el (nth (getF state) clause)`
                have "literalFalse l (elements (getM ?state'))"
                  using `getWatch1 ?state' clause = Some ?w1`
                  using `getWatch2 ?state' clause = Some ?w2`
                  using None
                  using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
                  by simp
                with `l \<noteq> ?w2` `?w2 = literal` Cons(8)
                have "literalFalse l (elements M)"
                  by simp
                with Cons(4) `literalTrue l (elements M)`
                show ?thesis
                  unfolding InvariantConsistent_def
                  using Cons(8)
                  by (auto simp add: inconsistentCharacterization)
              qed
            qed
            with `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M`
            show ?thesis
              unfolding InvariantWatchCharacterization_def
              using `literalFalse ?w1 (elements M)`
              using `getWatch1 ?state' clause = Some ?w1`[THEN sym]
              using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
              using `0 \<le> clause \<and> clause < length (getF state)`
              unfolding watchCharacterizationCondition_def
              by (simp) (blast)
          qed
          
          have **: "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements (getM ?state'')) \<and> 
                      elementLevel (opposite l) (getM ?state'') \<le> elementLevel (opposite ?w1) (getM ?state'')"
          proof-
            {

              fix l::Literal
              assume "l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2"


              have "literalFalse l (elements (getM ?state'')) \<and> 
                    elementLevel (opposite l) (getM ?state'') \<le> elementLevel (opposite ?w1) (getM ?state'')"
              proof-
                from * `l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2`
                have "literalFalse l (elements M)" "elementLevel (opposite l) M \<le> elementLevel (opposite ?w1) M"
                  by auto
                thus ?thesis
                  using elementLevelAppend[of "opposite l" "M" "[(opposite literal, decision)]"]
                  using `literalFalse ?w1 (elements M)`
                  using elementLevelAppend[of "opposite ?w1" "M" "[(opposite literal, decision)]"]
                  using Cons(8)
                  by simp
              qed
            }
            thus ?thesis
              by simp
          qed

          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            by (auto simp add: Let_def)
          hence "\<forall> l. l el (nth (getF ?fState) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> 
                      literalFalse l (elements (getM ?fState)) \<and> 
                      elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w1) (getM ?fState)"
            using **
            using `getM ?state'' = getM state`
            using `getF ?state'' = getF state`
            by simp
          moreover
          have "\<forall> l. literalFalse l (elements (getM ?fState)) \<longrightarrow> 
                     elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w2) (getM ?fState)"
          proof-
            have "elementLevel (opposite ?w2) (getM ?fState) = currentLevel (getM ?fState)"
              using Cons(8)
              using `(getM ?fState) = (getM state)`
              using `\<not> literalFalse ?w2 (elements M)`
              using `?w2 = literal`
              using elementOnCurrentLevel[of "opposite ?w2" "M" "decision"]
              by simp
            thus ?thesis
              by (simp add: elementLevelLeqCurrentLevel)
          qed
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(7) Cons(8)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch2 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            using `?w1 \<noteq> ?w2`
            unfolding watchCharacterizationCondition_def
            by (simp add: Let_def)
        next
          case False

          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          let ?fState = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(3)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding InvariantConsistent_def
            unfolding setReason_def
            by simp
          moreover
          from Cons(5)
          have "InvariantUniq (getM ?state'')"
            unfolding InvariantUniq_def
            unfolding setReason_def
            by simp
          moreover
          from Cons(6)
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            unfolding setReason_def
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(10)
            using `clause \<notin> set Wl'`
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            unfolding setReason_def
            by auto
          moreover
          have "getWatch1 ?state'' clause = Some ?w1" "getWatch2 ?state'' clause = Some ?w2"
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            unfolding setReason_def
            by auto
          moreover
          have "getWatch1 ?fState clause = Some ?w1" "getWatch2 ?fState clause = Some ?w2"
            using `getWatch1 ?state'' clause = Some ?w1` `getWatch2 ?state'' clause = Some ?w2`
            using `clause \<notin> set Wl'`
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            using notifyWatchesLoopPreservedWatches[of "?state''" "Wl'" "literal" "clause # newWl" ]
            by (auto simp add: Let_def)
          moreover
          have "(getM ?fState) = (getM state)" "(getF ?fState) = (getF state)"
            using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
            using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')` `getF ?state'' = getF state`
            using Cons(7)
            unfolding setReason_def
            by (auto simp add: Let_def)
          ultimately 
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> (\<forall>w1 w2. Some w1 = getWatch1 ?fState c \<and> Some w2 = getWatch2 ?fState c \<longrightarrow>
               watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! c) \<and>
               watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! c))" and
               "?fState = notifyWatches_loop literal (clause # Wl') newWl state"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(7) Cons(8)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch2 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (auto simp add: Let_def)
          moreover
          have *: "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state''))"
            using None
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
            using Cons(8)
            unfolding setReason_def
            by auto

          have**: "\<forall> l. l el (nth (getF ?fState) clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?fState))"
            using `(getM ?fState) = (getM state)` `(getF ?fState) = (getF state)`
            using *
            using `getM ?state'' = getM state`
            using `getF ?state'' = getF state`
            by auto

          have ***: "\<forall> l. literalFalse l (elements (getM ?fState)) \<longrightarrow> 
                     elementLevel (opposite l) (getM ?fState) \<le> elementLevel (opposite ?w2) (getM ?fState)"
          proof-
            have "elementLevel (opposite ?w2) (getM ?fState) = currentLevel (getM ?fState)"
              using Cons(8)
              using `(getM ?fState) = (getM state)`
              using `\<not> literalFalse ?w2 (elements M)`
              using `?w2 = literal`
              using elementOnCurrentLevel[of "opposite ?w2" "M" "decision"]
              by simp
            thus ?thesis
              by (simp add: elementLevelLeqCurrentLevel)
          qed

          have "(\<forall>w1 w2. Some w1 = getWatch1 ?fState clause \<and> Some w2 = getWatch2 ?fState clause \<longrightarrow>
            watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! clause) \<and>
            watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! clause))"
          proof-
            {
              fix w1 w2
              assume "Some w1 = getWatch1 ?fState clause \<and> Some w2 = getWatch2 ?fState clause"
              hence "w1 = ?w1" "w2 = ?w2"
                using `getWatch1 ?fState clause = Some ?w1`
                using `getWatch2 ?fState clause = Some ?w2`
                by auto
              hence "watchCharacterizationCondition w1 w2 (getM ?fState) (getF ?fState ! clause) \<and>
                watchCharacterizationCondition w2 w1 (getM ?fState) (getF ?fState ! clause)"
                unfolding watchCharacterizationCondition_def
                using ** ***
                unfolding watchCharacterizationCondition_def
                using `(getM ?fState) = (getM state)` `(getF ?fState) = (getF state)`
                using `\<not> literalFalse ?w1 (elements (getM ?state'))`
                by simp
            }
            thus ?thesis
              by auto
          qed
          ultimately
          show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed
  

lemma NotifyWatchesLoopConflictFlagEffect:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "InvariantConsistent (getM state)"
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)"
  "literalFalse literal (elements (getM state))"
  "uniq Wl"
shows
  "let state' = notifyWatches_loop literal Wl newWl state in
     getConflictFlag state' = 
        (getConflictFlag state \<or> 
         (\<exists> clause. clause \<in> set Wl \<and> clauseFalse (nth (getF state) clause) (elements (getM state))))"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  
  from `uniq (clause # Wl')`
  have "uniq Wl'" and "clause \<notin> set Wl'"
    by (auto simp add: uniqAppendIff)

  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause" "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto

    from `Some literal = getWatch1 state clause`
      `getWatch2 ?state' clause = Some ?w2`
    `literalFalse literal (elements (getM state))`
    have "literalFalse ?w2 (elements (getM state))"
      unfolding swapWatches_def
      by simp

    from `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 el (nth (getF state) clause)"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `clause < length (getF state)`
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getF ?state' = getF state \<and> 
        getM ?state' = getM state \<and> 
        getConflictFlag ?state' = getConflictFlag state
        "
        unfolding swapWatches_def
        by simp
      moreover
      have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c"
        using Cons(5)
        unfolding swapWatches_def
        by auto
      moreover
      have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
        using `?w1 el (nth (getF state) clause)`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `InvariantConsistent (getM state)`
        unfolding InvariantConsistent_def
        unfolding swapWatches_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(3) Cons(4) Cons(6)
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `Some literal = getWatch1 state clause`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq Wl'`
        by (auto simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "\<not> literalFalse l' (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantConsistent (getM ?state'')"
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getConflictFlag ?state'' = getConflictFlag state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(5)
          using `clause \<notin> set Wl'`
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
          using `l' el (nth (getF ?state') clause)` 
          using `\<not> literalFalse l' (elements (getM ?state'))`
          using `InvariantConsistent (getM state)`
          unfolding InvariantConsistent_def
          unfolding swapWatches_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3) Cons(4) Cons(6)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using `uniq Wl'`
          using Some
          by (auto simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding setWatch2_def
            unfolding swapWatches_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state"
            unfolding swapWatches_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(5)
            using `clause \<notin> set Wl'`
            unfolding swapWatches_def
            unfolding setWatch2_def
            by auto
          moreover
          have "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using `\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))`
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `literalFalse ?w2 (elements (getM state))`
            unfolding swapWatches_def
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4) Cons(6)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (auto simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(5)
            using `clause \<notin> set Wl'`
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
            using `?w1 el (nth (getF state) clause)`
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `InvariantConsistent (getM state)`
            unfolding InvariantConsistent_def
          unfolding swapWatches_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)      
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4) Cons(6)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            apply (simp add: Let_def)
            unfolding setReason_def
            unfolding swapWatches_def
            by auto
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto

    from `\<not> Some literal = getWatch1 state clause`
      `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)`
    have "Some literal = getWatch2 state clause"
      by auto
    hence "literalFalse ?w2 (elements (getM state))"
      using 
      `getWatch2 ?state' clause = Some ?w2`
      `literalFalse literal (elements (getM state))`
      by simp

    from `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 el (nth (getF state) clause)"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `clause < length (getF state)`
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto
    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True

      have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
        using `?w1 el (nth (getF state) clause)`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `InvariantConsistent (getM state)`
        unfolding InvariantConsistent_def
        unfolding swapWatches_def
        by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)

      thus ?thesis
        using True
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6)
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq Wl'`
        by (auto simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "\<not> literalFalse l' (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantConsistent (getM ?state'')"
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getConflictFlag ?state'' = getConflictFlag state"
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(5)
          using `clause \<notin> set Wl'`
          unfolding setWatch2_def
          by auto
        moreover
        have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
          using `l' el (nth (getF ?state') clause)` 
          using `\<not> literalFalse l' (elements (getM ?state'))`
          using `InvariantConsistent (getM state)`
          unfolding InvariantConsistent_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3) Cons(4) Cons(6)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using `uniq Wl'`
          using Some
          by (auto simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding setWatch2_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state"
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(5)
            using `clause \<notin> set Wl'`
            unfolding setWatch2_def
            by auto
          moreover
          have "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using `\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))`
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `literalFalse ?w2 (elements (getM state))`
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4) Cons(6)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (auto simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantConsistent (getM ?state'')"
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state"
            unfolding setReason_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(5)
            using `clause \<notin> set Wl'`
            unfolding setReason_def
            by auto
          moreover
          have "\<not> clauseFalse (nth (getF state) clause) (elements (getM state))"
            using `?w1 el (nth (getF state) clause)`
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `InvariantConsistent (getM state)`
            unfolding InvariantConsistent_def
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)      
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4) Cons(6)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            apply (simp add: Let_def)
            unfolding setReason_def
            by auto
        qed
      qed
    qed
  qed
qed


lemma NotifyWatchesLoopQEffect:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State
assumes 
  "(getM state) = M @ [(opposite literal, decision)]" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "InvariantConsistent (getM state)" and
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)" and
  "uniq Wl" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M"
shows
  "let state' = notifyWatches_loop literal Wl newWl state in
      ((\<forall> l. l \<in> (set (getQ state') - set (getQ state)) \<longrightarrow> 
            (\<exists> clause. (clause el (getF state) \<and>
                        literal el clause \<and>
                        (isUnitClause clause l (elements (getM state)))))) \<and>
      (\<forall> clause. clause \<in> set Wl \<longrightarrow> 
          (\<forall> l. (isUnitClause (nth (getF state) clause) l (elements (getM state))) \<longrightarrow> 
                     l \<in> (set (getQ state')))))" 
  (is "let state' = notifyWatches_loop literal Wl newWl state in (?Cond1 state' state \<and> ?Cond2 Wl state' state)")
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  
  from `uniq (clause # Wl')`
  have "uniq Wl'" and "clause \<notin> set Wl'"
    by (auto simp add: uniqAppendIff)

  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause" "clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto

  from `0 \<le> clause` `clause < length (getF state)`
  have "(nth (getF state) clause) el (getF state)"
    by simp

  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto

    have "?w2 = literal"
      using `Some literal = getWatch1 state clause`
      using `getWatch2 ?state' clause = Some ?w2`
      unfolding swapWatches_def
      by simp
      
    hence "literalFalse ?w2 (elements (getM state))"
      using `(getM state) = M @ [(opposite literal, decision)]`
      by simp

    from `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `clause < length (getF state)`
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    from `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 \<noteq> ?w2"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `clause < length (getF state)`
      unfolding InvariantWatchesDiffer_def
      unfolding swapWatches_def
      by auto

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(3)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      from Cons(4)
      have "InvariantWatchesDiffer (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesDiffer_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getF ?state' = getF state \<and> 
        getM ?state' = getM state \<and> 
        getQ ?state' = getQ state \<and> 
        getConflictFlag ?state' = getConflictFlag state
        "
        unfolding swapWatches_def
        by simp
      moreover
      have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c"
        using Cons(7)
        unfolding swapWatches_def
        by auto
      moreover
      have "InvariantWatchCharacterization (getF ?state') (getWatch1 ?state') (getWatch2 ?state') M"
        using Cons(9)
        unfolding swapWatches_def
        unfolding InvariantWatchCharacterization_def
        by auto
      moreover
      have "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
        using `?w1 el (nth (getF state) clause)`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `InvariantConsistent (getM state)`
        unfolding InvariantConsistent_def
        unfolding swapWatches_def
          by (auto simp add: isUnitClause_def inconsistentCharacterization)
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(5) Cons(6)
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `Some literal = getWatch1 state clause`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq Wl'`
        by ( simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "\<not> literalFalse l' (elements (getM ?state'))" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' \<noteq> ?w1`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          unfolding InvariantWatchesDiffer_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(6)
        have "InvariantConsistent (getM ?state'')"
          unfolding setWatch2_def
          unfolding swapWatches_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getConflictFlag ?state'' = getConflictFlag state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(7)
          using `clause \<notin> set Wl'`
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
        proof-
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww1 (elements M)"
              
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww1) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww1) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                unfolding setWatch2_def
                by simp
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using `getWatch1 ?state' clause = Some ?w1`
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              
              have "\<not> (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(2)
                using `l' \<noteq> ?w1` and `l' \<noteq> ?w2` `l' el (nth (getF ?state') clause)`
                using `\<not> literalFalse l' (elements (getM ?state'))`
                using a and b
                using `c = clause`
                unfolding swapWatches_def
                unfolding setWatch2_def
                by auto
              moreover
              have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> 
                elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                using `clause < length (getF state)`
                using `getWatch1 ?state' clause = Some ?w1`[THEN sym]
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                using `literalFalse ww1 (elements M)`
                using `ww1 = ?w1`
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              ultimately
              show ?thesis
                using `ww1 = ?w1`
                using `c = clause`
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
            qed
          }
          moreover 
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww2 (elements M)"
            
            have "(\<exists>l. l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww2) M) \<or>
                  (\<forall>l. l el ((getF ?state'') ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                       literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww2) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding swapWatches_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using `getWatch1 ?state' clause = Some ?w1`
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding setWatch2_def
                unfolding swapWatches_def
                by auto
              with `\<not> literalFalse l' (elements (getM ?state'))` b
                Cons(2)
              have False
                unfolding swapWatches_def
                by simp
              thus ?thesis
                by simp
            qed
          }
          ultimately
          show ?thesis
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by blast
        qed
        moreover
        have "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
          (* Depends on the watch characterization invariant *)
        proof-
          {
            assume "\<not> ?thesis"
            then obtain l
              where "isUnitClause (nth (getF state) clause) l (elements (getM state))"
              by auto
            with `l' el (nth (getF ?state') clause)` `\<not> literalFalse l' (elements (getM ?state'))`
            have "l = l'"
              unfolding isUnitClause_def
              unfolding swapWatches_def
              by auto
            with `l' \<noteq> ?w1` have
              "literalFalse ?w1 (elements (getM ?state'))"
              using `isUnitClause (nth (getF state) clause) l (elements (getM state))`
              using `?w1 el (nth (getF state) clause)`
              unfolding isUnitClause_def
              unfolding swapWatches_def
              by simp
            with `?w1 \<noteq> ?w2` `?w2 = literal`
            Cons(2)
            have "literalFalse ?w1 (elements M)"
              unfolding swapWatches_def
              by simp

            from `isUnitClause (nth (getF state) clause) l (elements (getM state))`
              Cons(6)
            have "\<not> (\<exists> l. (l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))))"
              using containsTrueNotUnit[of _ "(nth (getF state) clause)" "elements (getM state)"]
              unfolding InvariantConsistent_def
              by auto

            from `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M`
            `clause < length (getF state)`
              `literalFalse ?w1 (elements M)` 
              `getWatch1 ?state' clause = Some ?w1` [THEN sym]
              `getWatch2 ?state' clause = Some ?w2` [THEN sym]
            have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                  (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
              unfolding InvariantWatchCharacterization_def
              unfolding watchCharacterizationCondition_def
              unfolding swapWatches_def
              by auto
            with `\<not> (\<exists> l. (l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))))`
            Cons(2)
            have "(\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
              by auto
            with `l' el (getF ?state' ! clause)` `l' \<noteq> ?w1` `l' \<noteq> ?w2` `\<not> literalFalse l' (elements (getM ?state'))`
            Cons(2)
            have False
              unfolding swapWatches_def
              by simp
          }
          thus ?thesis
            by auto
        qed
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(2) Cons(5) Cons(6)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using `uniq Wl'`
          using Some
          by (simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            by auto
          moreover
          from Cons(6)
          have "InvariantConsistent (getM ?state'')"
            unfolding swapWatches_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getSATFlag ?state'' = getSATFlag state"
            unfolding swapWatches_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(7)
            using `clause \<notin> set Wl'`
            unfolding swapWatches_def
            by auto
          moreover
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            using Cons(9)
            unfolding swapWatches_def
            unfolding InvariantWatchCharacterization_def
            by auto
          moreover
          have "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using `\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))`
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `literalFalse ?w2 (elements (getM state))`
            unfolding swapWatches_def
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          hence "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
            unfolding isUnitClause_def
            by (simp add: clauseFalseIffAllLiteralsAreFalse)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(5) Cons(6)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(6)
          have "InvariantConsistent (getM ?state'')"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state \<and> 
            getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state @ [?w1]))"
            unfolding swapWatches_def
            unfolding setReason_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(7)
            using `clause \<notin> set Wl'`
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            using Cons(9)
            unfolding swapWatches_def
            unfolding setReason_def
            unfolding InvariantWatchCharacterization_def
            by auto
          ultimately
          have "let state' = notifyWatches_loop literal Wl' (clause # newWl) ?state'' in 
                   ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(5)
            using `uniq Wl'`
            by (simp add: Let_def)
          moreover
          have "notifyWatches_loop literal Wl' (clause # newWl) ?state'' = notifyWatches_loop literal (clause # Wl') newWl state"
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
          ultimately 
          have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                   ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''"
            by simp

          have "isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))"
            using `\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))`
            using `?w1 el (nth (getF state) clause)`
            using `?w2 el (nth (getF state) clause)`
            using `literalFalse ?w2 (elements (getM state))`
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            unfolding swapWatches_def
            unfolding isUnitClause_def
            by auto

          show ?thesis
          proof-
            {
              fix l::Literal
              assume "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                l \<in> set (getQ state') - set (getQ state)"
              have "\<exists>clause. clause el (getF state) \<and> literal el clause \<and> isUnitClause clause l (elements (getM state))"
              proof (cases "l \<noteq> ?w1")
                case True
                hence "let state' = notifyWatches_loop literal (clause # Wl') newWl state in 
                   l \<in> set (getQ state') - set (getQ ?state'')"
                  using `let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                    l \<in> set (getQ state') - set (getQ state)`
                  unfolding setReason_def
                  unfolding swapWatches_def
                  by (simp add:Let_def)
                with `let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                  ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''`
                show ?thesis
                  unfolding setReason_def
                  unfolding swapWatches_def
                  by (simp add:Let_def del: notifyWatches_loop.simps)
              next
                case False
                thus ?thesis
                  using `(nth (getF state) clause) el (getF state)`
                        `?w2 = literal`
                        `?w2 el (nth (getF state) clause)`
                        `isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))`
                  by (auto simp add:Let_def)
              qed
            } 
            hence "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                ?Cond1 state' state"
              by simp
            moreover
            {
              fix c
              assume "c \<in> set (clause # Wl')"
              have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in 
                \<forall> l. isUnitClause (nth (getF state) c) l (elements (getM state)) \<longrightarrow> l \<in> set (getQ state')"
              proof (cases "c = clause")
                case True
                {
                  fix l::Literal
                  assume "isUnitClause (nth (getF state) c) l (elements (getM state))"
                  with `isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))` `c = clause`
                  have "l = ?w1"
                    unfolding isUnitClause_def
                    by auto
                  have "isPrefix (getQ ?state'') (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')`
                    using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
                    using Cons(5)
                    unfolding swapWatches_def
                    unfolding setReason_def
                    by (simp add: Let_def)
                  hence "set (getQ ?state'') \<subseteq> set (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using prefixIsSubset[of "getQ ?state''" "getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state'')"]
                    by auto
                  hence "l \<in> set (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using `l = ?w1`
                    unfolding swapWatches_def
                    unfolding setReason_def
                  by auto
              } 
              thus ?thesis
                using `notifyWatches_loop literal Wl' (clause # newWl) ?state'' = notifyWatches_loop literal (clause # Wl') newWl state`
                by (simp add:Let_def)
            next
                case False
                hence "c \<in> set Wl'"
                  using `c \<in> set (clause # Wl')`
                  by simp
                {
                  fix l::Literal
                  assume "isUnitClause (nth (getF state) c) l (elements (getM state))"
                  hence "isUnitClause (nth (getF ?state'') c) l (elements (getM ?state''))"
                    unfolding setReason_def
                    unfolding swapWatches_def
                    by simp
                  with `let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                    ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''`
                    `c \<in> set Wl'`
                  have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in l \<in> set (getQ state')"
                    by (simp add:Let_def)
                }
                thus ?thesis
                  by (simp add:Let_def)
              qed
            }
            hence "?Cond2 (clause # Wl') (notifyWatches_loop literal (clause # Wl') newWl state) state"
              by (simp add: Let_def)
            ultimately
            show ?thesis
              by (simp add:Let_def)
          qed
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto


    from `\<not> Some literal = getWatch1 state clause`
      `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)`
    have "Some literal = getWatch2 state clause"
      by auto
    hence "?w2 = literal"
      using `getWatch2 ?state' clause = Some ?w2`
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(2)
      by simp

    from `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `clause < length (getF state)`
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    from `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 \<noteq> ?w2"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `clause < length (getF state)`
      unfolding InvariantWatchesDiffer_def
      unfolding swapWatches_def
      by auto
    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      have "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
        using `?w1 el (nth (getF state) clause)`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `InvariantConsistent (getM state)`
        unfolding InvariantConsistent_def
        by (auto simp add: isUnitClause_def inconsistentCharacterization)
      thus ?thesis
        using True
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7) Cons(8) Cons(9)
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq Wl'`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)" "\<not> literalFalse l' (elements (getM ?state'))" "l' \<noteq> ?w1" "l' \<noteq> ?w2"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by auto

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(4)
        have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' \<noteq> ?w1`
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          unfolding InvariantWatchesDiffer_def
          unfolding setWatch2_def
          by auto
        moreover
        from Cons(6)
        have "InvariantConsistent (getM ?state'')"
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getConflictFlag ?state'' = getConflictFlag state"
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(7)
          using `clause \<notin> set Wl'`
          unfolding setWatch2_def
          by auto
        moreover
        have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
        proof-
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww1 (elements M)"
              
            have "(\<exists>l.  l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww1) M) \<or>
              (\<forall>l. l el (getF ?state'' ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                   literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww1) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using `getWatch1 ?state' clause = Some ?w1`
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding setWatch2_def
                by auto
              
              have "\<not> (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using `l' \<noteq> ?w1` and `l' \<noteq> ?w2` `l' el (nth (getF ?state') clause)`
                using `\<not> literalFalse l' (elements (getM ?state'))`
                using Cons(2)
                using a and b
                using `c = clause`
                unfolding setWatch2_def
                by auto
              moreover
              have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                    (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                using `clause < length (getF state)`
                using `getWatch1 ?state' clause = Some ?w1`[THEN sym]
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                using `literalFalse ww1 (elements M)`
                using `ww1 = ?w1`
                unfolding setWatch2_def
                by auto
              ultimately
              show ?thesis
                using `ww1 = ?w1`
                using `c = clause`
                unfolding setWatch2_def
                by auto
            qed
          }
          moreover 
          {
            fix c::nat and ww1::Literal and ww2::Literal
            assume a: "0 \<le> c \<and> c < length (getF ?state'') \<and> Some ww1 = (getWatch1 ?state'' c) \<and> Some ww2 = (getWatch2 ?state'' c)"
            assume b: "literalFalse ww2 (elements M)"
            
            have "(\<exists>l.  l el ((getF ?state'') ! c) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ww2) M) \<or>
              (\<forall>l. l el (getF ?state'' ! c) \<and> l \<noteq> ww1 \<and> l \<noteq> ww2 \<longrightarrow> 
                   literalFalse l (elements M) \<and> elementLevel (opposite l) M \<le> elementLevel (opposite ww2) M)"
            proof (cases "c = clause")
              case False
              thus ?thesis
                using a and b
                using Cons(9)
                unfolding InvariantWatchCharacterization_def
                unfolding watchCharacterizationCondition_def
                unfolding setWatch2_def
                by auto
            next
              case True
              with a 
              have "ww1 = ?w1" and "ww2 = l'"
                using `getWatch1 ?state' clause = Some ?w1`
                using `getWatch2 ?state' clause = Some ?w2`[THEN sym]
                unfolding setWatch2_def
                by auto
              with `\<not> literalFalse l' (elements (getM ?state'))` b
              Cons(2)
              have False
                unfolding setWatch2_def
                by simp
              thus ?thesis
                by simp
            qed
          }
          ultimately
          show ?thesis
            unfolding InvariantWatchCharacterization_def
            unfolding watchCharacterizationCondition_def
            by blast
        qed
        moreover
        have "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
          (* Depends on the watch characterization invariant *)
        proof-
          {
            assume "\<not> ?thesis"
            then obtain l
              where "isUnitClause (nth (getF state) clause) l (elements (getM state))"
              by auto
            with `l' el (nth (getF ?state') clause)` `\<not> literalFalse l' (elements (getM ?state'))`
            have "l = l'"
              unfolding isUnitClause_def
              by auto
            with `l' \<noteq> ?w1` have
              "literalFalse ?w1 (elements (getM ?state'))"
              using `isUnitClause (nth (getF state) clause) l (elements (getM state))`
              using `?w1 el (nth (getF state) clause)`
              unfolding isUnitClause_def
              by simp
            with `?w1 \<noteq> ?w2` `?w2 = literal`
            Cons(2)
            have "literalFalse ?w1 (elements M)"
              by simp

            from `isUnitClause (nth (getF state) clause) l (elements (getM state))`
              Cons(6)
            have "\<not> (\<exists> l. (l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))))"
              using containsTrueNotUnit[of _ "(nth (getF state) clause)" "elements (getM state)"]
              unfolding InvariantConsistent_def
              by auto

            from `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) M`
            `clause < length (getF state)`
              `literalFalse ?w1 (elements M)` 
              `getWatch1 ?state' clause = Some ?w1` [THEN sym]
              `getWatch2 ?state' clause = Some ?w2` [THEN sym]
            have "(\<exists>l. l el (getF state ! clause) \<and> literalTrue l (elements M) \<and> elementLevel l M \<le> elementLevel (opposite ?w1) M) \<or>
                  (\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
              unfolding InvariantWatchCharacterization_def
              unfolding watchCharacterizationCondition_def
              unfolding swapWatches_def
              by auto
            with `\<not> (\<exists> l. (l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))))`
            Cons(2)
            have "(\<forall>l. l el (getF state ! clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements M))"
              by auto
            with `l' el (getF ?state' ! clause)` `l' \<noteq> ?w1` `l' \<noteq> ?w2` `\<not> literalFalse l' (elements (getM ?state'))`
            Cons(2)
            have False
              unfolding swapWatches_def
              by simp
          }
          thus ?thesis
            by auto
        qed
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(2) Cons(5) Cons(7)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using `uniq Wl'`
          using Some
          by (simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            by auto
          moreover
          from Cons(6)
          have "InvariantConsistent (getM ?state'')"
            unfolding setWatch2_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getSATFlag ?state'' = getSATFlag state"
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(7)
            using `clause \<notin> set Wl'`
            unfolding setWatch2_def
            by auto
          moreover
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            using Cons(9)
            unfolding InvariantWatchCharacterization_def
            by auto
          moreover
          have "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using `\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))`
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `literalFalse ?w2 (elements (getM state))`
            unfolding swapWatches_def
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          hence "\<not> (\<exists> l. isUnitClause (nth (getF state) clause) l (elements (getM state)))"
            unfolding isUnitClause_def
            by (simp add: clauseFalseIffAllLiteralsAreFalse)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(5) Cons(7)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"

          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(4)
          have "InvariantWatchesDiffer (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesDiffer_def
            unfolding setReason_def
            by auto
          moreover
          from Cons(6)
          have "InvariantConsistent (getM ?state'')"
            unfolding setReason_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getSATFlag ?state'' = getSATFlag state"
            unfolding setReason_def
            by simp
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(7)
            using `clause \<notin> set Wl'`
            unfolding setReason_def
            by auto
          moreover
          have "InvariantWatchCharacterization (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'') M"
            using Cons(9)
            unfolding InvariantWatchCharacterization_def
            unfolding setReason_def
            by auto
          ultimately
          have "let state' = notifyWatches_loop literal Wl' (clause # newWl) ?state'' in 
                   ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''"
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(5) Cons(6) Cons(7)
            using `uniq Wl'`
            by (simp add: Let_def)
          moreover
          have "notifyWatches_loop literal Wl' (clause # newWl) ?state'' = notifyWatches_loop literal (clause # Wl') newWl state"
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
          ultimately 
          have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                   ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''"
            by simp

          have "isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))"
            using `\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))`
            using `?w1 el (nth (getF state) clause)`
            using `?w2 el (nth (getF state) clause)`
            using `literalFalse ?w2 (elements (getM state))`
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            unfolding swapWatches_def
            unfolding isUnitClause_def
            by auto

          show ?thesis
          proof-
            {
              fix l::Literal
              assume "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                l \<in> set (getQ state') - set (getQ state)"
              have "\<exists>clause. clause el (getF state) \<and> literal el clause \<and> isUnitClause clause l (elements (getM state))"
              proof (cases "l \<noteq> ?w1")
                case True
                hence "let state' = notifyWatches_loop literal (clause # Wl') newWl state in 
                   l \<in> set (getQ state') - set (getQ ?state'')"
                  using `let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                    l \<in> set (getQ state') - set (getQ state)`
                  unfolding setReason_def
                  unfolding swapWatches_def
                  by (simp add:Let_def)
                with `let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                  ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''`
                show ?thesis
                  unfolding setReason_def
                  unfolding swapWatches_def
                  by (simp add:Let_def del: notifyWatches_loop.simps)
              next
                case False
                thus ?thesis
                  using `(nth (getF state) clause) el (getF state)` `isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))`
                        `?w2 = literal`
                        `?w2 el (nth (getF state) clause)`
                  by (auto simp add:Let_def)
              qed
            } 
            hence "let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                ?Cond1 state' state"
              by simp
            moreover
            {
              fix c
              assume "c \<in> set (clause # Wl')"
              have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in 
                \<forall> l. isUnitClause (nth (getF state) c) l (elements (getM state)) \<longrightarrow> l \<in> set (getQ state')"
              proof (cases "c = clause")
                case True
                {
                  fix l::Literal
                  assume "isUnitClause (nth (getF state) c) l (elements (getM state))"
                  with `isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))` `c = clause`
                  have "l = ?w1"
                    unfolding isUnitClause_def
                    by auto
                  have "isPrefix (getQ ?state'') (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using `InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')`
                    using notifyWatchesLoopPreservedVariables[of "?state''" "Wl'" "literal" "clause # newWl"]
                    using Cons(5)
                    unfolding swapWatches_def
                    unfolding setReason_def
                    by (simp add: Let_def)
                  hence "set (getQ ?state'') \<subseteq> set (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using prefixIsSubset[of "getQ ?state''" "getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state'')"]
                    by auto
                  hence "l \<in> set (getQ (notifyWatches_loop literal Wl' (clause # newWl) ?state''))"
                    using `l = ?w1`
                    unfolding swapWatches_def
                    unfolding setReason_def
                  by auto
              } 
              thus ?thesis
                using `notifyWatches_loop literal Wl' (clause # newWl) ?state'' = notifyWatches_loop literal (clause # Wl') newWl state`
                by (simp add:Let_def)
            next
                case False
                hence "c \<in> set Wl'"
                  using `c \<in> set (clause # Wl')`
                  by simp
                {
                  fix l::Literal
                  assume "isUnitClause (nth (getF state) c) l (elements (getM state))"
                  hence "isUnitClause (nth (getF ?state'') c) l (elements (getM ?state''))"
                    unfolding setReason_def
                    unfolding swapWatches_def
                    by simp
                  with `let state' = notifyWatches_loop literal (clause # Wl') newWl state in
                    ?Cond1 state' ?state'' \<and> ?Cond2 Wl' state' ?state''`
                    `c \<in> set Wl'`
                  have "let state' = notifyWatches_loop literal (clause # Wl') newWl state in l \<in> set (getQ state')"
                    by (simp add:Let_def)
                }
                thus ?thesis
                  by (simp add:Let_def)
              qed
            }
            hence "?Cond2 (clause # Wl') (notifyWatches_loop literal (clause # Wl') newWl state) state"
              by (simp add: Let_def)
            ultimately
            show ?thesis
              by (simp add:Let_def)
          qed
        qed
      qed
    qed
  qed
qed

lemma InvariantUniqQAfterNotifyWatchesLoop:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "InvariantUniqQ (getQ state)"
shows
  "let state' = notifyWatches_loop literal Wl newWl state in
       InvariantUniqQ (getQ state')
  " 
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')
  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state \<and> 
        getQ ?state' = getQ state
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(3) Cons(4)
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `Some literal = getWatch1 state clause`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(3) Cons(4)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3) Cons(4)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "uniq (getQ ?state'')"
            using Cons(4)
            using `getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])`
            unfolding InvariantUniqQ_def
            by (simp add: uniqAppendIff)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            unfolding isPrefix_def
            unfolding InvariantUniqQ_def
            by (simp add: Let_def split: split_if_asm)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      by auto    
    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state')) clause`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''"]
          using Cons(3) Cons(4)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state"
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3) Cons(4)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            unfolding setReason_def
            by auto
          moreover
          have "uniq (getQ ?state'')"
            using Cons(4)
            using `getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])`
            unfolding InvariantUniqQ_def
            by (simp add: uniqAppendIff)
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            unfolding isPrefix_def
            unfolding InvariantUniqQ_def
            by (simp add: Let_def split: split_if_asm)
        qed
      qed
    qed
  qed
qed

lemma InvariantConflictClauseCharacterizationAfterNotifyWatches:
assumes 
  "(getM state) = M @ [(opposite literal, decision)]" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)" and
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
  "uniq Wl"
shows 
  "let state' = (notifyWatches_loop literal Wl newWl state) in
   InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state')"
using assms
proof (induct Wl arbitrary: newWl state)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')

  from `uniq (clause # Wl')`
  have "clause \<notin> set Wl'" "uniq Wl'"
    by (auto simp add:uniqAppendIff)

  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto

    with True have
      "?w2 = literal"
      unfolding swapWatches_def
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(2)
      by simp

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(3)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto
      moreover
      have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c"
        using Cons(5)
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state \<and> 
        getConflictFlag ?state' = getConflictFlag state \<and> 
        getConflictClause ?state' = getConflictClause state
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(4) Cons(6) Cons(7)
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `Some literal = getWatch1 state clause`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq Wl'`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(5)
          using `clause \<notin> set Wl'`
          using swapWatchesEffect[of "clause" "state"]
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getConflictFlag ?state'' = getConflictFlag state \<and> 
          getConflictClause ?state'' = getConflictClause state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(2) Cons(4) Cons(6) Cons(7)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          using `uniq Wl'`
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getConflictFlag ?state'' \<and> 
            getConflictClause ?state'' = clause"
            unfolding swapWatches_def
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(5)
            using `clause \<notin> set Wl'`
            using swapWatchesEffect[of "clause" "state"]
            by simp
          moreover
          have "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state''))"
            using None
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
            unfolding setReason_def
            unfolding swapWatches_def
            by auto

          hence "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `literalFalse ?w2 (elements (getM state))`
            unfolding swapWatches_def
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          moreover
          have "(nth (getF state) clause) el (getF state)"
            using `0 \<le> clause \<and> clause < length (getF state)`
            using nth_mem[of "clause" "getF state"]
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(4) Cons(6) Cons(7)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            using `0 \<le> clause \<and> clause < length (getF state)`
            unfolding InvariantConflictClauseCharacterization_def
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getConflictFlag ?state'' = getConflictFlag state"
            "getConflictClause ?state'' = getConflictClause state"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(5)
            using `clause \<notin> set Wl'`
            using swapWatchesEffect[of "clause" "state"]
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "clause # newWl"]
            using Cons(2) Cons(4) Cons(6) Cons(7)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (simp add: Let_def)
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      by auto

    from `\<not> Some literal = getWatch1 state clause`
      `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)`
    have "Some literal = getWatch2 state clause"
      by auto
    hence "?w2 = literal"
      using `getWatch2 ?state' clause = Some ?w2`
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(2)
      by simp

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons(1)[of "?state'" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7)
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq Wl'`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(3)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state')) clause`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getConflictFlag ?state'' = getConflictFlag state \<and> 
          getConflictClause ?state'' = getConflictClause state"
          unfolding setWatch2_def
          by simp
        moreover
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(5)
          using `clause \<notin> set Wl'`
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "newWl"]
          using Cons(2) Cons(4) Cons(6) Cons(7)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          using `uniq Wl'`
          by (simp add: Let_def)
      next
        case None
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state \<and> 
            getConflictFlag ?state'' \<and> 
            getConflictClause ?state'' = clause"
            by simp
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(5)
            using `clause \<notin> set Wl'`
            by simp
          moreover
          have "\<forall> l. l el (nth (getF ?state'') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state''))"
            using None
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using getNonWatchedUnfalsifiedLiteralNoneCharacterization[of "nth (getF ?state') clause" "?w1" "?w2" "getM ?state'"]
            unfolding setReason_def
            by auto
          hence "clauseFalse (nth (getF state) clause) (elements (getM state))"
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `literalFalse ?w2 (elements (getM state))`
            by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          moreover
          have "(nth (getF state) clause) el (getF state)"
            using `0 \<le> clause \<and> clause < length (getF state)`
            using nth_mem[of "clause" "getF state"]
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(2) Cons(4) Cons(6) Cons(7)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            using `0 \<le> clause \<and> clause < length (getF state)`
            unfolding InvariantConflictClauseCharacterization_def
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          from Cons(3)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getConflictFlag ?state'' = getConflictFlag state"
            "getConflictClause ?state'' = getConflictClause state"
            unfolding setReason_def
            by auto
          moreover
          have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(5)
            using `clause \<notin> set Wl'`
            unfolding setReason_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(2) Cons(4) Cons(6) Cons(7)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (simp add: Let_def)
        qed
      qed
    qed
  qed
qed

lemma InvariantGetReasonIsReasonQSubset:
  assumes "Q \<subseteq> Q'" and
  "InvariantGetReasonIsReason GetReason F M Q'"
  shows
  "InvariantGetReasonIsReason GetReason F M Q"
using assms
unfolding InvariantGetReasonIsReason_def
by auto

lemma InvariantGetReasonIsReasonAfterNotifyWatches:
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> 0 \<le> c \<and> c < length (getF state)" and
  "\<forall> (c::nat). c \<in> set Wl \<longrightarrow> Some literal = (getWatch1 state c)  \<or> Some literal = (getWatch2 state c)" and
  "uniq Wl"
  "getM state = M @ [(opposite literal, decision)]"
  "InvariantGetReasonIsReason (getReason state) (getF state) (getM state) Q"
shows
  "let state' = notifyWatches_loop literal Wl newWl state in
   let Q' = Q \<union> (set (getQ state') - set (getQ state)) in
     InvariantGetReasonIsReason (getReason state') (getF state') (getM state') Q'"
using assms
proof (induct Wl arbitrary: newWl state Q)
  case Nil
  thus ?case
    by simp
next
  case (Cons clause Wl')

  from `uniq (clause # Wl')`
  have "clause \<notin> set Wl'" "uniq Wl'"
    by (auto simp add:uniqAppendIff)

  from `\<forall> (c::nat). c \<in> set (clause # Wl') \<longrightarrow> 0 \<le> c \<and> c < length (getF state)`
  have "0 \<le> clause \<and> clause < length (getF state)"
    by auto
  then obtain wa::Literal and wb::Literal
    where "getWatch1 state clause = Some wa" and "getWatch2 state clause = Some wb"
    using Cons
    unfolding InvariantWatchesEl_def
    by auto
  show ?case
  proof (cases "Some literal = getWatch1 state clause")
    case True
    let ?state' = "swapWatches clause state"
    let ?w1 = wb
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch2 state clause = Some wb`
      unfolding swapWatches_def
      by auto
    let ?w2 = wa
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch1 state clause = Some wa`
      unfolding swapWatches_def
      by auto
    with True have
      "?w2 = literal"
      unfolding swapWatches_def
      by simp
    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(6)
      by simp

    from `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `0 \<le> clause \<and> clause < length (getF state)`
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      
      from Cons(2)
      have "InvariantWatchesEl (getF ?state') (getWatch1 ?state') (getWatch2 ?state')"
        unfolding InvariantWatchesEl_def
        unfolding swapWatches_def
        by auto 
      moreover
      have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state' c \<or> Some literal = getWatch2 ?state' c"
        using Cons(4)
        unfolding swapWatches_def
        by auto
      moreover
      have "getM ?state' = getM state \<and> 
        getF ?state' = getF state \<and> 
        getQ ?state' = getQ state \<and> 
        getReason ?state' = getReason state
        "
        unfolding swapWatches_def
        by simp
      ultimately
      show ?thesis
        using Cons(1)[of "?state'" "Q" "clause # newWl"]
        using Cons(3) Cons(6) Cons(7)
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `Some literal = getWatch1 state clause`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq Wl'`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state') clause)"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state') clause)`
          unfolding InvariantWatchesEl_def
          unfolding swapWatches_def
          unfolding setWatch2_def
          by auto
        moreover
        have "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
          using Cons(4)
          using `clause \<notin> set Wl'`
          using swapWatchesEffect[of "clause" "state"]
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getReason ?state'' = getReason state"
          unfolding swapWatches_def
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''" "Q" "newWl"]
          using Cons(3) Cons(6) Cons(7)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using Some
          using `uniq Wl'`
          by (simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp
        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            by auto
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(4)
            unfolding swapWatches_def
            by auto
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state \<and> 
            getReason ?state'' = getReason state"
            unfolding swapWatches_def
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''" "Q""clause # newWl"]
            using Cons(3) Cons(6) Cons(7)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          let ?state0 = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"


          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            "getReason ?state'' = (getReason state)(?w1 := Some clause)"
            unfolding swapWatches_def
            unfolding setReason_def
            by auto
          moreover
          hence "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(4)
            using `clause \<notin> set Wl'`
            using swapWatchesEffect[of "clause" "state"]
            unfolding setReason_def
            by simp
          moreover
          have "isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))"
            using `\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))`
            using `?w1 el (nth (getF state) clause)`
            using `?w2 el (nth (getF state) clause)`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `literalFalse ?w2 (elements (getM state))`
            unfolding swapWatches_def
            unfolding isUnitClause_def
            by auto
          hence "InvariantGetReasonIsReason (getReason ?state'') (getF ?state'') (getM ?state'') (Q \<union> {?w1})"
            using Cons(7)
            using `getM ?state'' = getM state`
            using `getF ?state'' = getF state`
            using `getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])`
            using `getReason ?state'' = (getReason state)(?w1 := Some clause)`
            using `0 \<le> clause \<and> clause < length (getF state)`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using `isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))`
            unfolding swapWatches_def
            unfolding InvariantGetReasonIsReason_def
            by auto
          moreover
          have "(\<lambda>a. if a = ?w1 then Some clause else getReason state a) = getReason ?state''"
            unfolding setReason_def
            unfolding swapWatches_def
            by (auto simp add: fun_upd_def)
          ultimately
          have "InvariantGetReasonIsReason (getReason ?state0) (getF ?state0) (getM ?state0) 
                  (Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1})"
            using Cons(1)[of "?state''" "Q \<union> {?w1}" "clause # newWl"]
            using Cons(3) Cons(6) Cons(7)
            using `uniq Wl'`
            by (simp add: Let_def split: split_if_asm)
          moreover
          have "(Q \<union> (set (getQ ?state0) - set (getQ state))) \<subseteq> (Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1})"
            using `getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])`
            unfolding swapWatches_def
            by auto
          ultimately
          have "InvariantGetReasonIsReason (getReason ?state0) (getF ?state0) (getM ?state0) 
                  (Q \<union> (set (getQ ?state0) - set (getQ state)))"
            using InvariantGetReasonIsReasonQSubset[of "Q \<union> (set (getQ ?state0) - set (getQ state))" 
              "Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1}" "getReason ?state0" "getF ?state0" "getM ?state0"]
            by simp
          moreover
          have "notifyWatches_loop literal (clause # Wl') newWl state = ?state0"
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (simp add: Let_def)
          ultimately
          show ?thesis
            by simp
        qed
      qed
    qed
  next
    case False
    let ?state' = state
    let ?w1 = wa
    have "getWatch1 ?state' clause = Some ?w1"
      using `getWatch1 state clause = Some wa`
      by auto
    let ?w2 = wb
    have "getWatch2 ?state' clause = Some ?w2"
      using `getWatch2 state clause = Some wb`
      by auto

    have "?w2 = literal"
      using `0 \<le> clause \<and> clause < length (getF state)`
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using Cons(4)
      using False
      by simp

    hence "literalFalse ?w2 (elements (getM state))"
      using Cons(6)
      by simp

    from `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    have "?w1 el (nth (getF state) clause)" "?w2 el (nth (getF state) clause)"
      using `getWatch1 ?state' clause = Some ?w1`
      using `getWatch2 ?state' clause = Some ?w2`
      using `0 \<le> clause \<and> clause < length (getF state)`
      unfolding InvariantWatchesEl_def
      unfolding swapWatches_def
      by auto

    show ?thesis
    proof (cases "literalTrue ?w1 (elements (getM ?state'))")
      case True
      thus ?thesis
        using Cons(1)[of "state" "Q" "clause # newWl"]
        using Cons(2) Cons(3) Cons(4) Cons(5) Cons(6) Cons(7)
        using `\<not> Some literal = getWatch1 state clause`
        using `getWatch1 ?state' clause = Some ?w1`
        using `getWatch2 ?state' clause = Some ?w2`
        using `literalTrue ?w1 (elements (getM ?state'))`
        using `uniq Wl'`
        by (simp add:Let_def)
    next
      case False
      show ?thesis
      proof (cases "getNonWatchedUnfalsifiedLiteral (nth (getF ?state') clause) ?w1 ?w2 (getM ?state')")
        case (Some l')
        hence "l' el (nth (getF ?state')) clause"
          using getNonWatchedUnfalsifiedLiteralSomeCharacterization
          by simp

        let ?state'' = "setWatch2 clause l' ?state'"

        from Cons(2)
        have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
          using `l' el (nth (getF ?state')) clause`
          unfolding InvariantWatchesEl_def
          unfolding setWatch2_def
          by auto
        moreover
        have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
          using Cons(4)
          using `clause \<notin> set Wl'`
          unfolding setWatch2_def
          by simp
        moreover
        have "getM ?state'' = getM state \<and>
          getF ?state'' = getF state \<and> 
          getQ ?state'' = getQ state \<and> 
          getReason ?state'' = getReason state"
          unfolding setWatch2_def
          by simp
        ultimately
        show ?thesis
          using Cons(1)[of "?state''"]
          using Cons(3) Cons(6) Cons(7)
          using `getWatch1 ?state' clause = Some ?w1`
          using `getWatch2 ?state' clause = Some ?w2`
          using `\<not> Some literal = getWatch1 state clause`
          using `\<not> literalTrue ?w1 (elements (getM ?state'))`
          using `uniq Wl'`
          using Some
          by (simp add: Let_def)
      next
        case None
        hence "\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))"
          using getNonWatchedUnfalsifiedLiteralNoneCharacterization
          by simp

        show ?thesis
        proof (cases "literalFalse ?w1 (elements (getM ?state'))")
          case True
          let ?state'' = "?state'\<lparr>getConflictFlag := True, getConflictClause := clause\<rparr>"
          
          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            by auto
          moreover
          have "\<forall>c. c \<in> set Wl' \<longrightarrow> Some literal = getWatch1 ?state'' c \<or> Some literal = getWatch2 ?state'' c"
            using Cons(4)
            using `clause \<notin> set Wl'`
            unfolding setWatch2_def
            by simp
          moreover
          have "getM ?state'' = getM state \<and>
            getF ?state'' = getF state \<and> 
            getQ ?state'' = getQ state \<and> 
            getReason ?state'' = getReason state"
            by simp
          ultimately
          show ?thesis
            using Cons(1)[of "?state''"]
            using Cons(3) Cons(6) Cons(7)
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (simp add: Let_def)
        next
          case False
          let ?state'' = "setReason ?w1 clause (?state'\<lparr>getQ := (if ?w1 el (getQ ?state') then (getQ ?state') else (getQ ?state') @ [?w1])\<rparr>)"
          let ?state0 = "notifyWatches_loop literal Wl' (clause # newWl) ?state''"


          from Cons(2)
          have "InvariantWatchesEl (getF ?state'') (getWatch1 ?state'') (getWatch2 ?state'')"
            unfolding InvariantWatchesEl_def
            unfolding setReason_def
            by auto
          moreover
          have "getM ?state'' = getM state"
            "getF ?state'' = getF state"
            "getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])"
            "getReason ?state'' = (getReason state)(?w1 := Some clause)"
            unfolding setReason_def
            by auto
          moreover
          hence "\<forall>  (c::nat). c \<in> set Wl' \<longrightarrow> Some literal = (getWatch1 ?state'' c)  \<or> Some literal = (getWatch2 ?state'' c)"
            using Cons(4)
            using `clause \<notin> set Wl'`
            unfolding setReason_def
            by simp
          moreover
          have "isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))"
            using `\<forall> l. l el (nth (getF ?state') clause) \<and> l \<noteq> ?w1 \<and> l \<noteq> ?w2 \<longrightarrow> literalFalse l (elements (getM ?state'))`
            using `?w1 el (nth (getF state) clause)`
            using `?w2 el (nth (getF state) clause)`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `literalFalse ?w2 (elements (getM state))`
            unfolding isUnitClause_def
            by auto
          hence "InvariantGetReasonIsReason (getReason ?state'') (getF ?state'') (getM ?state'') (Q \<union> {?w1})"
            using Cons(7)
            using `getM ?state'' = getM state`
            using `getF ?state'' = getF state`
            using `getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])`
            using `getReason ?state'' = (getReason state)(?w1 := Some clause)`
            using `0 \<le> clause \<and> clause < length (getF state)`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using `isUnitClause (nth (getF state) clause) ?w1 (elements (getM state))`
            unfolding InvariantGetReasonIsReason_def
            by auto
          moreover
          have "(\<lambda>a. if a = ?w1 then Some clause else getReason state a) = getReason ?state''"
            unfolding setReason_def
            by (auto simp add: fun_upd_def)
          ultimately
          have "InvariantGetReasonIsReason (getReason ?state0) (getF ?state0) (getM ?state0) 
                  (Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1})"
            using Cons(1)[of "?state''" "Q \<union> {?w1}" "clause # newWl"]
            using Cons(3) Cons(6) Cons(7)
            using `uniq Wl'`
            by (simp add: Let_def split: split_if_asm)
          moreover
          have "(Q \<union> (set (getQ ?state0) - set (getQ state))) \<subseteq> (Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1})"
            using `getQ ?state'' = (if ?w1 el (getQ state) then (getQ state) else (getQ state) @ [?w1])`
            by auto
          ultimately
          have "InvariantGetReasonIsReason (getReason ?state0) (getF ?state0) (getM ?state0) 
                  (Q \<union> (set (getQ ?state0) - set (getQ state)))"
            using InvariantGetReasonIsReasonQSubset[of "Q \<union> (set (getQ ?state0) - set (getQ state))" 
              "Q \<union> (set (getQ ?state0) - set (getQ ?state'')) \<union> {?w1}" "getReason ?state0" "getF ?state0" "getM ?state0"]
            by simp
          moreover
          have "notifyWatches_loop literal (clause # Wl') newWl state = ?state0"
            using `getWatch1 ?state' clause = Some ?w1`
            using `getWatch2 ?state' clause = Some ?w2`
            using `\<not> Some literal = getWatch1 state clause`
            using `\<not> literalTrue ?w1 (elements (getM ?state'))`
            using None
            using `\<not> literalFalse ?w1 (elements (getM ?state'))`
            using `uniq Wl'`
            by (simp add: Let_def)
          ultimately
          show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed


(****************************************************************************)
(*  A S S E R T   L I T E R A L                                             *)
(****************************************************************************)

lemma assertLiteralEffect:
fixes state::State and l::Literal and d::bool
assumes 
"InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
"InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
shows
"(getM (assertLiteral l d state)) = (getM state) @ [(l, d)]" and 
"(getF (assertLiteral l d state)) = (getF state)" and
"(getSATFlag (assertLiteral l d state)) = (getSATFlag state)" and
"isPrefix (getQ state) (getQ (assertLiteral l d state))"
using assms
unfolding assertLiteral_def
unfolding notifyWatches_def
unfolding InvariantWatchListsContainOnlyClausesFromF_def
using notifyWatchesLoopPreservedVariables[of "(state\<lparr>getM := getM state @ [(l, d)]\<rparr>)" "getWatchList (state\<lparr>getM := getM state @ [(l, d)]\<rparr>) (opposite l)"]
by (auto simp add: Let_def)

lemma WatchInvariantsAfterAssertLiteral:
assumes
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
shows
  "let state' = (assertLiteral literal decision state) in
     InvariantWatchListsContainOnlyClausesFromF (getWatchList state') (getF state') \<and> 
     InvariantWatchListsUniq (getWatchList state') \<and> 
     InvariantWatchListsCharacterization (getWatchList state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantWatchesEl (getF state') (getWatch1 state') (getWatch2 state') \<and> 
     InvariantWatchesDiffer (getF state') (getWatch1 state') (getWatch2 state')
"
using assms
unfolding assertLiteral_def
unfolding notifyWatches_def
using InvariantWatchesElNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>" "getWatchList state (opposite literal)" "opposite literal" "[]"]
using InvariantWatchesDifferNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>" "getWatchList state (opposite literal)" "opposite literal" "[]"]
using InvariantWatchListsContainOnlyClausesFromFNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>" "getWatchList state (opposite literal)" "[]" "opposite literal"]
using InvariantWatchListsCharacterizationNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>" "(getWatchList (state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>) (opposite literal))" "opposite literal" "[]"]
unfolding InvariantWatchListsContainOnlyClausesFromF_def
unfolding InvariantWatchListsCharacterization_def
unfolding InvariantWatchListsUniq_def
by (auto simp add: Let_def)


lemma InvariantWatchCharacterizationAfterAssertLiteral:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])" and
  "InvariantUniq ((getM state) @ [(literal, decision)])" and
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
shows
  "let state' = (assertLiteral literal decision state) in
      InvariantWatchCharacterization (getF state') (getWatch1 state') (getWatch2 state') (getM state')"
proof-
  let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
  let ?state' = "assertLiteral literal decision state"
  have *: "\<forall>c. c \<in> set (getWatchList ?state (opposite literal)) \<longrightarrow>
            (\<forall>w1 w2. Some w1 = getWatch1 ?state' c \<and> Some w2 = getWatch2 ?state' c \<longrightarrow>
                     watchCharacterizationCondition w1 w2 (getM ?state') (getF ?state' ! c) \<and>
                     watchCharacterizationCondition w2 w1 (getM ?state') (getF ?state' ! c))"
    using assms
    using NotifyWatchesLoopWatchCharacterizationEffect[of "?state" "getM state" "getWatchList ?state (opposite literal)" "opposite literal" "decision" "[]"]
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (simp add: Let_def)
  {
    fix c
    assume "0 \<le> c" and "c < length (getF ?state')"
    fix w1::Literal and w2::Literal
    assume "Some w1 = getWatch1 ?state' c" "Some w2 = getWatch2 ?state' c"
    have "watchCharacterizationCondition w1 w2 (getM ?state') (getF ?state' ! c) \<and>
          watchCharacterizationCondition w2 w1 (getM ?state') (getF ?state' ! c)"
    proof (cases "c \<in> set (getWatchList ?state (opposite literal))")
      case True
      thus ?thesis
        using *
        using `Some w1 = getWatch1 ?state' c` `Some w2 = getWatch2 ?state' c`
        by auto
    next
      case False
      hence "Some (opposite literal) \<noteq> getWatch1 state c" and "Some (opposite literal) \<noteq> getWatch2 state c"
        using `InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)`
        unfolding InvariantWatchListsCharacterization_def
        by auto
      moreover
      from assms False
      have "getWatch1 ?state' c = getWatch1 state c" and "getWatch2 ?state' c = getWatch2 state c"
        using notifyWatchesLoopPreservedWatches[of "?state" "getWatchList ?state (opposite literal)" "opposite literal" "[]"]
        using False
        unfolding assertLiteral_def
        unfolding notifyWatches_def
        unfolding InvariantWatchListsContainOnlyClausesFromF_def
        by (auto simp add: Let_def)
      ultimately
      have "w1 \<noteq> opposite literal" "w2 \<noteq> opposite literal"
        using `Some w1 = getWatch1 ?state' c` and `Some w2 = getWatch2 ?state' c`
        by auto

      have "watchCharacterizationCondition w1 w2 (getM state) (getF state ! c)" and
           "watchCharacterizationCondition w2 w1 (getM state) (getF state ! c)"
        using `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)`
        using `Some w1 = getWatch1 ?state' c` and `Some w2 = getWatch2 ?state' c`
        using `getWatch1 ?state' c = getWatch1 state c` and `getWatch2 ?state' c = getWatch2 state c`
        unfolding InvariantWatchCharacterization_def
        using `c < length (getF ?state')`
        using assms
        using assertLiteralEffect[of "state" "literal" "decision"]
        by auto

      have "watchCharacterizationCondition w1 w2 (getM ?state') ((getF ?state') ! c)"
      proof-
        {
          assume "literalFalse w1 (elements (getM ?state'))"
            with `w1 \<noteq> opposite literal`
            have "literalFalse w1 (elements (getM state))"
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            by simp
          with `watchCharacterizationCondition w1 w2 (getM state) (getF state ! c)`
          have "(\<exists> l. l el ((getF state) ! c) \<and> literalTrue l (elements (getM state))
            \<and> elementLevel l (getM state) \<le> elementLevel (opposite w1) (getM state)) \<or> 
            (\<forall>l. l el (getF state ! c) \<and> l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow>
            literalFalse l (elements (getM state)) \<and> 
            elementLevel (opposite l) (getM state) \<le> elementLevel (opposite w1) (getM state))" (is "?a state \<or> ?b state")
            unfolding watchCharacterizationCondition_def
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            using `w1 \<noteq> opposite literal`
            by simp
          have "?a ?state' \<or> ?b ?state'"
          proof (cases "?b state")
            case True
            show ?thesis
            proof-
              {
                fix l
                assume "l el (nth (getF ?state') c)" "l \<noteq> w1" "l \<noteq> w2"
                have "literalFalse l (elements (getM ?state')) \<and> 
                      elementLevel (opposite l) (getM ?state') \<le> elementLevel (opposite w1) (getM ?state')"
                proof-
                  from True `l el (nth (getF ?state') c)` `l \<noteq> w1` `l \<noteq> w2`
                  have "literalFalse l (elements (getM state))"
                    "elementLevel (opposite l) (getM state) \<le> elementLevel (opposite w1) (getM state)"
                    using assms 
                    using assertLiteralEffect[of "state" "literal" "decision"]
                    by auto
                  thus ?thesis
                    using `literalFalse w1 (elements (getM state))`
                    using elementLevelAppend[of "opposite w1" "getM state" "[(literal, decision)]"]
                    using elementLevelAppend[of "opposite l" "getM state" "[(literal, decision)]"]
                    using assms 
                    using assertLiteralEffect[of "state" "literal" "decision"]
                    by auto
                qed
              }
              thus ?thesis
                by simp
            qed
          next
            case False
            with `?a state \<or> ?b state`
            obtain l::Literal
              where "l el (getF state ! c)" "literalTrue l (elements (getM state))" 
              "elementLevel l (getM state) \<le> elementLevel (opposite w1) (getM state)"
              by auto
            
            from `w1 \<noteq> opposite literal`
              `literalFalse w1 (elements (getM ?state'))`
            have "elementLevel (opposite w1) ((getM state) @ [(literal, decision)]) = elementLevel (opposite w1) (getM state)"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              unfolding elementLevel_def
              by (simp add: markedElementsToAppend)
            moreover
            from `literalTrue l (elements (getM state))`
            have "elementLevel l ((getM state) @ [(literal, decision)]) = elementLevel l (getM state)"
              unfolding elementLevel_def
              by (simp add: markedElementsToAppend)
            ultimately
            have "elementLevel l ((getM state) @ [(literal, decision)]) \<le> elementLevel (opposite w1) ((getM state) @ [(literal, decision)])"
              using `elementLevel l (getM state) \<le> elementLevel (opposite w1) (getM state)`
              by simp
            thus ?thesis
              using `l el (getF state ! c)` `literalTrue l (elements (getM state))`
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              by auto
          qed
        }
        thus ?thesis
          unfolding watchCharacterizationCondition_def
          by auto
      qed
      moreover
      have "watchCharacterizationCondition w2 w1 (getM ?state') ((getF ?state') ! c)"
      proof-
        {
          assume "literalFalse w2 (elements (getM ?state'))"
            with `w2 \<noteq> opposite literal`
            have "literalFalse w2 (elements (getM state))"
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            by simp
          with `watchCharacterizationCondition w2 w1 (getM state) (getF state ! c)`
          have "(\<exists> l. l el ((getF state) ! c) \<and> literalTrue l (elements (getM state))
            \<and> elementLevel l (getM state) \<le> elementLevel (opposite w2) (getM state)) \<or> 
            (\<forall>l. l el (getF state ! c) \<and> l \<noteq> w2 \<and> l \<noteq> w1 \<longrightarrow>
            literalFalse l (elements (getM state)) \<and> 
            elementLevel (opposite l) (getM state) \<le> elementLevel (opposite w2) (getM state))" (is "?a state \<or> ?b state")
            unfolding watchCharacterizationCondition_def
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            using `w2 \<noteq> opposite literal`
            by simp
          have "?a ?state' \<or> ?b ?state'"
          proof (cases "?b state")
            case True
            show ?thesis
            proof-
              {
                fix l
                assume "l el (nth (getF ?state') c)" "l \<noteq> w1" "l \<noteq> w2"
                have "literalFalse l (elements (getM ?state')) \<and> 
                      elementLevel (opposite l) (getM ?state') \<le> elementLevel (opposite w2) (getM ?state')"
                proof-
                  from True `l el (nth (getF ?state') c)` `l \<noteq> w1` `l \<noteq> w2`
                  have "literalFalse l (elements (getM state))"
                    "elementLevel (opposite l) (getM state) \<le> elementLevel (opposite w2) (getM state)"
                    using assms 
                    using assertLiteralEffect[of "state" "literal" "decision"]
                    by auto
                  thus ?thesis
                    using `literalFalse w2 (elements (getM state))`
                    using elementLevelAppend[of "opposite w2" "getM state" "[(literal, decision)]"]
                    using elementLevelAppend[of "opposite l" "getM state" "[(literal, decision)]"]
                    using assms 
                    using assertLiteralEffect[of "state" "literal" "decision"]
                    by auto
                qed
              }
              thus ?thesis
                by simp
            qed
          next
            case False
            with `?a state \<or> ?b state`
            obtain l::Literal
              where "l el (getF state ! c)" "literalTrue l (elements (getM state))" 
              "elementLevel l (getM state) \<le> elementLevel (opposite w2) (getM state)"
              by auto
            
            from `w2 \<noteq> opposite literal`
              `literalFalse w2 (elements (getM ?state'))`
            have "elementLevel (opposite w2) ((getM state) @ [(literal, decision)]) = elementLevel (opposite w2) (getM state)"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              unfolding elementLevel_def
              by (simp add: markedElementsToAppend)
            moreover
            from `literalTrue l (elements (getM state))`
            have "elementLevel l ((getM state) @ [(literal, decision)]) = elementLevel l (getM state)"
              unfolding elementLevel_def
              by (simp add: markedElementsToAppend)
            ultimately
            have "elementLevel l ((getM state) @ [(literal, decision)]) \<le> elementLevel (opposite w2) ((getM state) @ [(literal, decision)])"
              using `elementLevel l (getM state) \<le> elementLevel (opposite w2) (getM state)`
              by simp
            thus ?thesis
              using `l el (getF state ! c)` `literalTrue l (elements (getM state))`
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              by auto
          qed
        }
        thus ?thesis
          unfolding watchCharacterizationCondition_def
          by auto
      qed
      ultimately
      show ?thesis
        by simp
    qed
  }
  thus ?thesis
    unfolding InvariantWatchCharacterization_def
    by (simp add: Let_def)
qed


lemma assertLiteralConflictFlagEffect:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantUniq ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
shows
"let state' = assertLiteral literal decision state in
    getConflictFlag state' = (getConflictFlag state \<or> 
                                 (\<exists> clause. clause el (getF state) \<and> 
                                            opposite literal el clause \<and> 
                                            clauseFalse clause ((elements (getM state)) @ [literal])))"
proof-
  let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
  let ?state' = "assertLiteral literal decision state"

  have "getConflictFlag ?state' = (getConflictFlag state \<or> 
          (\<exists> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<and> 
                     clauseFalse (nth (getF ?state) clause) (elements (getM ?state))))"
    using NotifyWatchesLoopConflictFlagEffect[of "?state" 
      "getWatchList ?state (opposite literal)"
      "opposite literal" "[]"]
    using `InvariantConsistent ((getM state) @ [(literal, decision)])`
    using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)`
    using `InvariantWatchListsUniq (getWatchList state)`
    using `InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)`
    using `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (simp add: Let_def)
  moreover
  have "(\<exists> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<and> 
                     clauseFalse (nth (getF ?state) clause) (elements (getM ?state))) = 
        (\<exists> clause. clause el (getF state) \<and> 
                     opposite literal el clause \<and> 
                     clauseFalse clause ((elements (getM state)) @ [literal]))" (is "?lhs = ?rhs")
  proof
    assume "?lhs"
    then obtain clause
      where "clause \<in> set (getWatchList ?state (opposite literal))" 
      "clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
      by auto

    have "getWatch1 ?state clause = Some (opposite literal) \<or> getWatch2 ?state clause = Some (opposite literal)"
      "clause < length (getF ?state)"
      "\<exists> w1 w2. getWatch1 ?state clause = Some w1 \<and> getWatch2 ?state clause = Some w2 \<and> 
      w1 el (nth (getF ?state) clause) \<and> w2 el (nth (getF ?state) clause)"
      using `clause \<in> set (getWatchList ?state (opposite literal))`
      using assms
      unfolding InvariantWatchListsContainOnlyClausesFromF_def
      unfolding InvariantWatchesEl_def
      unfolding InvariantWatchListsCharacterization_def
      by auto
    hence "(nth (getF ?state) clause) el (getF ?state)"
      "opposite literal el (nth (getF ?state) clause)"
      using nth_mem[of "clause" "getF ?state"]
      by auto
    thus "?rhs"
      using `clauseFalse (nth (getF ?state) clause) (elements (getM ?state))`
      by auto
  next
    assume "?rhs"
    then obtain clause
      where "clause el (getF ?state)" 
      "opposite literal el clause"
      "clauseFalse clause ((elements (getM state)) @ [literal])"
      by auto
    then obtain ci
      where "clause = (nth (getF ?state) ci)" "ci < length (getF ?state)"
      by (auto simp add: in_set_conv_nth)
    moreover
    from `ci < length (getF ?state)`
    obtain w1 w2
      where "getWatch1 state ci = Some w1" "getWatch2 state ci = Some w2" 
      "w1 el (nth (getF state) ci)" "w2 el (nth (getF state) ci)"
      using assms
      unfolding InvariantWatchesEl_def
      by auto
    have " getWatch1 state ci = Some (opposite literal) \<or> getWatch2 state ci = Some (opposite literal)"
    proof-
      {
        assume "\<not> ?thesis"
        with `clauseFalse clause ((elements (getM state)) @ [literal])`
          `clause = (nth (getF ?state) ci)`
          `getWatch1 state ci = Some w1` `getWatch2 state ci = Some w2`
          `w1 el (nth (getF state) ci)` `w2 el (nth (getF state) ci)`
        have "literalFalse w1 (elements (getM state))" "literalFalse w2 (elements (getM state))"
          by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
        

        
        from `InvariantConsistent ((getM state) @ [(literal, decision)])`
        `clauseFalse clause ((elements (getM state)) @ [literal])`
        have "\<not> (\<exists> l. l el clause \<and> literalTrue l (elements (getM state)))"
          unfolding InvariantConsistent_def
          by (auto simp add: inconsistentCharacterization clauseFalseIffAllLiteralsAreFalse)


        from `InvariantUniq ((getM state) @ [(literal, decision)])`
        have "\<not> literalTrue literal (elements (getM state))"
          unfolding InvariantUniq_def
          by (auto simp add: uniqAppendIff)
        
        from `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)`
          `literalFalse w1 (elements (getM state))` `literalFalse w2 (elements (getM state))`
          `\<not> (\<exists> l. l el clause \<and> literalTrue l (elements (getM state)))`
          `getWatch1 state ci = Some w1`[THEN sym] 
          `getWatch2 state ci = Some w2`[THEN sym]
          `ci < length (getF ?state)`
          `clause = (nth (getF ?state) ci)`
        have "\<forall> l. l el clause \<and> l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state))"
          unfolding InvariantWatchCharacterization_def
          unfolding watchCharacterizationCondition_def
          by auto
        hence "literalTrue literal (elements (getM state))"
          using `\<not> (getWatch1 state ci = Some (opposite literal) \<or> getWatch2 state ci = Some (opposite literal))`
          using `opposite literal el clause`
          using `getWatch1 state ci = Some w1`
          using `getWatch2 state ci = Some w2`
          by auto
        with `\<not> literalTrue literal (elements (getM state))`
        have False
          by simp
      }
      thus ?thesis
        by auto
    qed
    ultimately
    show "?lhs"
      using assms
      using `clauseFalse clause ((elements (getM state)) @ [literal])`
      unfolding InvariantWatchListsCharacterization_def
      by force
  qed
  ultimately
  show ?thesis
    by auto
qed

lemma InvariantConflictFlagCharacterizationAfterAssertLiteral:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
shows
  "let state' = (assertLiteral literal decision state) in
      InvariantConflictFlagCharacterization (getConflictFlag state') (getF state') (getM state')"
proof-
  let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
  let ?state' = "assertLiteral literal decision state"

  have *:"getConflictFlag ?state' = (getConflictFlag state \<or> 
          (\<exists> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<and> 
                     clauseFalse (nth (getF ?state) clause) (elements (getM ?state))))"
    using NotifyWatchesLoopConflictFlagEffect[of "?state" 
      "getWatchList ?state (opposite literal)"
      "opposite literal" "[]"]
    using `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
    using `InvariantConsistent ((getM state) @ [(literal, decision)])`
    using `InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)`
    using `InvariantWatchListsUniq (getWatchList state)`
    using `InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)`
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (simp add: Let_def)

  hence "getConflictFlag state \<longrightarrow> getConflictFlag ?state'"
    by simp

  show ?thesis
  proof (cases "getConflictFlag state")
    case True
    thus ?thesis
      using `InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)`
      using assertLiteralEffect[of "state" "literal" "decision"]
      using `getConflictFlag state \<longrightarrow> getConflictFlag ?state'`
      using assms
      unfolding InvariantConflictFlagCharacterization_def
      by (auto simp add: Let_def formulaFalseAppendValuation)
  next
    case False
    
    hence "\<not> formulaFalse (getF state) (elements (getM state))"
      using `InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)`
      unfolding InvariantConflictFlagCharacterization_def
      by simp

    have **: "\<forall> clause. clause \<notin> set (getWatchList ?state (opposite literal)) \<and> 
                          0 \<le> clause \<and> clause < length (getF ?state) \<longrightarrow> 
                          \<not> clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
    proof-
      {
        fix clause
        assume "clause \<notin> set (getWatchList ?state (opposite literal))" and
          "0 \<le> clause \<and> clause < length (getF ?state)"

        from `0 \<le> clause \<and> clause < length (getF ?state)`
        obtain w1::Literal and w2::Literal
          where "getWatch1 ?state clause = Some w1" and
                "getWatch2 ?state clause = Some w2" and
                "w1 el (nth (getF ?state) clause)" and
                "w2 el (nth (getF ?state) clause)"
          using `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
          unfolding InvariantWatchesEl_def
          by auto

        have "\<not> clauseFalse (nth (getF ?state) clause) (elements (getM ?state))" 
        proof-
          from `clause \<notin> set (getWatchList ?state (opposite literal))`
          have "w1 \<noteq> opposite literal" and
               "w2 \<noteq> opposite literal"
            using `InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)`
            using `getWatch1 ?state clause = Some w1` and `getWatch2 ?state clause = Some w2`
            unfolding InvariantWatchListsCharacterization_def
            by auto

          from `\<not> formulaFalse (getF state) (elements (getM state))`
          have "\<not> clauseFalse (nth (getF ?state) clause) (elements (getM state))"
            using  `0 \<le> clause \<and> clause < length (getF ?state)`
            by (simp add: formulaFalseIffContainsFalseClause)
        
          
          show ?thesis
          proof (cases "literalFalse w1 (elements (getM state)) \<or> literalFalse w2 (elements (getM state))")
            case True
            (* Depends on the watch characterization invariant *)
            with `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)`
            have $: "(\<exists> l. l el (nth (getF state) clause) \<and> literalTrue l (elements (getM state))) \<or> 
                  (\<forall> l. l el (nth (getF state) clause) \<and> 
                         l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state)))
              "
              using `getWatch1 ?state clause = Some w1`[THEN sym]
              using `getWatch2 ?state clause = Some w2`[THEN sym]
              using `0 \<le> clause \<and> clause < length (getF ?state)`
              unfolding InvariantWatchCharacterization_def
              unfolding watchCharacterizationCondition_def
              by auto

            thus ?thesis
            proof (cases "\<forall> l. l el (nth (getF state) clause) \<and> 
                            l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state))")
              case True
              have "\<not> literalFalse w1 (elements (getM state)) \<or> \<not> literalFalse w2 (elements (getM state))"
              proof-
                from `\<not> clauseFalse (nth (getF ?state) clause) (elements (getM state))`
                obtain l::Literal
                  where "l el (nth (getF ?state) clause)" and "\<not> literalFalse l (elements (getM state))"
                  by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
                with True
                show ?thesis
                  by auto
              qed
              hence "\<not> literalFalse w1 (elements (getM ?state)) \<or> \<not> literalFalse w2 (elements (getM ?state))"
                using `w1 \<noteq> opposite literal` and `w2 \<noteq> opposite literal`
                by auto
              thus ?thesis
                using `w1 el (nth (getF ?state) clause)` `w2 el (nth (getF ?state) clause)`
                by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
            next
              case False
              then obtain l::Literal
              where "l el (nth (getF state) clause)" and "literalTrue l (elements (getM state))"
                using $
                by auto
              thus ?thesis
                using `InvariantConsistent ((getM state) @ [(literal, decision)])`
                unfolding InvariantConsistent_def
                by (auto simp add: clauseFalseIffAllLiteralsAreFalse inconsistentCharacterization)
            qed
          next
            case False
            thus ?thesis
              using `w1 el (nth (getF ?state) clause)` and
                `w1 \<noteq> opposite literal`
              by (auto simp add: clauseFalseIffAllLiteralsAreFalse)
          qed
        qed
      } thus ?thesis
        by simp
    qed

    show ?thesis
    proof (cases "getConflictFlag ?state'")
      case True
      from `\<not> getConflictFlag state` `getConflictFlag ?state'`
      obtain clause::nat
        where
        "clause \<in> set (getWatchList ?state (opposite literal))" and
         "clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
        using *
        by auto
      from `InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)`
        `clause \<in> set (getWatchList ?state (opposite literal))`
      have "(nth (getF ?state) clause) el (getF ?state)"
        unfolding InvariantWatchListsContainOnlyClausesFromF_def
        using nth_mem
        by simp
      with `clauseFalse (nth (getF ?state) clause) (elements (getM ?state))` 
      have "formulaFalse (getF ?state) (elements (getM ?state))"
        by (auto simp add: Let_def formulaFalseIffContainsFalseClause)  
      thus ?thesis
        using `\<not> getConflictFlag state` `getConflictFlag ?state'`
        unfolding InvariantConflictFlagCharacterization_def
        using assms
        using assertLiteralEffect[of "state" "literal" "decision"]
        by (simp add: Let_def)
    next
      case False
      hence "\<forall> clause::nat. clause \<in> set (getWatchList ?state (opposite literal)) \<longrightarrow> 
        \<not> clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
        using *
        by auto
      with **
      have "\<forall> clause. 0 \<le> clause \<and> clause < length (getF ?state) \<longrightarrow> 
                          \<not> clauseFalse (nth (getF ?state) clause) (elements (getM ?state))"
        by auto
      hence "\<not> formulaFalse (getF ?state) (elements (getM ?state))"
        by (auto simp add:set_conv_nth formulaFalseIffContainsFalseClause)
      thus ?thesis
        using `\<not> getConflictFlag state` `\<not> getConflictFlag ?state'`
        using assms
        unfolding InvariantConflictFlagCharacterization_def
        by (auto simp add: Let_def assertLiteralEffect)
    qed
  qed
qed

lemma InvariantConflictClauseCharacterizationAfterAssertLiteral:
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantConflictClauseCharacterization (getConflictFlag state) (getConflictClause state) (getF state) (getM state)"
shows 
  "let state' = assertLiteral literal decision state in
   InvariantConflictClauseCharacterization (getConflictFlag state') (getConflictClause state') (getF state') (getM state')"
proof-
  let ?state0 = "state\<lparr> getM := getM state @ [(literal, decision)]\<rparr>"
  show ?thesis
    using assms
    using InvariantConflictClauseCharacterizationAfterNotifyWatches[of "?state0" "getM state" "opposite literal" "decision" 
    "getWatchList ?state0 (opposite literal)" "[]"]
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantConflictClauseCharacterization_def
    by (simp add: Let_def clauseFalseAppendValuation)
qed

lemma assertLiteralQEffect:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantUniq ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
shows
"let state' = assertLiteral literal decision state in
    set (getQ state') = set (getQ state) \<union> 
           { ul. (\<exists> uc. uc el (getF state) \<and> 
                        opposite literal el uc \<and> 
                        isUnitClause uc ul ((elements (getM state)) @ [literal])) }" 
   (is "let state' = assertLiteral literal decision state in
    set (getQ state') = set (getQ state) \<union> ?ulSet")
proof-
    let ?state' = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
    let ?state'' = "assertLiteral literal decision state"
    
    have "set (getQ ?state'') - set (getQ state) \<subseteq> ?ulSet"
      unfolding assertLiteral_def
      unfolding notifyWatches_def
      using assms
      using NotifyWatchesLoopQEffect[of "?state'" "getM state" "opposite literal" "decision" "getWatchList ?state' (opposite literal)" "[]"]
      unfolding InvariantWatchListsCharacterization_def
      unfolding InvariantWatchListsUniq_def
      unfolding InvariantWatchListsContainOnlyClausesFromF_def
      using set_conv_nth[of "getF state"]
      by (auto simp add: Let_def)
    moreover
    have "?ulSet \<subseteq> set (getQ ?state'')"
    proof
      fix ul
      assume "ul \<in> ?ulSet"
      then obtain uc
        where "uc el (getF state)" "opposite literal el uc" "isUnitClause uc ul ((elements (getM state)) @ [literal])"
        by auto
      then obtain uci
        where "uc = (nth (getF state) uci)" "uci < length (getF state)"
        using set_conv_nth[of "getF state"]
        by auto
      let ?w1 = "getWatch1 state uci"
      let ?w2 = "getWatch2 state uci"

      have "?w1 = Some (opposite literal) \<or> ?w2 = Some (opposite literal)"
      proof-
        {
          assume "\<not> ?thesis"
          
          from `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)`
          obtain wl1 wl2
            where "?w1 = Some wl1" "?w2 = Some wl2" "wl1 el (getF state ! uci)" "wl2 el (getF state ! uci)"
            unfolding InvariantWatchesEl_def
            using `uci < length (getF state)`
            by force

          with `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)`
          have "watchCharacterizationCondition wl1 wl2 (getM state) (getF state ! uci)"
               "watchCharacterizationCondition wl2 wl1 (getM state) (getF state ! uci)"
            using `uci < length (getF state)`
            unfolding InvariantWatchCharacterization_def
            by auto

          from `isUnitClause uc ul ((elements (getM state)) @ [literal])`
          have "\<not> (\<exists> l. l el uc \<and> (literalTrue l ((elements (getM state)) @ [literal])))"
            using containsTrueNotUnit
            using `InvariantConsistent ((getM state) @ [(literal, decision)])`
            unfolding InvariantConsistent_def
            by auto
          
          from `InvariantUniq ((getM state) @ [(literal, decision)])`
          have "\<not> literal el (elements (getM state))"
            unfolding InvariantUniq_def
            by (simp add: uniqAppendIff)
        
          from `\<not> ?thesis` 
            `?w1 = Some wl1` `?w2 = Some wl2`
          have "wl1 \<noteq> opposite literal" "wl2 \<noteq> opposite literal"
            by auto

          from `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
          have "wl1 \<noteq> wl2"
            using `?w1 = Some wl1` `?w2 = Some wl2`
            unfolding InvariantWatchesDiffer_def
            using `uci < length (getF state)`
            by auto
          
          have "literalFalse wl1 (elements (getM state)) \<or> literalFalse wl2 (elements (getM state))"
          proof (cases "ul = wl1")
            case True
            with `wl1 \<noteq> wl2`
            have "ul \<noteq> wl2"
              by simp
            with `isUnitClause uc ul ((elements (getM state)) @ [literal])`
              `wl2 \<noteq> opposite literal` `wl2 el (getF state ! uci)`
              `uc = (getF state ! uci)`
            show ?thesis
              unfolding isUnitClause_def
              by auto
          next
            case False
            with `isUnitClause uc ul ((elements (getM state)) @ [literal])`
              `wl1 \<noteq> opposite literal` `wl1 el (getF state ! uci)`
              `uc = (getF state ! uci)`
            show ?thesis
              unfolding isUnitClause_def
              by auto
          qed

          with  `watchCharacterizationCondition wl1 wl2 (getM state) (getF state ! uci)`
            `watchCharacterizationCondition wl2 wl1 (getM state) (getF state ! uci)`
            `\<not> (\<exists> l. l el uc \<and> (literalTrue l ((elements (getM state)) @ [literal])))`
            `uc = (getF state ! uci)`
            `?w1 = Some wl1` `?w2 = Some wl2`
          have "\<forall> l. l el uc \<and> l \<noteq> wl1 \<and> l \<noteq> wl2 \<longrightarrow> literalFalse l (elements (getM state))"
            unfolding watchCharacterizationCondition_def
            by auto
          with `wl1 \<noteq> opposite literal` `wl2 \<noteq> opposite literal` `opposite literal el uc`
          have "literalTrue literal (elements (getM state))"
            by auto
          with `\<not> literal el (elements (getM state))`
          have False
            by simp
        } thus ?thesis
          by auto
      qed
      with `InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)`
      have "uci \<in> set (getWatchList state (opposite literal))"
        unfolding InvariantWatchListsCharacterization_def
        by auto

      thus "ul \<in> set (getQ ?state'')"
        using `uc el (getF state)` 
        using `isUnitClause uc ul ((elements (getM state)) @ [literal])`
        using `uc = (getF state ! uci)`
        unfolding assertLiteral_def
        unfolding notifyWatches_def
        using assms
        using NotifyWatchesLoopQEffect[of "?state'" "getM state" "opposite literal" "decision" "getWatchList ?state' (opposite literal)" "[]"]
        unfolding InvariantWatchListsCharacterization_def
        unfolding InvariantWatchListsUniq_def
        unfolding InvariantWatchListsContainOnlyClausesFromF_def
        by (auto simp add: Let_def)
    qed
    moreover
    have "set (getQ state) \<subseteq> set (getQ ?state'')"
      using assms
      using assertLiteralEffect[of "state" "literal" "decision"]
      using prefixIsSubset[of "getQ state" "getQ ?state''"]
      by simp
    ultimately
    show ?thesis
      by (auto simp add: Let_def)
qed


lemma InvariantQCharacterizationAfterAssertLiteral:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
shows
  "let state' = (assertLiteral literal decision state) in
      InvariantQCharacterization (getConflictFlag state') (removeAll literal (getQ state')) (getF state') (getM state')"
proof-
  let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
  let ?state' = "assertLiteral literal decision state"

  have *:"\<forall>l. l \<in> set (getQ ?state') - set (getQ ?state) \<longrightarrow>
            (\<exists>clause. clause el (getF ?state) \<and> isUnitClause clause l (elements (getM ?state)))"
    using NotifyWatchesLoopQEffect[of "?state" "getM state" "opposite literal" "decision"   "getWatchList ?state (opposite literal)" "[]"]
    using assms
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchCharacterization_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (auto simp add: Let_def)

  have **: "\<forall> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<longrightarrow> 
              (\<forall> l. (isUnitClause (nth (getF ?state) clause) l (elements (getM ?state))) \<longrightarrow> 
                      l \<in> (set (getQ ?state')))"
    using NotifyWatchesLoopQEffect[of "?state" "getM state" "opposite literal" "decision" "getWatchList ?state (opposite literal)" "[]"]
    using assms
    unfolding InvariantWatchListsUniq_def
    unfolding InvariantWatchListsCharacterization_def
    unfolding InvariantWatchListsContainOnlyClausesFromF_def
    unfolding InvariantWatchCharacterization_def
    unfolding assertLiteral_def
    unfolding notifyWatches_def
    by (simp add: Let_def)

  have "getConflictFlag state \<longrightarrow> getConflictFlag ?state'"
  proof-
    have "getConflictFlag ?state' = (getConflictFlag state \<or> 
            (\<exists> clause. clause \<in> set (getWatchList ?state (opposite literal)) \<and> 
                       clauseFalse (nth (getF ?state) clause) (elements (getM ?state))))"
      using NotifyWatchesLoopConflictFlagEffect[of "?state" 
        "getWatchList ?state (opposite literal)"
        "opposite literal" "[]"]
      using assms
      unfolding InvariantWatchListsUniq_def
      unfolding InvariantWatchListsCharacterization_def
      unfolding InvariantWatchListsContainOnlyClausesFromF_def
      unfolding assertLiteral_def
      unfolding notifyWatches_def
      by (simp add: Let_def)
    thus ?thesis
      by simp
  qed

  {
    assume "\<not> getConflictFlag ?state'"
    with `getConflictFlag state \<longrightarrow> getConflictFlag ?state'`
    have "\<not> getConflictFlag state"
      by simp

    have "\<forall>l. l el (removeAll literal (getQ ?state')) =
             (\<exists>c. c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state')))"
    proof
      fix l::Literal
      show "l el (removeAll literal (getQ ?state')) =
             (\<exists>c. c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state')))"
      proof
        assume "l el (removeAll literal (getQ ?state'))"
        hence "l el (getQ ?state')" "l \<noteq> literal"
          by auto
        show "\<exists>c. c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state'))"
        proof (cases "l el (getQ state)")
          case True
        
          from `\<not> getConflictFlag state`
            `InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)`
            `l el (getQ state)`
          obtain c::Clause
            where "c el (getF state)" "isUnitClause c l (elements (getM state))"
            unfolding InvariantQCharacterization_def
            by auto

          show ?thesis
          proof (cases "l \<noteq> opposite literal")
            case True
            hence "opposite l \<noteq> literal"
              by auto
            
            from `isUnitClause c l (elements (getM state))`
              `opposite l \<noteq> literal` `l \<noteq> literal`
            have "isUnitClause c l ((elements (getM state) @ [literal]))"
              using isUnitClauseAppendValuation[of "c" "l" "elements (getM state)" "literal"]
              by simp
            thus ?thesis
              using assms
              using `c el (getF state)`
              using assertLiteralEffect[of "state" "literal" "decision"]
              by auto
          next
            case False
            hence "opposite l = literal"
              by simp

            from `isUnitClause c l (elements (getM state))`
            have "clauseFalse c (elements (getM ?state'))"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              using unitBecomesFalse[of "c" "l" "elements (getM state)"]
              using `opposite l = literal`
              by simp
            with `c el (getF state)`
            have "formulaFalse (getF state) (elements (getM ?state'))"
              by (auto simp add: formulaFalseIffContainsFalseClause)
                
            from assms
            have "InvariantConflictFlagCharacterization (getConflictFlag ?state') (getF ?state') (getM ?state')"
              using InvariantConflictFlagCharacterizationAfterAssertLiteral
              by (simp add: Let_def)
            with `formulaFalse (getF state) (elements (getM ?state'))`
            have "getConflictFlag ?state'"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              unfolding InvariantConflictFlagCharacterization_def
              by auto
            with `\<not> getConflictFlag ?state'`
            show ?thesis
              by simp
          qed
        next
          case False
          then obtain c::Clause
            where "c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state'))"
            using *
            using `l el (getQ ?state')`
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            by auto
          thus ?thesis
            using formulaEntailsItsClauses[of "c" "getF ?state'"]
            by auto
          qed
      next
        assume "\<exists>c. c el (getF ?state') \<and> isUnitClause c l (elements (getM ?state'))"
        then obtain c::Clause
          where "c el (getF ?state')" "isUnitClause c l (elements (getM ?state'))"
          by auto
        then obtain ci::nat
          where "0 \<le> ci" "ci < length (getF ?state')" "c = (nth (getF ?state') ci)"
          using set_conv_nth[of "getF ?state'"]
          by auto
        then obtain w1::Literal and w2::Literal
          where "getWatch1 state ci = Some w1" and "getWatch2 state ci = Some w2" and 
          "w1 el c" and "w2 el c"
          using `InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)` 
          using `c = (nth (getF ?state') ci)`
          unfolding InvariantWatchesEl_def
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          by auto
        hence "w1 \<noteq> w2"
          using `ci < length (getF ?state')`
          using `InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)`
          unfolding InvariantWatchesDiffer_def
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          by auto

        show "l el (removeAll literal (getQ ?state'))"
        proof (cases "isUnitClause c l (elements (getM state))")
          case True
          with `InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)`
            `\<not> getConflictFlag state`
            `c el (getF ?state')` 
          have "l el (getQ state)"
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            unfolding InvariantQCharacterization_def
            by auto
          have "isPrefix (getQ state) (getQ ?state')"
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            by simp
          then obtain Q' 
            where "(getQ state) @ Q' = (getQ ?state')"
            unfolding isPrefix_def
            by auto
          have "l el (getQ ?state')"
            using `l el (getQ state)`
            `(getQ state) @ Q' = (getQ ?state')`[THEN sym]
            by simp
          moreover
          have "l \<noteq> literal"
            using `isUnitClause c l (elements (getM ?state'))`
            using assms
            using assertLiteralEffect[of "state" "literal" "decision"]
            unfolding isUnitClause_def
            by simp
          ultimately
          show ?thesis
            by auto
        next
          case False
            (* The clause was not unit in M but it became unit in M' *)
          thus ?thesis
          proof (cases "ci \<in> set (getWatchList ?state (opposite literal))")
            case True
            with ** 
              `isUnitClause c l (elements (getM ?state'))`
              `c = (nth (getF ?state') ci)`
            have "l \<in> set (getQ ?state')"
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              by simp
            moreover
            have "l \<noteq> literal"
              using `isUnitClause c l (elements (getM ?state'))`
              unfolding isUnitClause_def
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              by simp
            ultimately
            show ?thesis
              by simp
          next
            case False
            with `InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)`
            have "w1 \<noteq> opposite literal" "w2 \<noteq> opposite literal"
              using `getWatch1 state ci = Some w1` and `getWatch2 state ci = Some w2`
              unfolding InvariantWatchListsCharacterization_def
              by auto
            have "literalFalse w1 (elements (getM state)) \<or> literalFalse w2 (elements (getM state))"
            proof-
              {
                assume "\<not> ?thesis"
                hence "\<not> literalFalse w1 (elements (getM ?state'))" "\<not> literalFalse w2 (elements (getM ?state'))"
                  using `w1 \<noteq> opposite literal` and `w2 \<noteq> opposite literal`
                  using assms
                  using assertLiteralEffect[of "state" "literal" "decision"]
                  by auto
                with `w1 \<noteq> w2` `w1 el c` `w2 el c`
                have  "\<not> isUnitClause c l (elements (getM ?state'))"
                  unfolding isUnitClause_def
                  by auto
              }
              with `isUnitClause c l (elements (getM ?state'))`
              show ?thesis
                by auto
            qed
                (* Depends on the watch characterization invariant *)
            with `InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)`
            have $: "(\<exists> l. l el c \<and> literalTrue l (elements (getM state))) \<or> 
                     (\<forall> l. l el c \<and> 
                         l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state)))
              "
              using `ci < length (getF ?state')`
              using `c = (nth (getF ?state') ci)`
              using `getWatch1 state ci = Some w1`[THEN sym] and `getWatch2 state ci = Some w2`[THEN sym]
              using assms
              using assertLiteralEffect[of "state" "literal" "decision"]
              unfolding InvariantWatchCharacterization_def
              unfolding watchCharacterizationCondition_def
              by auto
            thus ?thesis
            proof(cases "\<forall> l. l el c \<and> l \<noteq> w1 \<and> l \<noteq> w2 \<longrightarrow> literalFalse l (elements (getM state))")
              case True
              with `isUnitClause c l (elements (getM ?state'))`
              have "literalFalse w1 (elements (getM state)) \<longrightarrow> 
                      \<not> literalFalse w2 (elements (getM state)) \<and> \<not> literalTrue w2 (elements (getM state)) \<and> l = w2"
                   "literalFalse w2 (elements (getM state)) \<longrightarrow> 
                      \<not> literalFalse w1 (elements (getM state)) \<and> \<not> literalTrue w1 (elements (getM state)) \<and> l = w1"
                unfolding isUnitClause_def
                using assms
                using assertLiteralEffect[of "state" "literal" "decision"]
                by auto
              
              with `literalFalse w1 (elements (getM state)) \<or> literalFalse w2 (elements (getM state))`
              have "(literalFalse w1 (elements (getM state)) \<and> \<not> literalFalse w2 (elements (getM state)) \<and> \<not> literalTrue w2 (elements (getM state)) \<and> l = w2) \<or> 
                    (literalFalse w2 (elements (getM state)) \<and> \<not> literalFalse w1 (elements (getM state)) \<and> \<not> literalTrue w1 (elements (getM state)) \<and> l = w1)"
                by blast
              hence "isUnitClause c l (elements (getM state))"
                using `w1 el c` `w2 el c` True
                unfolding isUnitClause_def
                by auto
              thus ?thesis
                using `\<not> isUnitClause c l (elements (getM state))`
                by simp
            next
              case False
              then obtain l'::Literal where 
                "l' el c" "literalTrue l' (elements (getM state))"
                using $
                by auto
              hence "literalTrue l' (elements (getM ?state'))"
                using assms
                using assertLiteralEffect[of "state" "literal" "decision"]
                by auto
              
              from `InvariantConsistent ((getM state) @ [(literal, decision)])`
                `l' el c` `literalTrue l' (elements (getM ?state'))`
              show ?thesis
                using containsTrueNotUnit[of "l'" "c" "elements (getM ?state')"]
                using `isUnitClause c l (elements (getM ?state'))`
                using assms
                using assertLiteralEffect[of "state" "literal" "decision"]
                unfolding InvariantConsistent_def
                by auto
            qed
          qed
        qed
      qed
    qed
  }
  thus ?thesis
    unfolding InvariantQCharacterization_def
    by simp
qed

lemma AssertLiteralStartQIreleveant:
fixes literal :: Literal and Wl :: "nat list" and newWl :: "nat list" and state :: State 
assumes 
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and 
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
shows
  "let state' = (assertLiteral literal decision (state\<lparr> getQ := Q' \<rparr>)) in
   let state'' = (assertLiteral literal decision (state\<lparr> getQ := Q'' \<rparr>)) in
   (getM state') = (getM state'') \<and> 
   (getF state') = (getF state'') \<and> 
   (getSATFlag state') = (getSATFlag state'') \<and> 
   (getConflictFlag state') = (getConflictFlag state'')
  " 
using assms
unfolding assertLiteral_def
unfolding notifyWatches_def
unfolding InvariantWatchListsContainOnlyClausesFromF_def
using notifyWatchesStartQIreleveant[of 
"state\<lparr> getQ := Q', getM := getM state @ [(literal, decision)] \<rparr>"
"getWatchList (state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>) (opposite literal)" 
"state\<lparr> getQ := Q'', getM := getM state @ [(literal, decision)] \<rparr>" 
"opposite literal" "[]"]
by (simp add: Let_def)

lemma assertedLiteralIsNotUnit:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
shows
  "let state' = assertLiteral literal decision state in
      \<not> literal \<in> (set (getQ state') - set(getQ state))"
proof-
  {
    let ?state = "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
    let ?state' = "assertLiteral literal decision state"

    assume "\<not> ?thesis"
    
    have *:"\<forall>l. l \<in> set (getQ ?state') - set (getQ ?state) \<longrightarrow>
            (\<exists>clause. clause el (getF ?state) \<and> isUnitClause clause l (elements (getM ?state)))"
      using NotifyWatchesLoopQEffect[of "?state" "getM state" "opposite literal" "decision"   "getWatchList ?state (opposite literal)" "[]"]
      using assms
      unfolding InvariantWatchListsUniq_def
      unfolding InvariantWatchListsCharacterization_def
      unfolding InvariantWatchListsContainOnlyClausesFromF_def
      unfolding InvariantWatchCharacterization_def
      unfolding assertLiteral_def
      unfolding notifyWatches_def
      by (auto simp add: Let_def)
    with `\<not> ?thesis`
    obtain clause
      where "isUnitClause clause literal (elements (getM ?state))"
      by (auto simp add: Let_def)
    hence "False"
      unfolding isUnitClause_def
      by simp
  }
  thus ?thesis
    by auto
qed

lemma InvariantQCharacterizationAfterAssertLiteralNotInQ:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchListsUniq (getWatchList state)" and
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "\<not> literal el (getQ state)"
shows
  "let state' = (assertLiteral literal decision state) in
      InvariantQCharacterization (getConflictFlag state') (getQ state') (getF state') (getM state')"
proof-
  let ?state' = "assertLiteral literal decision state"
  have "InvariantQCharacterization (getConflictFlag ?state') (removeAll literal (getQ ?state')) (getF ?state') (getM ?state')"
    using assms
    using InvariantQCharacterizationAfterAssertLiteral
    by (simp add: Let_def)
  moreover
  have "\<not> literal el (getQ ?state')"
    using assms
    using assertedLiteralIsNotUnit[of "state" "literal" "decision"]
    by (simp add: Let_def)
  hence "removeAll literal (getQ ?state') = getQ ?state'"
    using removeAll_id[of "literal" "getQ ?state'"]
    by simp
  ultimately
  show ?thesis
    by (simp add: Let_def)
qed

lemma InvariantUniqQAfterAssertLiteral:
assumes
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantUniqQ (getQ state)"
shows
  "let state' = assertLiteral literal decision state in
      InvariantUniqQ (getQ state')"
using assms
using InvariantUniqQAfterNotifyWatchesLoop[of "state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>"
"getWatchList (state\<lparr>getM := getM state @ [(literal, decision)]\<rparr>) (opposite literal)"
"opposite literal" "[]"]
unfolding assertLiteral_def
unfolding notifyWatches_def
unfolding InvariantWatchListsContainOnlyClausesFromF_def  
by (auto simp add: Let_def)

lemma InvariantsNoDecisionsWhenConflictNorUnitAfterAssertLiteral:
assumes
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)" and
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)" and
  "InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)"
  "InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)"
  "InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))"
  "InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))"
  "decision \<longrightarrow> \<not> (getConflictFlag state) \<and> (getQ state) = []"
shows
  "let state' = assertLiteral literal decision state in
       InvariantNoDecisionsWhenConflict (getF state') (getM state') (currentLevel (getM state')) \<and> 
       InvariantNoDecisionsWhenUnit (getF state') (getM state') (currentLevel (getM state'))"
proof-
  {
    let ?state' = "assertLiteral literal decision state"
    fix level
    assume "level < currentLevel (getM ?state')"
    have "\<not> formulaFalse (getF ?state') (elements (prefixToLevel level (getM ?state'))) \<and> 
          \<not> (\<exists>clause literal. clause el (getF ?state') \<and>
                isUnitClause clause literal (elements (prefixToLevel level (getM ?state'))))" 
    proof (cases "level < currentLevel (getM state)")
      case True
      hence "prefixToLevel level (getM ?state') = prefixToLevel level (getM state)"
        using assms
        using assertLiteralEffect[of "state" "literal" "decision"]
        by (auto simp add: prefixToLevelAppend)
      moreover
      have "\<not> formulaFalse (getF state) (elements (prefixToLevel level (getM state)))"
        using `InvariantNoDecisionsWhenConflict (getF state) (getM state) (currentLevel (getM state))`
        using `level < currentLevel (getM state)`
        unfolding InvariantNoDecisionsWhenConflict_def
        by simp
      moreover
      have "\<not> (\<exists>clause literal. clause el (getF state) \<and> 
                isUnitClause clause literal (elements (prefixToLevel level (getM state))))"
        using `InvariantNoDecisionsWhenUnit (getF state) (getM state) (currentLevel (getM state))`
        using `level < currentLevel (getM state)`
        unfolding InvariantNoDecisionsWhenUnit_def
        by simp
      ultimately
      show ?thesis
        using assms
        using assertLiteralEffect[of "state" "literal" "decision"]
        by auto
    next
      case False
      thus ?thesis
      proof (cases "decision")
        case False
        hence "currentLevel (getM ?state') = currentLevel (getM state)"
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          unfolding currentLevel_def
          by (auto simp add: markedElementsAppend)
        thus ?thesis 
          using `\<not> (level < currentLevel (getM state))`
          using `level < currentLevel (getM ?state')`
          by simp
      next
        case True
        hence "currentLevel (getM ?state') = currentLevel (getM state) + 1"
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          unfolding currentLevel_def
          by (auto simp add: markedElementsAppend)
        hence "level = currentLevel (getM state)"
          using `\<not> (level < currentLevel (getM state))`
          using `level < currentLevel (getM ?state')`
          by simp
        hence "prefixToLevel level (getM ?state') = (getM state)"
          using `decision`
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          using prefixToLevelAppend[of "currentLevel (getM state)" "getM state" "[(literal, True)]"]
          by auto
        thus ?thesis
          using `decision`
          using `decision \<longrightarrow> \<not> (getConflictFlag state) \<and> (getQ state) = []`
          using `InvariantConflictFlagCharacterization (getConflictFlag state) (getF state) (getM state)`       
          using `InvariantQCharacterization (getConflictFlag state) (getQ state) (getF state) (getM state)`
          unfolding InvariantConflictFlagCharacterization_def
          unfolding InvariantQCharacterization_def
          using assms
          using assertLiteralEffect[of "state" "literal" "decision"]
          by simp
      qed
    qed
  } thus ?thesis
    unfolding InvariantNoDecisionsWhenConflict_def
    unfolding InvariantNoDecisionsWhenUnit_def
    by auto
qed



lemma InvariantVarsQAfterAssertLiteral:
assumes
  "InvariantConsistent ((getM state) @ [(literal, decision)])"
  "InvariantUniq ((getM state) @ [(literal, decision)])"
  "InvariantWatchListsContainOnlyClausesFromF (getWatchList state) (getF state)"
  "InvariantWatchListsUniq (getWatchList state)"
  "InvariantWatchListsCharacterization (getWatchList state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesEl (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchesDiffer (getF state) (getWatch1 state) (getWatch2 state)"
  "InvariantWatchCharacterization (getF state) (getWatch1 state) (getWatch2 state) (getM state)"  
  "InvariantVarsQ (getQ state) F0 Vbl"
  "InvariantVarsF (getF state) F0 Vbl"
shows  
  "let state' = assertLiteral literal decision state in
     InvariantVarsQ (getQ state') F0 Vbl"
proof-
  let ?Q' = "{ul. \<exists>uc. uc el (getF state) \<and>
                  (opposite literal) el uc \<and> isUnitClause uc ul (elements (getM state) @ [literal])}"
  let ?state' = "assertLiteral literal decision state"
  have "vars ?Q' \<subseteq> vars (getF state)"
  proof
    fix vbl::Variable
    assume "vbl \<in> vars ?Q'"
    then obtain ul::Literal
      where "ul \<in> ?Q'" "var ul = vbl"
      by auto
    then obtain uc::Clause
      where "uc el (getF state)"  "isUnitClause uc ul (elements (getM state) @ [literal])"
      by auto
    hence "vars uc \<subseteq> vars (getF state)" "var ul \<in> vars uc"
      using formulaContainsItsClausesVariables[of "uc" "getF state"]
      using clauseContainsItsLiteralsVariable[of "ul" "uc"]
      unfolding isUnitClause_def
      by auto
    thus "vbl \<in> vars (getF state)"
      using `var ul = vbl`
      by auto
  qed
  thus ?thesis
    using assms
    using assertLiteralQEffect[of "state" "literal" "decision"]
    using varsClauseVarsSet[of "getQ ?state'"]
    using varsClauseVarsSet[of "getQ state"]
    unfolding InvariantVarsQ_def
    unfolding InvariantVarsF_def
    by (auto simp add: Let_def)
qed

end