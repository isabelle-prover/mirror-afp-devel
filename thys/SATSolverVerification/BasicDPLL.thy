(*    Title:              SatSolverVerification/BasicDPLL.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

section{* BasicDPLL *}
theory BasicDPLL
imports SatSolverVerification
begin

text{* This theory formalizes the transition rule system BasicDPLL
 which is based on the classical DPLL procedure, but does not use the
 PureLiteral rule. *}

(******************************************************************************)
subsection{* Specification *}
(******************************************************************************)

text{* The state of the procedure is uniquely determined by its trail. *}
record State = 
"getM" :: LiteralTrail

text{* Procedure checks the satisfiability of the formula F0 which
  does not change during the solving process. An external parameter is
  the set @{term decisionVars} which are the variables that branching
  is performed on. Usually this set contains all variables of the
  formula F0, but that does not always have to be the case. *}


text{* Now we define the transition rules of the system *}
definition
appliedDecide:: "State \<Rightarrow> State \<Rightarrow> Variable set \<Rightarrow> bool"
where
"appliedDecide stateA stateB decisionVars == 
  \<exists> l. 
        (var l) \<in> decisionVars \<and> 
        \<not> l el (elements (getM stateA)) \<and> 
        \<not> opposite l el (elements (getM stateA)) \<and>

        getM stateB = getM stateA @ [(l, True)]
"
definition
applicableDecide :: "State \<Rightarrow> Variable set \<Rightarrow> bool"
where
"applicableDecide state decisionVars == \<exists> state'. appliedDecide state state' decisionVars"

definition
appliedUnitPropagate :: "State \<Rightarrow> State \<Rightarrow> Formula \<Rightarrow> bool"
where
"appliedUnitPropagate stateA stateB F0 == 
  \<exists> (uc::Clause) (ul::Literal). 
       uc el F0 \<and> 
       isUnitClause uc ul (elements (getM stateA)) \<and> 

       getM stateB = getM stateA @ [(ul, False)]
"
definition
applicableUnitPropagate :: "State \<Rightarrow> Formula \<Rightarrow> bool"
where
"applicableUnitPropagate state F0 == \<exists> state'. appliedUnitPropagate state state' F0"

definition
appliedBacktrack :: "State \<Rightarrow> State \<Rightarrow> Formula \<Rightarrow> bool"
where
"appliedBacktrack stateA stateB F0 == 
      formulaFalse F0 (elements (getM stateA)) \<and> 
      decisions (getM stateA) \<noteq> [] \<and> 

      getM stateB = prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]
"
definition
applicableBacktrack :: "State \<Rightarrow> Formula \<Rightarrow> bool"
where
"applicableBacktrack state F0 ==  \<exists> state'. appliedBacktrack state state' F0"


text{* Solving starts with the empty trail. *}
definition
isInitialState :: "State \<Rightarrow> Formula \<Rightarrow> bool"
where
"isInitialState state F0 == 
      getM state = []
"
text{* Transitions are preformed only by using one of the three given rules. *}
definition
"transition stateA stateB F0 decisionVars == 
     appliedDecide        stateA stateB decisionVars \<or>
     appliedUnitPropagate stateA stateB F0  \<or> 
     appliedBacktrack     stateA stateB F0
"

text{* Transition relation is obtained by applying transition rules
iteratively. It is defined using a reflexive-transitive closure. *}
definition
"transitionRelation F0 decisionVars == ({(stateA, stateB). transition stateA stateB F0 decisionVars})^*"

text{* Final state is one in which no rules apply *}
definition
isFinalState :: "State \<Rightarrow> Formula \<Rightarrow> Variable set \<Rightarrow> bool"
where
"isFinalState state F0 decisionVars == \<not> (\<exists> state'. transition state state' F0 decisionVars)"

text{* The following several lemmas give conditions for applicability of different rules. *}
lemma applicableDecideCharacterization:
  fixes stateA::State
  shows "applicableDecide stateA decisionVars = 
  (\<exists> l. 
        (var l) \<in> decisionVars \<and> 
        \<not> l el (elements (getM stateA)) \<and> 
        \<not> opposite l el (elements (getM stateA))) 
  " (is "?lhs = ?rhs")
proof
  assume ?rhs
  then obtain l where 
    *: "(var l) \<in> decisionVars" "\<not> l el (elements (getM stateA))" "\<not> opposite l el (elements (getM stateA))"
    unfolding applicableDecide_def
    by auto
  let ?stateB = "stateA\<lparr> getM := (getM stateA) @ [(l, True)] \<rparr>"
  from * have "appliedDecide stateA ?stateB decisionVars"
    unfolding appliedDecide_def
    by auto
  thus ?lhs
    unfolding applicableDecide_def
    by auto
next
  assume ?lhs
  then obtain stateB l
    where "(var l) \<in> decisionVars" "\<not> l el (elements (getM stateA))"
    "\<not> opposite l el (elements (getM stateA))"
    unfolding applicableDecide_def
    unfolding appliedDecide_def
    by auto
  thus ?rhs
    by auto
qed

lemma applicableUnitPropagateCharacterization:
  fixes stateA::State and F0::Formula
  shows "applicableUnitPropagate stateA F0 = 
  (\<exists> (uc::Clause) (ul::Literal). 
       uc el F0 \<and> 
       isUnitClause uc ul (elements (getM stateA)))
  " (is "?lhs = ?rhs")
proof
  assume "?rhs"
  then obtain ul uc 
    where *: "uc el F0" "isUnitClause uc ul (elements (getM stateA))"
    unfolding applicableUnitPropagate_def
    by auto
  let ?stateB = "stateA\<lparr> getM := getM stateA @ [(ul, False)] \<rparr>"
  from * have "appliedUnitPropagate stateA ?stateB F0" 
    unfolding appliedUnitPropagate_def
    by auto
  thus ?lhs
    unfolding applicableUnitPropagate_def
    by auto
next
  assume ?lhs
  then obtain stateB uc ul
    where "uc el F0" "isUnitClause uc ul (elements (getM stateA))"
    unfolding applicableUnitPropagate_def
    unfolding appliedUnitPropagate_def
    by auto
  thus ?rhs
    by auto
qed

lemma applicableBacktrackCharacterization:
  fixes stateA::State
  shows "applicableBacktrack stateA F0 = 
      (formulaFalse F0 (elements (getM stateA)) \<and> 
       decisions (getM stateA) \<noteq> [])" (is "?lhs = ?rhs")
proof
  assume ?rhs
  hence *: "formulaFalse F0 (elements (getM stateA))" "decisions (getM stateA) \<noteq> []"
    by auto
  let ?stateB = "stateA\<lparr> getM := prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]\<rparr>"
  from * have "appliedBacktrack stateA ?stateB F0"
    unfolding appliedBacktrack_def
    by auto
  thus ?lhs
    unfolding applicableBacktrack_def
    by auto
next
  assume "?lhs"
  then obtain stateB 
    where "appliedBacktrack stateA stateB F0"
    unfolding applicableBacktrack_def
    by auto
  hence 
    "formulaFalse F0 (elements (getM stateA))"
    "decisions (getM stateA) \<noteq> []"
    "getM stateB = prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]"
    unfolding appliedBacktrack_def
    by auto
  thus ?rhs
    by auto
qed

text{* Final states are the ones where no rule is applicable. *}
lemma finalStateNonApplicable: 
  fixes state::State
  shows "isFinalState state F0 decisionVars = 
          (\<not> applicableDecide state decisionVars \<and> 
           \<not> applicableUnitPropagate state F0 \<and> 
           \<not> applicableBacktrack state F0)"
unfolding isFinalState_def
unfolding transition_def
unfolding applicableDecide_def
unfolding applicableUnitPropagate_def
unfolding applicableBacktrack_def
by auto
  
(******************************************************************************)
subsection{* Invariants *}
(******************************************************************************)
text{* Invariants that are relevant for the rest of correctness proof. *}
definition
invariantsHoldInState :: "State \<Rightarrow> Formula \<Rightarrow> Variable set \<Rightarrow> bool"
where
"invariantsHoldInState state F0 decisionVars == 
    InvariantImpliedLiterals F0 (getM state) \<and>
    InvariantVarsM (getM state) F0 decisionVars \<and>
    InvariantConsistent (getM state) \<and>
    InvariantUniq (getM state)
"

text{* Invariants hold in initial states. *}
lemma invariantsHoldInInitialState:
  fixes state :: State and F0 :: Formula
  assumes "isInitialState state F0" 
  shows "invariantsHoldInState state F0 decisionVars"
using assms
by (auto simp add:
  isInitialState_def 
  invariantsHoldInState_def 
  InvariantImpliedLiterals_def 
  InvariantVarsM_def
  InvariantConsistent_def
  InvariantUniq_def
)

text{* Valid transitions preserve invariants. *}
lemma transitionsPreserveInvariants: 
  fixes stateA::State and stateB::State
  assumes "transition stateA stateB F0 decisionVars" and 
  "invariantsHoldInState stateA F0 decisionVars"
  shows "invariantsHoldInState stateB F0 decisionVars"
proof-
    from `invariantsHoldInState stateA F0 decisionVars`
    have 
      "InvariantImpliedLiterals F0 (getM stateA)" and 
      "InvariantVarsM (getM stateA) F0 decisionVars" and
      "InvariantConsistent (getM stateA)" and
      "InvariantUniq (getM stateA)"
      unfolding invariantsHoldInState_def
      by auto
  {
    assume "appliedDecide stateA stateB decisionVars"
    then obtain l::Literal where
      "(var l) \<in> decisionVars"
      "\<not> literalTrue l (elements (getM stateA))"
      "\<not> literalFalse l (elements (getM stateA))"
      "getM stateB = getM stateA @ [(l, True)]"
      unfolding appliedDecide_def
      by auto

    from `\<not> literalTrue l (elements (getM stateA))` `\<not> literalFalse l (elements (getM stateA))` 
    have *: "var l \<notin> vars (elements (getM stateA))"
      using variableDefinedImpliesLiteralDefined[of "l" "elements (getM stateA)"]
      by simp

    have "InvariantImpliedLiterals F0 (getM stateB)"
      using 
        `getM stateB = getM stateA @ [(l, True)]` 
        `InvariantImpliedLiterals F0 (getM stateA)`
        `InvariantUniq (getM stateA)`
        `var l \<notin> vars (elements (getM stateA))`
        InvariantImpliedLiteralsAfterDecide[of "F0" "getM stateA" "l" "getM stateB"]
      by simp
    moreover
    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using `getM stateB = getM stateA @ [(l, True)]` 
        `InvariantVarsM (getM stateA) F0 decisionVars`
        `var l \<in> decisionVars`
        InvariantVarsMAfterDecide[of "getM stateA" "F0" "decisionVars" "l" "getM stateB"]
      by simp
    moreover 
    have "InvariantConsistent (getM stateB)"
      using `getM stateB = getM stateA @ [(l, True)]` 
        `InvariantConsistent (getM stateA)`
        `var l \<notin> vars (elements (getM stateA))`
        InvariantConsistentAfterDecide[of "getM stateA" "l" "getM stateB"]
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using `getM stateB = getM stateA @ [(l, True)]` 
        `InvariantUniq (getM stateA)`
        `var l \<notin> vars (elements (getM stateA))`
        InvariantUniqAfterDecide[of "getM stateA" "l" "getM stateB"]
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  moreover
  {
    assume "appliedUnitPropagate stateA stateB F0"
    then obtain uc::Clause and ul::Literal where 
      "uc el F0"
      "isUnitClause uc ul (elements (getM stateA))"
      "getM stateB = getM stateA @ [(ul, False)]"
      unfolding appliedUnitPropagate_def
      by auto

    from `isUnitClause uc ul (elements (getM stateA))`
    have "ul el uc"
      unfolding isUnitClause_def
      by simp

    from `uc el F0`
    have "formulaEntailsClause F0 uc"
      by (simp add: formulaEntailsItsClauses)
    
    have "InvariantImpliedLiterals F0 (getM stateB)"
      using
        `InvariantImpliedLiterals F0 (getM stateA)` 
        `formulaEntailsClause F0 uc`
        `isUnitClause uc ul (elements (getM stateA))`
        `getM stateB = getM stateA @ [(ul, False)]`
        InvariantImpliedLiteralsAfterUnitPropagate[of "F0" "getM stateA" "uc" "ul" "getM stateB"]
      by simp
    moreover
    from `ul el uc` `uc el F0`
    have "ul el F0"
      by (auto simp add: literalElFormulaCharacterization)
    hence "var ul \<in> vars F0 \<union> decisionVars"
      using formulaContainsItsLiteralsVariable [of "ul" "F0"]
      by auto

    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using `InvariantVarsM (getM stateA) F0 decisionVars`
        `var ul \<in> vars F0 \<union> decisionVars`
        `getM stateB = getM stateA @ [(ul, False)]`
        InvariantVarsMAfterUnitPropagate[of "getM stateA" "F0" "decisionVars" "ul" "getM stateB"]
      by simp
    moreover
    have "InvariantConsistent (getM stateB)"
      using `InvariantConsistent (getM stateA)`
        `isUnitClause uc ul (elements (getM stateA))`
        `getM stateB = getM stateA @ [(ul, False)]`
        InvariantConsistentAfterUnitPropagate [of "getM stateA" "uc" "ul" "getM stateB"]
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using `InvariantUniq (getM stateA)`
        `isUnitClause uc ul (elements (getM stateA))`
        `getM stateB = getM stateA @ [(ul, False)]`
        InvariantUniqAfterUnitPropagate [of "getM stateA" "uc" "ul" "getM stateB"]
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  moreover
  {
    assume "appliedBacktrack stateA stateB F0"
    hence "formulaFalse F0 (elements (getM stateA))" 
      "formulaFalse F0 (elements (getM stateA))"
      "decisions (getM stateA) \<noteq> []"
      "getM stateB = prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]"
      unfolding appliedBacktrack_def
      by auto      

    have "InvariantImpliedLiterals F0 (getM stateB)"
      using `InvariantImpliedLiterals F0 (getM stateA)`
        `formulaFalse F0 (elements (getM stateA))`
        `decisions (getM stateA) \<noteq> []`
        `getM stateB = prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]`
        `InvariantUniq (getM stateA)`
        `InvariantConsistent (getM stateA)`
        InvariantImpliedLiteralsAfterBacktrack[of "F0" "getM stateA" "getM stateB"]
      by simp
    moreover
    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using `InvariantVarsM (getM stateA) F0 decisionVars`
        `decisions (getM stateA) \<noteq> []`
        `getM stateB = prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]`
        InvariantVarsMAfterBacktrack[of "getM stateA" "F0" "decisionVars" "getM stateB"]
      by simp
    moreover
    have "InvariantConsistent (getM stateB)"
      using `InvariantConsistent (getM stateA)`
        `InvariantUniq (getM stateA)`
        `decisions (getM stateA) \<noteq> []`
        `getM stateB = prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]`
        InvariantConsistentAfterBacktrack[of "getM stateA" "getM stateB"]
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using `InvariantConsistent (getM stateA)`
        `InvariantUniq (getM stateA)`
        `decisions (getM stateA) \<noteq> []`
        `getM stateB = prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]`
        InvariantUniqAfterBacktrack[of "getM stateA" "getM stateB"]
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  ultimately
  show ?thesis
    using `transition stateA stateB F0 decisionVars`
    unfolding transition_def
    by auto
qed

text{* The consequence is that invariants hold in all valid runs. *}
lemma invariantsHoldInValidRuns: 
  fixes F0 :: Formula and decisionVars :: "Variable set"
  assumes "invariantsHoldInState stateA F0 decisionVars" and
  "(stateA, stateB) \<in> transitionRelation F0 decisionVars"
  shows "invariantsHoldInState stateB F0 decisionVars"
using assms
using transitionsPreserveInvariants
using rtrancl_induct[of "stateA" "stateB" 
  "{(stateA, stateB). transition stateA stateB F0 decisionVars}" "\<lambda> x. invariantsHoldInState x F0 decisionVars"]
unfolding transitionRelation_def
by auto

lemma invariantsHoldInValidRunsFromInitialState:
  fixes F0 :: Formula and decisionVars :: "Variable set"
  assumes "isInitialState state0 F0" 
  and "(state0, state) \<in> transitionRelation F0 decisionVars"
  shows "invariantsHoldInState state F0 decisionVars"
proof-
  from `isInitialState state0 F0`
  have "invariantsHoldInState state0 F0 decisionVars"
    by (simp add:invariantsHoldInInitialState)
  with assms
  show ?thesis
    using invariantsHoldInValidRuns [of "state0"  "F0" "decisionVars" "state"]
    by simp
qed

text{*
 In the following text we will show that there are two kinds of states:
 \begin{enumerate}
  \item \textit{UNSAT} states where @{term "formulaFalse F0 (elements (getM state))"}
  and @{term "decisions (getM state) = []"}. 
  \item \textit{SAT} states where @{term "\<not> formulaFalse F0 (elements (getM state))"}
  and @{term "vars (elements (getM state)) \<supseteq> decisionVars"}.
 \end{enumerate}
  
 The soundness theorems claim that if \textit{UNSAT} state is reached
 the formula is unsatisfiable and if \textit{SAT} state is reached,
 the formula is satisfiable.

 Completeness theorems claim that every final state is either
 \textit{UNSAT} or \textit{SAT}. A consequence of this and soundness
 theorems, is that if formula is unsatisfiable the solver will finish
 in an \textit{UNSAT} state, and if the formula is satisfiable the
 solver will finish in a \textit{SAT} state.  *}


(******************************************************************************)
subsection{* Soundness *}
(******************************************************************************)

(*----------------------------------------------------------------------------*)
theorem soundnessForUNSAT:
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes
  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars"

  "formulaFalse F0 (elements (getM state))"
  "decisions (getM state) = []"
  shows "\<not> satisfiable F0"
(*----------------------------------------------------------------------------*)
proof-
  from `isInitialState state0 F0` `(state0, state) \<in> transitionRelation F0 decisionVars`
  have "invariantsHoldInState state F0 decisionVars" 
    using invariantsHoldInValidRunsFromInitialState
    by simp
  hence "InvariantImpliedLiterals F0 (getM state)"
    unfolding invariantsHoldInState_def
    by auto
  with `formulaFalse F0 (elements (getM state))`
    `decisions (getM state) = []`
  show ?thesis
    using unsatReport[of "F0" "getM state" "F0"]
    unfolding InvariantEquivalent_def equivalentFormulae_def
    by simp
qed

(*----------------------------------------------------------------------------*)
theorem soundnessForSAT:
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes
  "vars F0 \<subseteq> decisionVars" and

  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars"

  "\<not> formulaFalse F0 (elements (getM state))"
  "vars (elements (getM state)) \<supseteq> decisionVars"  

  shows 
  "model (elements (getM state)) F0"
(*----------------------------------------------------------------------------*)
proof-
  from `isInitialState state0 F0` `(state0, state) \<in> transitionRelation F0 decisionVars`
  have "invariantsHoldInState state F0 decisionVars" 
    using invariantsHoldInValidRunsFromInitialState
    by simp
  hence 
    "InvariantConsistent (getM state)" 
    unfolding invariantsHoldInState_def
    by auto
  with assms
  show ?thesis
  using satReport[of "F0" "decisionVars" "F0" "getM state"]
  unfolding InvariantEquivalent_def equivalentFormulae_def
  InvariantVarsF_def
  by auto
qed


(******************************************************************************)
subsection{* Termination *}
(******************************************************************************)
text{* We now define a termination ordering on the set of states based
on the @{term lexLessRestricted} trail ordering. This ordering will be central
in termination proof. *}

definition "terminationLess (F0::Formula) decisionVars == {((stateA::State), (stateB::State)).
  (getM stateA, getM stateB) \<in> lexLessRestricted (vars F0 \<union> decisionVars)}"


text{* We want to show that every valid transition decreases a state
  with respect to the constructed termination ordering. Therefore, we
  show that $Decide$, $UnitPropagate$ and $Backtrack$ rule decrease the
  trail with respect to the restricted trail ordering. Invariants
  ensure that trails are indeed @{term uniq}, @{term consistent} and with 
  finite variable sets. *}
lemma trailIsDecreasedByDeciedUnitPropagateAndBacktrack:
  fixes stateA::State and stateB::State
  assumes "invariantsHoldInState stateA F0 decisionVars" and
  "appliedDecide stateA stateB decisionVars \<or> appliedUnitPropagate stateA stateB F0 \<or> appliedBacktrack stateA stateB F0"
  shows "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
proof-
  from `appliedDecide stateA stateB decisionVars \<or> appliedUnitPropagate stateA stateB F0 \<or> appliedBacktrack stateA stateB F0`
    `invariantsHoldInState stateA F0 decisionVars` 
  have "invariantsHoldInState stateB F0 decisionVars"
      using transitionsPreserveInvariants
      unfolding transition_def
      by auto
    from `invariantsHoldInState stateA F0 decisionVars` 
    have *: "uniq (elements (getM stateA))" "consistent (elements (getM stateA))" "vars (elements (getM stateA)) \<subseteq> vars F0 \<union> decisionVars"
      unfolding invariantsHoldInState_def
      unfolding InvariantVarsM_def
      unfolding InvariantConsistent_def
      unfolding InvariantUniq_def
      by auto
    from `invariantsHoldInState stateB F0 decisionVars` 
    have **: "uniq (elements (getM stateB))" "consistent (elements (getM stateB))" "vars (elements (getM stateB)) \<subseteq> vars F0 \<union> decisionVars"
      unfolding invariantsHoldInState_def
      unfolding InvariantVarsM_def
      unfolding InvariantConsistent_def
      unfolding InvariantUniq_def
      by auto
  {
    assume "appliedDecide stateA stateB decisionVars"
    hence "(getM stateB, getM stateA) \<in> lexLess"
      unfolding appliedDecide_def
      by (auto simp add:lexLessAppend)
    with * ** 
    have "((getM stateB), (getM stateA)) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
      unfolding lexLessRestricted_def
      by auto
  }
  moreover
  {
    assume "appliedUnitPropagate stateA stateB F0"
    hence "(getM stateB, getM stateA) \<in> lexLess"
      unfolding appliedUnitPropagate_def
      by (auto simp add:lexLessAppend)
    with * ** 
    have "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
      unfolding lexLessRestricted_def
      by auto
  }
  moreover
  {
    assume "appliedBacktrack stateA stateB F0"
    hence
      "formulaFalse F0 (elements (getM stateA))"
      "decisions (getM stateA) \<noteq> []"
      "getM stateB = prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]"
      unfolding appliedBacktrack_def
      by auto
    hence "(getM stateB, getM stateA) \<in> lexLess"
      using `decisions (getM stateA) \<noteq> []`
        `getM stateB = prefixBeforeLastDecision (getM stateA) @ [(opposite (lastDecision (getM stateA)), False)]`
      by (simp add:lexLessBacktrack)
    with * ** 
    have "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
      unfolding lexLessRestricted_def
      by auto
  }
  ultimately
  show ?thesis
    using assms
    by auto
qed

text{* Now we can show that every rule application decreases a state
with respect to the constructed termination ordering. *}
lemma stateIsDecreasedByValidTransitions:
  fixes stateA::State and stateB::State 
  assumes "invariantsHoldInState stateA F0 decisionVars" and "transition stateA stateB F0 decisionVars"
  shows "(stateB, stateA) \<in> terminationLess F0 decisionVars"
proof-
  from `transition stateA stateB F0 decisionVars`
  have "appliedDecide stateA stateB decisionVars \<or> appliedUnitPropagate stateA stateB F0 \<or> appliedBacktrack stateA stateB F0"
    unfolding transition_def
    by simp 
  with `invariantsHoldInState stateA F0 decisionVars`
  have "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
    using trailIsDecreasedByDeciedUnitPropagateAndBacktrack
    by simp
  thus ?thesis 
    unfolding terminationLess_def
    by simp
qed

text{* The minimal states with respect to the termination ordering are
  final i.e., no further transition rules are applicable. *}
definition 
"isMinimalState stateMin F0 decisionVars == (\<forall> state::State. (state, stateMin) \<notin> terminationLess F0 decisionVars)"

lemma minimalStatesAreFinal:
  fixes stateA::State
  assumes "invariantsHoldInState state F0 decisionVars" and "isMinimalState state F0 decisionVars"
  shows "isFinalState state F0 decisionVars"
proof-
  {
    assume "\<not> ?thesis"
    then obtain state'::State 
      where "transition state state' F0 decisionVars"
      unfolding isFinalState_def
      by auto
    with `invariantsHoldInState state F0 decisionVars` 
    have "(state', state) \<in> terminationLess F0 decisionVars"
      using stateIsDecreasedByValidTransitions[of "state" "F0" "decisionVars" "state'"]
      unfolding transition_def
      by auto
    with `isMinimalState state F0 decisionVars` 
    have False
      unfolding isMinimalState_def
      by auto
  }
  thus ?thesis
    by auto
qed

text{* The following key lemma shows that the termination ordering is well founded. *}
lemma wfTerminationLess: 
  fixes decisionVars :: "Variable set" and F0 :: "Formula"
  assumes "finite decisionVars"
  shows "wf (terminationLess F0 decisionVars)"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> terminationLess F0 decisionVars \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q :: "State set" and state :: State
      assume "state \<in> Q"
      let ?Q1 = "{M::LiteralTrail. \<exists> state. state \<in> Q \<and> (getM state) = M}"
      from `state \<in> Q`
      have "getM state \<in> ?Q1"
        by auto
      from `finite decisionVars` 
      have "finite (vars F0 \<union> decisionVars)"
        using finiteVarsFormula[of "F0"]
        by simp
      hence "wf (lexLessRestricted (vars F0 \<union> decisionVars))"
      using  wfLexLessRestricted[of "vars F0 \<union> decisionVars"]
      by simp
    with `getM state \<in> ?Q1`
      obtain Mmin where "Mmin \<in> ?Q1" "\<forall>M'. (M', Mmin) \<in> lexLessRestricted (vars F0 \<union> decisionVars) \<longrightarrow> M' \<notin> ?Q1"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q1" in allE)
        apply (erule_tac x="getM state" in allE)
        by auto 
      from `Mmin \<in> ?Q1` obtain stateMin
        where "stateMin \<in> Q" "(getM stateMin) = Mmin"
        by auto
      have "\<forall>state'. (state', stateMin) \<in> terminationLess F0 decisionVars \<longrightarrow> state' \<notin> Q"
      proof
        fix state'
        show "(state', stateMin) \<in> terminationLess F0 decisionVars \<longrightarrow> state' \<notin> Q"
        proof
          assume "(state', stateMin) \<in> terminationLess F0 decisionVars"
          hence "(getM state', getM stateMin) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
            unfolding terminationLess_def
            by auto
          from `\<forall>M'. (M', Mmin) \<in> lexLessRestricted (vars F0 \<union> decisionVars) \<longrightarrow> M' \<notin> ?Q1`
            `(getM state', getM stateMin) \<in> lexLessRestricted (vars F0 \<union> decisionVars)` `getM stateMin = Mmin`
          have "getM state' \<notin> ?Q1"
            by simp
          with `getM stateMin = Mmin`
          show "state' \<notin> Q"
            by auto
        qed
      qed
      with `stateMin \<in> Q`
      have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> terminationLess F0 decisionVars \<longrightarrow> state' \<notin> Q)"
        by auto
    }
    thus ?thesis
      by auto
  qed
qed

text{* Using the termination ordering we show that the transition
relation is well founded on states reachable from initial state. *}
(*----------------------------------------------------------------------------*)
theorem wfTransitionRelation:
  fixes decisionVars :: "Variable set" and F0 :: "Formula" and state0 :: "State"
  assumes "finite decisionVars" and "isInitialState state0 F0"
  shows "wf {(stateB, stateA). 
             (state0, stateA) \<in> transitionRelation F0 decisionVars \<and> (transition stateA stateB F0 decisionVars)}"
(*----------------------------------------------------------------------------*)
proof-
  let ?rel = "{(stateB, stateA). 
                  (state0, stateA) \<in> transitionRelation F0 decisionVars \<and> (transition stateA stateB F0 decisionVars)}"
  let ?rel'= "terminationLess F0 decisionVars"

  have "\<forall>x y. (x, y) \<in> ?rel \<longrightarrow> (x, y) \<in> ?rel'"
  proof-
    {
      fix stateA::State and stateB::State
      assume "(stateB, stateA) \<in> ?rel"
      hence "(stateB, stateA) \<in> ?rel'"
        using `isInitialState state0 F0`
        using invariantsHoldInValidRunsFromInitialState[of "state0" "F0" "stateA" "decisionVars"]
        using stateIsDecreasedByValidTransitions[of "stateA" "F0" "decisionVars" "stateB"]
        by simp
    }
    thus ?thesis
      by simp
  qed
  moreover 
  have "wf ?rel'"
    using `finite decisionVars`
    by (rule wfTerminationLess)
  ultimately
  show ?thesis
    using wellFoundedEmbed[of "?rel" "?rel'"]
    by simp
qed



text{* We will now give two corollaries of the previous theorem. First
  is a weak termination result that shows that there is a terminating
  run from every intial state to the final one. *}
corollary
  fixes decisionVars :: "Variable set" and F0 :: "Formula" and state0 :: "State"
  assumes "finite decisionVars" and "isInitialState state0 F0"
  shows "\<exists> state. (state0, state) \<in> transitionRelation F0 decisionVars \<and> isFinalState state F0 decisionVars"
proof-
  {
    assume "\<not> ?thesis"
    let ?Q = "{state. (state0, state) \<in> transitionRelation F0 decisionVars}"
    let ?rel = "{(stateB, stateA). (state0, stateA) \<in> transitionRelation F0 decisionVars \<and>
                         transition stateA stateB F0 decisionVars}"
    have "state0 \<in> ?Q"
      unfolding transitionRelation_def
      by simp
    hence "\<exists> state. state \<in> ?Q"
      by auto

    from assms 
    have "wf ?rel"
      using wfTransitionRelation[of "decisionVars" "state0" "F0"]
      by auto
    hence "\<forall> Q. (\<exists> x. x \<in> Q) \<longrightarrow> (\<exists> stateMin \<in> Q. \<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> Q)"
      unfolding wf_eq_minimal
      by simp
    hence " (\<exists> x. x \<in> ?Q) \<longrightarrow> (\<exists> stateMin \<in> ?Q. \<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> ?Q)"
      by rule
    with `\<exists> state. state \<in> ?Q`
    have "\<exists> stateMin \<in> ?Q. \<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> ?Q"
      by simp
    then obtain stateMin
      where "stateMin \<in> ?Q" and "\<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> ?Q"
      by auto
    
    from `stateMin \<in> ?Q` 
    have "(state0, stateMin) \<in> transitionRelation F0 decisionVars"
      by simp
    with `\<not> ?thesis`
    have "\<not> isFinalState stateMin F0 decisionVars"
      by simp
    then obtain state'::State
      where "transition stateMin state' F0 decisionVars"
      unfolding isFinalState_def
      by auto
    have "(state', stateMin) \<in> ?rel"
      using `(state0, stateMin) \<in> transitionRelation F0 decisionVars`
            `transition stateMin state' F0 decisionVars`
      by simp
    with `\<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> ?Q`
    have "state' \<notin> ?Q"
      by force
    moreover
    from `(state0, stateMin) \<in> transitionRelation F0 decisionVars` `transition stateMin state' F0 decisionVars`
    have "state' \<in> ?Q"
      unfolding transitionRelation_def
      using rtrancl_into_rtrancl[of "state0" "stateMin" "{(stateA, stateB). transition stateA stateB F0 decisionVars}" "state'"]
      by simp
    ultimately
    have False
      by simp
  }
  thus ?thesis
    by auto
qed

text{* Now we prove the final strong termination result which states
that there cannot be infinite chains of transitions. If there is an
infinite transition chain that starts from an initial state, its
elements would for a set that would contain initial state and for
every element of that set there would be another element of that set
that is directly reachable from it. We show that no such set exists. *}
corollary noInfiniteTransitionChains:
  fixes F0::Formula and decisionVars::"Variable set"
  assumes "finite decisionVars"
  shows "\<not> (\<exists> Q::(State set). \<exists> state0 \<in> Q. isInitialState state0 F0 \<and> 
                              (\<forall> state \<in> Q. (\<exists> state' \<in> Q. transition state state' F0 decisionVars))
            )"
proof-
  {
  assume "\<not> ?thesis"
  then obtain Q::"State set" and state0::"State"
    where "isInitialState state0 F0" "state0 \<in> Q"
          "\<forall> state \<in> Q. (\<exists> state' \<in> Q. transition state state' F0 decisionVars)"
    by auto
  let ?rel = "{(stateB, stateA). (state0, stateA) \<in> transitionRelation F0 decisionVars \<and>
                         transition stateA stateB F0 decisionVars}"
  from `finite decisionVars` `isInitialState state0 F0`
  have "wf ?rel"
    using wfTransitionRelation
    by simp
  hence wfmin: "\<forall>Q x. x \<in> Q \<longrightarrow>
         (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> ?rel \<longrightarrow> y \<notin> Q)"
    unfolding wf_eq_minimal 
    by simp
  let ?Q = "{state \<in> Q. (state0, state) \<in> transitionRelation F0 decisionVars}"
  from `state0 \<in> Q`
  have "state0 \<in> ?Q"
    unfolding transitionRelation_def
    by simp
  with wfmin
  obtain stateMin::State
    where "stateMin \<in> ?Q" and "\<forall>y. (y, stateMin) \<in> ?rel \<longrightarrow> y \<notin> ?Q"
    apply (erule_tac x="?Q" in allE)
    by auto

  from `stateMin \<in> ?Q`
  have "stateMin \<in> Q" "(state0, stateMin) \<in> transitionRelation F0 decisionVars"
    by auto
  with `\<forall> state \<in> Q. (\<exists> state' \<in> Q. transition state state' F0 decisionVars)`
  obtain state'::State
    where "state' \<in> Q" "transition stateMin state' F0 decisionVars"
    by auto

  with `(state0, stateMin) \<in> transitionRelation F0 decisionVars`
  have "(state', stateMin) \<in> ?rel"
    by simp
  with `\<forall>y. (y, stateMin) \<in> ?rel \<longrightarrow> y \<notin> ?Q`
  have "state' \<notin> ?Q"
    by force
  
  from `state' \<in> Q` `(state0, stateMin) \<in> transitionRelation F0 decisionVars`
    `transition stateMin state' F0 decisionVars`
  have "state' \<in> ?Q"
    unfolding transitionRelation_def
    using rtrancl_into_rtrancl[of "state0" "stateMin" "{(stateA, stateB). transition stateA stateB F0 decisionVars}" "state'"]
    by simp
  with `state' \<notin> ?Q`
  have False
    by simp
  }
  thus ?thesis
    by force
qed

(******************************************************************************)
subsection{* Completeness *}
(******************************************************************************)
text{* In this section we will first show that each final state is
either \textit{SAT} or \textit{UNSAT} state. *}

lemma finalNonConflictState: 
  fixes state::State and FO :: Formula
  assumes 
  "\<not> applicableDecide state decisionVars"
  shows "vars (elements (getM state)) \<supseteq> decisionVars"
proof
  fix x :: Variable
  let ?l = "Pos x"
  assume "x \<in> decisionVars"
  hence "var ?l = x" and "var ?l \<in> decisionVars" and "var (opposite ?l) \<in> decisionVars"
    by auto
  with `\<not> applicableDecide state decisionVars` 
  have "literalTrue ?l (elements (getM state)) \<or> literalFalse ?l (elements (getM state))"
    unfolding applicableDecideCharacterization
    by force
  with `var ?l = x`
  show "x \<in> vars (elements (getM state))"
    using valuationContainsItsLiteralsVariable[of "?l" "elements (getM state)"]
    using valuationContainsItsLiteralsVariable[of "opposite ?l" "elements (getM state)"]
    by auto
qed


lemma finalConflictingState: 
  fixes state :: State
  assumes 
  "\<not> applicableBacktrack state F0" and
  "formulaFalse F0 (elements (getM state))"  
  shows
  "decisions (getM state) = []"
using assms
using applicableBacktrackCharacterization
by auto

lemma finalStateCharacterizationLemma:
  fixes state :: State
  assumes 
  "\<not> applicableDecide state decisionVars"  and
  "\<not> applicableBacktrack state F0"
  shows
  "(\<not> formulaFalse F0 (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
   (formulaFalse F0 (elements (getM state)) \<and> decisions (getM state) = [])"
proof (cases "formulaFalse F0 (elements (getM state))")
  case True
  hence "decisions (getM state) = []"
    using assms
    using finalConflictingState
    by auto
  with True 
  show ?thesis
    by simp
next
  case False
  hence  "vars (elements (getM state)) \<supseteq> decisionVars"
    using assms
    using finalNonConflictState
    by auto
  with False
  show ?thesis
    by simp
qed


(*----------------------------------------------------------------------------*)
theorem finalStateCharacterization:
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars" and
  "isFinalState state F0 decisionVars"
  shows 
  "(\<not> formulaFalse F0 (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
   (formulaFalse F0 (elements (getM state)) \<and> decisions (getM state) = [])"
(*----------------------------------------------------------------------------*)
proof-
  from `isFinalState state F0 decisionVars` 
  have **: 
    "\<not> applicableBacktrack state F0"
    "\<not> applicableDecide state decisionVars"
    unfolding finalStateNonApplicable
    by auto

  thus ?thesis
    using finalStateCharacterizationLemma[of "state" "decisionVars"]
    by simp
qed

text{* Completeness theorems are easy consequences of this characterization and 
 soundness. *}
(*----------------------------------------------------------------------------*)
theorem completenessForSAT: 
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "satisfiable F0" and

  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars" and
  "isFinalState state F0 decisionVars"

  shows "\<not> formulaFalse F0 (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars"
(*----------------------------------------------------------------------------*)
proof-
  from assms
  have *: "(\<not> formulaFalse F0 (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
    (formulaFalse F0 (elements (getM state)) \<and> decisions (getM state) = [])"
    using finalStateCharacterization[of "state0" "F0" "state" "decisionVars"]
    by auto
  {
    assume "formulaFalse F0 (elements (getM state))"
    with * 
    have "formulaFalse F0 (elements (getM state))" "decisions (getM state) = []"
      by auto
    with assms
      have "\<not> satisfiable F0"
      using soundnessForUNSAT
      by simp
    with `satisfiable F0`
    have False
      by simp
  }
  with * show ?thesis
    by auto
qed

(*----------------------------------------------------------------------------*)
theorem completenessForUNSAT: 
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "vars F0 \<subseteq> decisionVars" and
  "\<not> satisfiable F0" and

  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars" and
  "isFinalState state F0 decisionVars"

  shows 
  "formulaFalse F0 (elements (getM state)) \<and> decisions (getM state) = []"
(*----------------------------------------------------------------------------*)
proof-
  from assms
  have *: 
  "(\<not> formulaFalse F0 (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
   (formulaFalse F0 (elements (getM state))  \<and> decisions (getM state) = [])"
    using finalStateCharacterization[of "state0" "F0" "state" "decisionVars"]
    by auto
  {
    assume "\<not> formulaFalse F0 (elements (getM state))"
    with *
    have "\<not> formulaFalse F0 (elements (getM state))" "vars (elements (getM state)) \<supseteq> decisionVars"
      by auto
    with assms
    have "satisfiable F0"
      using soundnessForSAT[of "F0" "decisionVars" "state0" "state"]
      unfolding satisfiable_def
      by auto
    with `\<not> satisfiable F0`
    have False
      by simp
  }
  with * show ?thesis
    by auto
qed

(*----------------------------------------------------------------------------*)
theorem partialCorrectness: 
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "vars F0 \<subseteq> decisionVars" and  

  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation F0 decisionVars" and
  "isFinalState state F0 decisionVars"

  shows 
  "satisfiable F0 = (\<not> formulaFalse F0 (elements (getM state)))"
(*----------------------------------------------------------------------------*)
using assms
using completenessForUNSAT[of "F0" "decisionVars" "state0" "state"]
using completenessForSAT[of "F0" "state0" "state" "decisionVars"]
by auto

end
