(*    Title:              SatSolverVerification/NieuwenhuisOliverasTinelli.thy
      Author:             Filip Maric
      Maintainer:         Filip Maric <filip at matf.bg.ac.yu>
*)

section{* Transition system of Nieuwenhuis, Oliveras and Tinelli. *}
theory NieuwenhuisOliverasTinelli
imports SatSolverVerification
begin

text{* This theory formalizes the transition rule system given by
Nieuwenhuis et al. in \cite{NieuwenhuisOliverasTinelli} *}


(******************************************************************************)
subsection{* Specification *}
(******************************************************************************)

record State = 
"getF" :: Formula
"getM" :: LiteralTrail

definition
appliedDecide:: "State \<Rightarrow> State \<Rightarrow> Variable set \<Rightarrow> bool"
where
"appliedDecide stateA stateB decisionVars == 
  \<exists> l. 
        (var l) \<in> decisionVars \<and> 
        \<not> l el (elements (getM stateA)) \<and> 
        \<not> opposite l el (elements (getM stateA)) \<and>

        getF stateB = getF stateA \<and>
        getM stateB = getM stateA @ [(l, True)]
"
definition
applicableDecide :: "State \<Rightarrow> Variable set \<Rightarrow> bool"
where
"applicableDecide state decisionVars == \<exists> state'. appliedDecide state state' decisionVars"

definition
appliedUnitPropagate :: "State \<Rightarrow> State \<Rightarrow> bool"
where
"appliedUnitPropagate stateA stateB == 
  \<exists> (uc::Clause) (ul::Literal). 
       uc el (getF stateA) \<and> 
       isUnitClause uc ul (elements (getM stateA)) \<and> 

       getF stateB = getF stateA \<and>
       getM stateB = getM stateA @ [(ul, False)]
"
definition
applicableUnitPropagate :: "State \<Rightarrow> bool"
where
"applicableUnitPropagate state == \<exists> state'. appliedUnitPropagate state state'"

definition
appliedBackjump :: "State \<Rightarrow> State \<Rightarrow> bool"
where
"appliedBackjump stateA stateB == 
  \<exists> bc bl level. 
       isUnitClause bc bl (elements (prefixToLevel level (getM stateA))) \<and> 
       formulaEntailsClause (getF stateA) bc \<and> 
       var bl \<in> vars (getF stateA) \<union> vars (elements (getM stateA)) \<and> 
       0 \<le> level \<and> level < (currentLevel (getM stateA)) \<and>

       getF stateB = getF stateA \<and>
       getM stateB = prefixToLevel level (getM stateA) @ [(bl, False)]
"
definition
applicableBackjump :: "State \<Rightarrow> bool"
where
"applicableBackjump state ==  \<exists> state'. appliedBackjump state state'"


definition
appliedLearn :: "State \<Rightarrow> State \<Rightarrow> bool"
where
"appliedLearn stateA stateB == 
  \<exists> c. 
       (formulaEntailsClause (getF stateA) c) \<and> 
       (vars c) \<subseteq> vars (getF stateA) \<union> vars (elements (getM stateA)) \<and> 
       getF stateB = getF stateA @ [c] \<and>
       getM stateB = getM stateA
"
definition
applicableLearn :: "State \<Rightarrow> bool"
where
"applicableLearn state == (\<exists> state'. appliedLearn state state')"



text{* Solving starts with the initial formula and the empty trail. *}
definition
isInitialState :: "State \<Rightarrow> Formula \<Rightarrow> bool"
where
"isInitialState state F0 == 
      getF state = F0 \<and>
      getM state = []
"

text{* Transitions are preformed only by using given rules. *}
definition
"transition stateA stateB decisionVars == 
     appliedDecide        stateA stateB decisionVars \<or>
     appliedUnitPropagate stateA stateB \<or> 
     appliedLearn         stateA stateB \<or>
     appliedBackjump      stateA stateB 
"

text{* Transition relation is obtained by applying transition rules
iteratively. It is defined using a reflexive-transitive closure. *}
definition
"transitionRelation decisionVars == ({(stateA, stateB). transition stateA stateB decisionVars})^*"

text{* Final state is one in which no rules apply *}
definition
isFinalState :: "State \<Rightarrow> Variable set \<Rightarrow> bool"
where
"isFinalState state decisionVars == \<not> (\<exists> state'. transition state state' decisionVars)"


text{* The following several lemmas establish conditions for applicability of different rules. *}
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
  shows "applicableUnitPropagate stateA = 
  (\<exists> (uc::Clause) (ul::Literal). 
       uc el (getF stateA) \<and> 
       isUnitClause uc ul (elements (getM stateA)))
  " (is "?lhs = ?rhs")
proof
  assume "?rhs"
  then obtain ul uc 
    where *: "uc el (getF stateA)" "isUnitClause uc ul (elements (getM stateA))"
    unfolding applicableUnitPropagate_def
    by auto
  let ?stateB = "stateA\<lparr> getM := getM stateA @ [(ul, False)] \<rparr>"
  from * have "appliedUnitPropagate stateA ?stateB" 
    unfolding appliedUnitPropagate_def
    by auto
  thus ?lhs
    unfolding applicableUnitPropagate_def
    by auto
next
  assume ?lhs
  then obtain stateB uc ul
    where "uc el (getF stateA)" "isUnitClause uc ul (elements (getM stateA))"
    unfolding applicableUnitPropagate_def
    unfolding appliedUnitPropagate_def
    by auto
  thus ?rhs
    by auto
qed

lemma applicableBackjumpCharacterization:
  fixes stateA::State
  shows "applicableBackjump stateA = 
   (\<exists> bc bl level. 
      isUnitClause bc bl (elements (prefixToLevel level (getM stateA))) \<and> 
      formulaEntailsClause (getF stateA) bc \<and> 
      var bl \<in> vars (getF stateA) \<union> vars (elements (getM stateA)) \<and> 
      0 \<le> level \<and> level < (currentLevel (getM stateA)))" (is "?lhs = ?rhs")
proof
  assume "?rhs"
  then obtain bc bl level
    where *: "isUnitClause bc bl (elements (prefixToLevel level (getM stateA)))"
     "formulaEntailsClause (getF stateA) bc"
     "var bl \<in> vars (getF stateA) \<union> vars (elements (getM stateA))"
     "0 \<le> level" "level < (currentLevel (getM stateA))"
    unfolding applicableBackjump_def
    by auto
  let ?stateB = "stateA\<lparr> getM := prefixToLevel level (getM stateA) @ [(bl, False)]\<rparr>"
  from * have "appliedBackjump stateA ?stateB"
    unfolding appliedBackjump_def
    by auto
  thus "?lhs"
    unfolding applicableBackjump_def
    by auto
next
  assume "?lhs"
  then obtain stateB 
    where "appliedBackjump stateA stateB"
    unfolding applicableBackjump_def
    by auto
  then obtain bc bl level
    where "isUnitClause bc bl (elements (prefixToLevel level (getM stateA)))"
    "formulaEntailsClause (getF stateA) bc"
    "var bl \<in> vars (getF stateA) \<union> vars (elements (getM stateA))"
    "getF stateB = getF stateA" 
    "getM stateB = prefixToLevel level (getM stateA) @ [(bl, False)]"
     "0 \<le> level" "level < (currentLevel (getM stateA))"
    unfolding appliedBackjump_def
    by auto
  thus "?rhs"
    by auto
qed

lemma applicableLearnCharacterization:
  fixes stateA::State
  shows "applicableLearn stateA = 
    (\<exists> c. formulaEntailsClause (getF stateA) c \<and> 
          vars c \<subseteq> vars (getF stateA) \<union>  vars (elements (getM stateA)))" (is "?lhs = ?rhs")
proof
  assume "?rhs"
  then obtain c where
  *: "formulaEntailsClause (getF stateA) c" 
     "vars c \<subseteq> vars (getF stateA) \<union>  vars (elements (getM stateA))"
    unfolding applicableLearn_def
    by auto
  let ?stateB = "stateA\<lparr> getF := getF stateA @ [c]\<rparr>"
  from * have "appliedLearn stateA ?stateB"
    unfolding appliedLearn_def
    by auto
  thus "?lhs"
    unfolding applicableLearn_def
    by auto
next
  assume "?lhs"
  then obtain c stateB
    where
    "formulaEntailsClause (getF stateA) c"
    "vars c \<subseteq> vars (getF stateA) \<union> vars (elements (getM stateA))"
    unfolding applicableLearn_def
    unfolding appliedLearn_def
    by auto
  thus "?rhs"
    by auto
qed

text{* Final states are the ones where no rule is applicable. *}
lemma finalStateNonApplicable: 
  fixes state::State
  shows "isFinalState state decisionVars = 
          (\<not> applicableDecide state decisionVars \<and> 
           \<not> applicableUnitPropagate state \<and> 
           \<not> applicableBackjump state \<and> 
           \<not> applicableLearn state)"
unfolding isFinalState_def
unfolding transition_def
unfolding applicableDecide_def
unfolding applicableUnitPropagate_def
unfolding applicableBackjump_def
unfolding applicableLearn_def
by auto

(******************************************************************************)
subsection{* Invariants *}
(******************************************************************************)
text{* Invariants that are relevant for the rest of correctness proof. *}
definition
invariantsHoldInState :: "State \<Rightarrow> Formula \<Rightarrow> Variable set \<Rightarrow> bool"
where
"invariantsHoldInState state F0 decisionVars == 
    InvariantImpliedLiterals (getF state) (getM state) \<and>
    InvariantVarsM (getM state) F0 decisionVars \<and>
    InvariantVarsF (getF state) F0 decisionVars \<and>
    InvariantConsistent (getM state) \<and>
    InvariantUniq (getM state) \<and> 
    InvariantEquivalent F0 (getF state)
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
  InvariantVarsF_def
  InvariantConsistent_def
  InvariantUniq_def
  InvariantEquivalent_def equivalentFormulae_def
)

text{* Valid transitions preserve invariants. *}
lemma transitionsPreserveInvariants: 
  fixes stateA::State and stateB::State
  assumes "transition stateA stateB decisionVars" and 
  "invariantsHoldInState stateA F0 decisionVars"
  shows "invariantsHoldInState stateB F0 decisionVars"
proof-
    from `invariantsHoldInState stateA F0 decisionVars`
    have 
      "InvariantImpliedLiterals (getF stateA) (getM stateA)" and 
      "InvariantVarsM (getM stateA) F0 decisionVars" and
      "InvariantVarsF (getF stateA) F0 decisionVars" and
      "InvariantConsistent (getM stateA)" and
      "InvariantUniq (getM stateA)" and
      "InvariantEquivalent F0 (getF stateA)"
      unfolding invariantsHoldInState_def
      by auto
  {
    assume "appliedDecide stateA stateB decisionVars"
    then obtain l::Literal where
      "(var l) \<in> decisionVars"
      "\<not> literalTrue l (elements (getM stateA))"
      "\<not> literalFalse l (elements (getM stateA))"
      "getM stateB = getM stateA @ [(l, True)]"
      "getF stateB = getF stateA"
      unfolding appliedDecide_def
      by auto

    from `\<not> literalTrue l (elements (getM stateA))` `\<not> literalFalse l (elements (getM stateA))` 
    have *: "var l \<notin> vars (elements (getM stateA))"
      using variableDefinedImpliesLiteralDefined[of "l" "elements (getM stateA)"]
      by simp

    have "InvariantImpliedLiterals (getF stateB) (getM stateB)"
      using `getF stateB = getF stateA`
        `getM stateB = getM stateA @ [(l, True)]` 
        `InvariantImpliedLiterals (getF stateA) (getM stateA)`
        `InvariantUniq (getM stateA)`
        `var l \<notin> vars (elements (getM stateA))`
        InvariantImpliedLiteralsAfterDecide[of "getF stateA" "getM stateA" "l" "getM stateB"]
      by simp
    moreover
    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using `getM stateB = getM stateA @ [(l, True)]` 
        `InvariantVarsM (getM stateA) F0 decisionVars`
        `var l \<in> decisionVars`
        InvariantVarsMAfterDecide[of "getM stateA" "F0" "decisionVars" "l" "getM stateB"]
      by simp
    moreover 
    have "InvariantVarsF (getF stateB) F0 decisionVars"
      using `getF stateB = getF stateA`
      `InvariantVarsF (getF stateA) F0 decisionVars`
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
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using `getF stateB = getF stateA`
      `InvariantEquivalent F0 (getF stateA)`
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  moreover
  {
    assume "appliedUnitPropagate stateA stateB"
    then obtain uc::Clause and ul::Literal where 
      "uc el (getF stateA)"
      "isUnitClause uc ul (elements (getM stateA))"
      "getF stateB = getF stateA"
      "getM stateB = getM stateA @ [(ul, False)]"
      unfolding appliedUnitPropagate_def
      by auto

    from `isUnitClause uc ul (elements (getM stateA))`
    have "ul el uc"
      unfolding isUnitClause_def
      by simp

    from `uc el (getF stateA)`
    have "formulaEntailsClause (getF stateA) uc"
      by (simp add: formulaEntailsItsClauses)

    
    have "InvariantImpliedLiterals (getF stateB) (getM stateB)"
      using `getF stateB = getF stateA` 
        `InvariantImpliedLiterals (getF stateA) (getM stateA)` 
        `formulaEntailsClause (getF stateA) uc`
        `isUnitClause uc ul (elements (getM stateA))`
        `getM stateB = getM stateA @ [(ul, False)]`
        InvariantImpliedLiteralsAfterUnitPropagate[of "getF stateA" "getM stateA" "uc" "ul" "getM stateB"]
      by simp
    moreover
    from `ul el uc` `uc el (getF stateA)`
    have "ul el (getF stateA)"
      by (auto simp add: literalElFormulaCharacterization)
    with `InvariantVarsF (getF stateA) F0 decisionVars`
    have "var ul \<in> vars F0 \<union> decisionVars"
      using "formulaContainsItsLiteralsVariable" [of "ul" "getF stateA"]
      unfolding InvariantVarsF_def
      by auto

    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using `InvariantVarsM (getM stateA) F0 decisionVars`
        `var ul \<in> vars F0 \<union> decisionVars`
        `getM stateB = getM stateA @ [(ul, False)]`
        InvariantVarsMAfterUnitPropagate[of "getM stateA" "F0" "decisionVars" "ul" "getM stateB"]
      by simp
    moreover
    have "InvariantVarsF (getF stateB) F0 decisionVars"
      using `getF stateB = getF stateA`
      `InvariantVarsF (getF stateA) F0 decisionVars`
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
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using `getF stateB = getF stateA` 
      `InvariantEquivalent F0 (getF stateA)`
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  moreover
  {
    assume "appliedLearn stateA stateB"
    then obtain c::Clause where
      "formulaEntailsClause (getF stateA) c"
      "vars c \<subseteq> vars (getF stateA) \<union> vars (elements (getM stateA))"
      "getF stateB = getF stateA @ [c]"
      "getM stateB = getM stateA"
      unfolding appliedLearn_def
      by auto
    
    have "InvariantImpliedLiterals (getF stateB) (getM stateB)"
      using 
        `InvariantImpliedLiterals (getF stateA) (getM stateA)`
        `getF stateB = getF stateA @ [c]`
        `getM stateB = getM stateA`
        InvariantImpliedLiteralsAfterLearn[of "getF stateA" "getM stateA" "getF stateB"]
      by simp
    moreover
    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using 
        `InvariantVarsM (getM stateA) F0 decisionVars`
        `getM stateB = getM stateA`
      by simp
    moreover
    from `vars c \<subseteq> vars (getF stateA) \<union> vars (elements (getM stateA))`
      `InvariantVarsM (getM stateA) F0 decisionVars`
        `InvariantVarsF (getF stateA) F0 decisionVars`
    have "vars c \<subseteq> vars F0 \<union> decisionVars"
      unfolding InvariantVarsM_def
      unfolding InvariantVarsF_def
      by auto
    hence "InvariantVarsF (getF stateB) F0 decisionVars"
      using `InvariantVarsF (getF stateA) F0 decisionVars`
        `getF stateB = getF stateA @ [c]`
      using varsAppendFormulae [of "getF stateA" "[c]"]
      unfolding InvariantVarsF_def
      by simp
    moreover
    have "InvariantConsistent (getM stateB)"
      using `InvariantConsistent (getM stateA)`
        `getM stateB = getM stateA`
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using `InvariantUniq (getM stateA)`
        `getM stateB = getM stateA`
      by simp
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using
        `InvariantEquivalent F0 (getF stateA)`
        `formulaEntailsClause (getF stateA) c`
        `getF stateB = getF stateA @ [c]`
        InvariantEquivalentAfterLearn[of "F0" "getF stateA" "c" "getF stateB"]
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by simp
  }
  moreover
  {
    assume "appliedBackjump stateA stateB"
    then obtain bc::Clause and bl::Literal and level::nat
      where 
      "isUnitClause bc bl (elements (prefixToLevel level (getM stateA)))"
      "formulaEntailsClause (getF stateA) bc"
      "var bl \<in> vars (getF stateA) \<union> vars (elements (getM stateA))"
      "getF stateB = getF stateA"
      "getM stateB = prefixToLevel level (getM stateA) @ [(bl, False)]"
      unfolding appliedBackjump_def
      by auto

    have "isPrefix (prefixToLevel level (getM stateA)) (getM stateA)"
      by (simp add:isPrefixPrefixToLevel)

    have "InvariantImpliedLiterals (getF stateB) (getM stateB)"
      using `InvariantImpliedLiterals (getF stateA) (getM stateA)`
        `isPrefix (prefixToLevel level (getM stateA)) (getM stateA)`
        `isUnitClause bc bl (elements (prefixToLevel level (getM stateA)))`
        `formulaEntailsClause (getF stateA) bc`
        `getF stateB = getF stateA`
        `getM stateB = prefixToLevel level (getM stateA) @ [(bl, False)]`
        InvariantImpliedLiteralsAfterBackjump[of "getF stateA" "getM stateA" "prefixToLevel level (getM stateA)" "bc" "bl" "getM stateB"]
      by simp
    moreover

    from `InvariantVarsF (getF stateA) F0 decisionVars`
      `InvariantVarsM (getM stateA) F0 decisionVars`
      `var bl \<in> vars (getF stateA) \<union> vars (elements (getM stateA))`
    have "var bl \<in> vars F0 \<union> decisionVars"
      unfolding InvariantVarsM_def
      unfolding InvariantVarsF_def
      by auto

    have "InvariantVarsM (getM stateB) F0 decisionVars"
      using `InvariantVarsM (getM stateA) F0 decisionVars`
        `isPrefix (prefixToLevel level (getM stateA)) (getM stateA)`
        `getM stateB = prefixToLevel level (getM stateA) @ [(bl, False)]`
        `var bl \<in> vars F0 \<union> decisionVars`
        InvariantVarsMAfterBackjump[of "getM stateA" "F0" "decisionVars" "prefixToLevel level (getM stateA)" "bl" "getM stateB"]
      by simp
    moreover
    have "InvariantVarsF (getF stateB) F0 decisionVars"
      using `getF stateB = getF stateA`
      `InvariantVarsF (getF stateA) F0 decisionVars`
      by simp
    moreover    
    have "InvariantConsistent (getM stateB)"
      using `InvariantConsistent (getM stateA)`
        `isPrefix (prefixToLevel level (getM stateA)) (getM stateA)`
        `isUnitClause bc bl (elements (prefixToLevel level (getM stateA)))`
        `getM stateB = prefixToLevel level (getM stateA) @ [(bl, False)]`
        InvariantConsistentAfterBackjump[of "getM stateA" "prefixToLevel level (getM stateA)" "bc" "bl" "getM stateB"]
      by simp
    moreover
    have "InvariantUniq (getM stateB)"
      using `InvariantUniq (getM stateA)`
        `isPrefix (prefixToLevel level (getM stateA)) (getM stateA)`
        `isUnitClause bc bl (elements (prefixToLevel level (getM stateA)))`
        `getM stateB = prefixToLevel level (getM stateA) @ [(bl, False)]`
        InvariantUniqAfterBackjump[of "getM stateA" "prefixToLevel level (getM stateA)" "bc" "bl" "getM stateB"]
      by simp
    moreover
    have "InvariantEquivalent F0 (getF stateB)"
      using
      `InvariantEquivalent F0 (getF stateA)`
      `getF stateB = getF stateA`
      by simp
    ultimately
    have ?thesis
      unfolding invariantsHoldInState_def
      by auto
  }
  ultimately
  show ?thesis
    using `transition stateA stateB decisionVars`
    unfolding transition_def
    by auto
qed

text{* The consequence is that invariants hold in all valid runs. *}
lemma invariantsHoldInValidRuns: 
  fixes F0 :: Formula and decisionVars :: "Variable set"
  assumes "invariantsHoldInState stateA F0 decisionVars" and
  "(stateA, stateB) \<in> transitionRelation decisionVars"
  shows "invariantsHoldInState stateB F0 decisionVars"
using assms
using transitionsPreserveInvariants
using rtrancl_induct[of "stateA" "stateB" 
  "{(stateA, stateB). transition stateA stateB decisionVars}" "\<lambda> x. invariantsHoldInState x F0 decisionVars"]
unfolding transitionRelation_def
by auto

lemma invariantsHoldInValidRunsFromInitialState:
  fixes F0 :: Formula and decisionVars :: "Variable set"
  assumes "isInitialState state0 F0" 
  and "(state0, state) \<in> transitionRelation decisionVars"
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
  and @{term "vars (elements (getM state)) \<supseteq> decisionVars"}
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
  "(state0, state) \<in> transitionRelation decisionVars"

  "formulaFalse (getF state) (elements (getM state))"
  "decisions (getM state) = []"

  shows "\<not> satisfiable F0"
(*----------------------------------------------------------------------------*)
proof-
  from `isInitialState state0 F0` `(state0, state) \<in> transitionRelation decisionVars`
  have "invariantsHoldInState state F0 decisionVars" 
    using invariantsHoldInValidRunsFromInitialState
    by simp
  hence "InvariantImpliedLiterals (getF state) (getM state)" "InvariantEquivalent F0 (getF state)"
    unfolding invariantsHoldInState_def
    by auto
  with `formulaFalse (getF state) (elements (getM state))`
    `decisions (getM state) = []`
  show ?thesis
    using unsatReport[of "getF state" "getM state" "F0"]
    by simp
qed

(*----------------------------------------------------------------------------*)
theorem soundnessForSAT:
  fixes F0 :: Formula and decisionVars :: "Variable set" and state0 :: State and state :: State
  assumes 
  "vars F0 \<subseteq> decisionVars" and

  "isInitialState state0 F0" and
  "(state0, state) \<in> transitionRelation decisionVars"

  "\<not> formulaFalse (getF state) (elements (getM state))"
  "vars (elements (getM state)) \<supseteq> decisionVars"  
  shows 
  "model (elements (getM state)) F0"
(*----------------------------------------------------------------------------*)
proof-
  from `isInitialState state0 F0` `(state0, state) \<in> transitionRelation decisionVars`
  have "invariantsHoldInState state F0 decisionVars" 
    using invariantsHoldInValidRunsFromInitialState
    by simp
  hence 
    "InvariantConsistent (getM state)" 
    "InvariantEquivalent F0 (getF state)"
    "InvariantVarsF (getF state) F0 decisionVars"
    unfolding invariantsHoldInState_def
    by auto
  with assms
  show ?thesis
  using satReport[of "F0" "decisionVars" "getF state" "getM state"]
  by simp
qed


(******************************************************************************)
subsection{* Termination *}
(******************************************************************************)
text{* This system is terminating, but only under assumption that
there is no infinite derivation consisting only of applications of 
rule $Learn$. We will formalize this condition by requiring that there
there exists an ordering @{term learnL} on the formulae that is
well-founded such that the state is decreased with each application
of the $Learn$ rule. If such ordering exists, the termination
ordering is built as a lexicographic combination of @{term lexLessRestricted} 
trail ordering and the @{term learnL} ordering. 
*}

definition "lexLessState F0 decisionVars == {((stateA::State), (stateB::State)). 
                       (getM stateA, getM stateB) \<in> lexLessRestricted (vars F0 \<union> decisionVars)}" 
definition "learnLessState learnL == {((stateA::State), (stateB::State)). 
                        getM stateA = getM stateB \<and> (getF stateA, getF stateB) \<in> learnL}" 
definition "terminationLess F0 decisionVars learnL == 
  {((stateA::State), (stateB::State)). 
      (stateA,stateB) \<in> lexLessState F0 decisionVars \<or> 
      (stateA,stateB) \<in> learnLessState learnL}"

text{* We want to show that every valid transition decreases a state
  with respect to the constructed termination ordering. Therefore, we
  show that $Decide$, $UnitPropagate$ and $Backjump$ rule decrease the
  trail with respect to the restricted trail ordering @{term
  lexLessRestricted}.  Invariants ensure that trails are indeed uniq,
  consistent and with finite variable sets. By assumption, $Learn$
  rule will decrease the formula component of the state with respect
  to the @{term learnL} ordering. *}

lemma trailIsDecreasedByDeciedUnitPropagateAndBackjump:
  fixes stateA::State and stateB::State
  assumes "invariantsHoldInState stateA F0 decisionVars" and
  "appliedDecide stateA stateB decisionVars \<or> appliedUnitPropagate stateA stateB \<or> appliedBackjump stateA stateB"
  shows "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
proof-
  from `appliedDecide stateA stateB decisionVars \<or> appliedUnitPropagate stateA stateB \<or> appliedBackjump stateA stateB`
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
    assume "appliedUnitPropagate stateA stateB"
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
    assume "appliedBackjump stateA stateB"
    then obtain bc::Clause and bl::Literal and level::nat
      where 
      "isUnitClause bc bl (elements (prefixToLevel level (getM stateA)))"
      "formulaEntailsClause (getF stateA) bc"
      "var bl \<in> vars (getF stateA) \<union> vars (elements (getM stateA))"
      "0 \<le> level" "level < currentLevel (getM stateA)" 
      "getF stateB = getF stateA"
      "getM stateB = prefixToLevel level (getM stateA) @ [(bl, False)]"
      unfolding appliedBackjump_def
      by auto
    
    with `getM stateB = prefixToLevel level (getM stateA) @ [(bl, False)]`
    have "(getM stateB, getM stateA) \<in> lexLess"
      by (simp add:lexLessBackjump)
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

text{* Now we can show that, under the assumption for $Learn$ rule,
  every rule application decreases a state with respect to the
  constructed termination ordering. *}
theorem stateIsDecreasedByValidTransitions:
  fixes stateA::State and stateB::State 
  assumes "invariantsHoldInState stateA F0 decisionVars" and "transition stateA stateB decisionVars"
  "appliedLearn stateA stateB  \<longrightarrow> (getF stateB, getF stateA) \<in> learnL"
  shows "(stateB, stateA) \<in> terminationLess F0 decisionVars learnL"
proof-
  {
    assume "appliedDecide stateA stateB decisionVars \<or> appliedUnitPropagate stateA stateB \<or> appliedBackjump stateA stateB"
    with `invariantsHoldInState stateA F0 decisionVars`
    have "(getM stateB, getM stateA) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
      using trailIsDecreasedByDeciedUnitPropagateAndBackjump
      by simp
    hence "(stateB, stateA) \<in> lexLessState F0 decisionVars"
      unfolding lexLessState_def
      by simp
    hence "(stateB, stateA) \<in> terminationLess F0 decisionVars learnL"
      unfolding terminationLess_def
      by simp
  }
  moreover
  {
    assume "appliedLearn stateA stateB"
    with `appliedLearn stateA stateB \<longrightarrow> (getF stateB, getF stateA) \<in> learnL`
    have "(getF stateB, getF stateA) \<in> learnL"
      by simp
    moreover
    from `appliedLearn stateA stateB`
    have "(getM stateB) = (getM stateA)"
      unfolding appliedLearn_def
      by auto
   ultimately
   have "(stateB, stateA) \<in> learnLessState learnL" 
      unfolding learnLessState_def
      by simp
    hence "(stateB, stateA) \<in> terminationLess F0 decisionVars learnL"
      unfolding terminationLess_def
      by simp
  }
  ultimately
  show ?thesis
    using `transition stateA stateB decisionVars`
    unfolding transition_def
    by auto
qed

text{* The minimal states with respect to the termination ordering are
  final i.e., no further transition rules are applicable. *}
definition 
"isMinimalState stateMin F0 decisionVars learnL == (\<forall> state::State. (state, stateMin) \<notin> terminationLess F0 decisionVars learnL)"

lemma minimalStatesAreFinal:
  fixes stateA::State
  assumes *: "\<forall> (stateA::State) (stateB::State). appliedLearn stateA stateB  \<longrightarrow> (getF stateB, getF stateA) \<in> learnL" and
  "invariantsHoldInState state F0 decisionVars" and "isMinimalState state F0 decisionVars learnL"
  shows "isFinalState state decisionVars"
proof-
  {
    assume "\<not> ?thesis"
    then obtain state'::State 
      where "transition state state' decisionVars"
      unfolding isFinalState_def
      by auto
    with `invariantsHoldInState state F0 decisionVars` *
    have "(state', state) \<in> terminationLess F0 decisionVars learnL"
      using stateIsDecreasedByValidTransitions[of "state" "F0" "decisionVars" "state'" "learnL"]
      unfolding transition_def
      by auto
    with `isMinimalState state F0 decisionVars learnL` 
    have False
      unfolding isMinimalState_def
      by auto
  }
  thus ?thesis
    by auto
qed

text{* We now prove that termination ordering is well founded. We
start with two auxiliary lemmas. *}
lemma wfLexLessState: 
  fixes decisionVars :: "Variable set" and F0 :: "Formula"
  assumes "finite decisionVars"
  shows "wf (lexLessState F0 decisionVars)"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q)"
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
      have "\<forall>state'. (state', stateMin) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q"
      proof
        fix state'
        show "(state', stateMin) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q"
        proof
          assume "(state', stateMin) \<in> lexLessState F0 decisionVars"
          hence "(getM state', getM stateMin) \<in> lexLessRestricted (vars F0 \<union> decisionVars)"
            unfolding lexLessState_def
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
      have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q)"
        by auto
    }
    thus ?thesis
      by auto
  qed
qed

lemma wfLearnLessState: 
  assumes "wf learnL"
  shows "wf (learnLessState learnL)"
unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists>stateMin\<in>Q. \<forall>state'. (state', stateMin) \<in> learnLessState learnL \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q :: "State set" and state :: State
      assume "state \<in> Q"
      let ?M = "(getM state)"
      let ?Q1 = "{f::Formula. \<exists> state. state \<in> Q \<and> (getM state) = ?M \<and> (getF state) = f}"
      from `state \<in> Q` 
      have "getF state \<in> ?Q1"
        by auto            
      with `wf learnL`
      obtain FMin where "FMin \<in> ?Q1" "\<forall>F'. (F', FMin) \<in> learnL \<longrightarrow> F' \<notin> ?Q1"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q1" in allE)
        apply (erule_tac x="getF state" in allE)
        by auto
      from `FMin \<in> ?Q1` obtain stateMin
        where "stateMin \<in> Q" "(getM stateMin) = ?M" "getF stateMin = FMin"
        by auto
      have "\<forall>state'. (state', stateMin) \<in> learnLessState learnL \<longrightarrow> state' \<notin> Q"
      proof
        fix state'
        show "(state', stateMin) \<in> learnLessState learnL \<longrightarrow> state' \<notin> Q"
        proof
          assume "(state', stateMin) \<in> learnLessState learnL"
          with `getM stateMin = ?M` 
          have "getM state' = getM stateMin" "(getF state', getF stateMin) \<in> learnL"
            unfolding learnLessState_def
            by auto
          from `\<forall>F'. (F', FMin) \<in> learnL \<longrightarrow> F' \<notin> ?Q1` 
            `(getF state', getF stateMin) \<in> learnL` `getF stateMin = FMin`
          have "getF state' \<notin> ?Q1"
            by simp
          with `getM state' = getM stateMin` `getM stateMin = ?M`
          show "state' \<notin> Q"
            by auto
        qed
      qed
      with `stateMin \<in> Q` 
      have "\<exists> stateMin \<in> Q. (\<forall>state'. (state', stateMin) \<in> learnLessState learnL \<longrightarrow> state' \<notin> Q)"
        by auto
    }
    thus ?thesis
      by auto
  qed
qed

text{* Now we can prove the following key lemma which shows that the
termination ordering is well founded. *}
lemma wfTerminationLess:
  fixes F0 :: Formula and decisionVars :: "Variable set"
  assumes "finite decisionVars" "wf learnL"
  shows "wf (terminationLess F0 decisionVars learnL)"
  unfolding wf_eq_minimal
proof-
  show "\<forall>Q state. state \<in> Q \<longrightarrow> (\<exists> stateMin \<in> Q. \<forall>state'. (state', stateMin) \<in> terminationLess F0 decisionVars learnL \<longrightarrow> state' \<notin> Q)"
  proof-
    {
      fix Q::"State set"
      fix state::State
      assume "state \<in> Q"
      have "wf (lexLessState F0 decisionVars)"
        using wfLexLessState[of "decisionVars" "F0"]
        using `finite decisionVars`
        by simp
      with `state \<in> Q` obtain state0
        where "state0 \<in> Q" "\<forall>state'. (state', state0) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q"
        unfolding wf_eq_minimal
        by auto
      let ?Q0 = "{state. state \<in> Q \<and> (getM state) = (getM state0)}"
      from `state0 \<in> Q`
      have "state0 \<in> ?Q0"
        by simp
      from `wf learnL` 
      have "wf (learnLessState learnL)"
        using wfLearnLessState
        by simp
      with `state0 \<in> ?Q0` obtain state1
        where "state1 \<in> ?Q0" "\<forall>state'. (state', state1) \<in> learnLessState learnL \<longrightarrow> state' \<notin> ?Q0"
        unfolding wf_eq_minimal
        apply (erule_tac x="?Q0" in allE)
        apply (erule_tac x="state0" in allE)
        by auto
      from `state1 \<in> ?Q0`
      have "state1 \<in> Q" "getM state1 = getM state0"
        by auto
      let ?stateMin = state1
      have "\<forall>state'. (state', ?stateMin) \<in> terminationLess F0 decisionVars learnL \<longrightarrow> state' \<notin> Q"
      proof
        fix state'
        show "(state', ?stateMin) \<in> terminationLess F0 decisionVars learnL \<longrightarrow> state' \<notin> Q"
        proof
          assume "(state', ?stateMin) \<in> terminationLess F0 decisionVars learnL"
          hence 
            "(state', ?stateMin) \<in> lexLessState F0 decisionVars \<or>
            (state', ?stateMin) \<in> learnLessState learnL"
            unfolding terminationLess_def
            by auto
          moreover
          {
            assume "(state', ?stateMin) \<in> lexLessState F0 decisionVars"
            with `getM state1 = getM state0`
            have "(state', state0) \<in> lexLessState F0 decisionVars"
              unfolding lexLessState_def
              by simp
            with `\<forall>state'. (state', state0) \<in> lexLessState F0 decisionVars \<longrightarrow> state' \<notin> Q`
            have "state' \<notin> Q"
              by simp
          }
          moreover
          {
            assume "(state', ?stateMin) \<in> learnLessState learnL"
            with `\<forall>state'. (state', state1) \<in> learnLessState learnL \<longrightarrow> state' \<notin> ?Q0`
            have "state' \<notin> ?Q0"
              by simp
            from `(state', state1) \<in> learnLessState learnL` `getM state1 = getM state0`
            have "getM state' = getM state0"
              unfolding learnLessState_def
              by auto
            with `state' \<notin> ?Q0`
            have "state' \<notin> Q"
              by simp
          }
          ultimately
          show "state' \<notin> Q"
            by auto
        qed
      qed
      with `?stateMin \<in> Q` have "(\<exists> stateMin \<in> Q. \<forall>state'. (state', stateMin) \<in> terminationLess F0 decisionVars learnL \<longrightarrow> state' \<notin> Q)"
        by auto
    }
    thus ?thesis
      by simp
  qed
qed

text{* Using the termination ordering we show that the transition
 relation is well founded on states reachable from initial state.  The
 assumption for the $Learn$ rule is neccessary. *}
(*----------------------------------------------------------------------------*)
theorem wfTransitionRelation:
  fixes decisionVars :: "Variable set" and F0 :: "Formula"
  assumes "finite decisionVars" and "isInitialState state0 F0" and
  *: "\<exists> learnL::(Formula \<times> Formula) set. 
        wf learnL \<and> 
        (\<forall> stateA stateB. appliedLearn stateA stateB  \<longrightarrow> (getF stateB, getF stateA) \<in> learnL)"
  shows "wf {(stateB, stateA). 
             (state0, stateA) \<in> transitionRelation decisionVars \<and> (transition stateA stateB decisionVars)}"
(*----------------------------------------------------------------------------*)
proof-
  from * obtain learnL::"(Formula \<times> Formula) set"
    where 
    "wf learnL" and
    **: "\<forall> stateA stateB. appliedLearn stateA stateB  \<longrightarrow> (getF stateB, getF stateA) \<in> learnL"
    by auto
  let ?rel = "{(stateB, stateA). 
                  (state0, stateA) \<in> transitionRelation decisionVars \<and> (transition stateA stateB decisionVars)}"
  let ?rel'= "terminationLess F0 decisionVars learnL"

  have "\<forall>x y. (x, y) \<in> ?rel \<longrightarrow> (x, y) \<in> ?rel'"
  proof-
    {
      fix stateA::State and stateB::State
      assume "(stateB, stateA) \<in> ?rel"
      hence "(stateB, stateA) \<in> ?rel'"
        using `isInitialState state0 F0`
        using invariantsHoldInValidRunsFromInitialState[of "state0" "F0" "stateA" "decisionVars"]
        using stateIsDecreasedByValidTransitions[of "stateA" "F0" "decisionVars" "stateB"] **
        by simp
    }
    thus ?thesis
      by simp
  qed
  moreover 
  have "wf ?rel'"
    using `finite decisionVars` `wf learnL`
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
  assumes "finite decisionVars" and "isInitialState state0 F0" and
  *: "\<exists> learnL::(Formula \<times> Formula) set. 
        wf learnL \<and> 
        (\<forall> stateA stateB. appliedLearn stateA stateB  \<longrightarrow> (getF stateB, getF stateA) \<in> learnL)"
  shows "\<exists> state. (state0, state) \<in> transitionRelation decisionVars \<and> isFinalState state decisionVars"
proof-
  {
    assume "\<not> ?thesis"
    let ?Q = "{state. (state0, state) \<in> transitionRelation decisionVars}"
    let ?rel = "{(stateB, stateA). (state0, stateA) \<in> transitionRelation decisionVars \<and>
                         transition stateA stateB decisionVars}"
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
    have "(state0, stateMin) \<in> transitionRelation decisionVars"
      by simp
    with `\<not> ?thesis`
    have "\<not> isFinalState stateMin decisionVars"
      by simp
    then obtain state'::State
      where "transition stateMin state' decisionVars"
      unfolding isFinalState_def
      by auto
    have "(state', stateMin) \<in> ?rel"
      using `(state0, stateMin) \<in> transitionRelation decisionVars`
            `transition stateMin state' decisionVars`
      by simp
    with `\<forall> state. (state, stateMin) \<in> ?rel \<longrightarrow> state \<notin> ?Q`
    have "state' \<notin> ?Q"
      by force
    moreover
    from `(state0, stateMin) \<in> transitionRelation decisionVars` `transition stateMin state' decisionVars`
    have "state' \<in> ?Q"
      unfolding transitionRelation_def
      using rtrancl_into_rtrancl[of "state0" "stateMin" "{(stateA, stateB). transition stateA stateB decisionVars}" "state'"]
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
  assumes "finite decisionVars" and
  *: "\<exists> learnL::(Formula \<times> Formula) set. 
        wf learnL \<and> 
        (\<forall> stateA stateB. appliedLearn stateA stateB  \<longrightarrow> (getF stateB, getF stateA) \<in> learnL)"
  shows "\<not> (\<exists> Q::(State set). \<exists> state0 \<in> Q. isInitialState state0 F0 \<and> 
                              (\<forall> state \<in> Q. (\<exists> state' \<in> Q. transition state state' decisionVars))
            )"
proof-
  {
  assume "\<not> ?thesis"
  then obtain Q::"State set" and state0::"State"
    where "isInitialState state0 F0" "state0 \<in> Q"
          "\<forall> state \<in> Q. (\<exists> state' \<in> Q. transition state state' decisionVars)"
    by auto
  let ?rel = "{(stateB, stateA). (state0, stateA) \<in> transitionRelation decisionVars \<and>
                         transition stateA stateB decisionVars}"
  from `finite decisionVars` `isInitialState state0 F0` *
  have "wf ?rel"
    using wfTransitionRelation
    by simp
  hence wfmin: "\<forall>Q x. x \<in> Q \<longrightarrow>
         (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> ?rel \<longrightarrow> y \<notin> Q)"
    unfolding wf_eq_minimal 
    by simp
  let ?Q = "{state \<in> Q. (state0, state) \<in> transitionRelation decisionVars}"
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
  have "stateMin \<in> Q" "(state0, stateMin) \<in> transitionRelation decisionVars"
    by auto
  with `\<forall> state \<in> Q. (\<exists> state' \<in> Q. transition state state' decisionVars)`
  obtain state'::State
    where "state' \<in> Q" "transition stateMin state' decisionVars"
    by auto

  with `(state0, stateMin) \<in> transitionRelation decisionVars`
  have "(state', stateMin) \<in> ?rel"
    by simp
  with `\<forall>y. (y, stateMin) \<in> ?rel \<longrightarrow> y \<notin> ?Q`
  have "state' \<notin> ?Q"
    by force
  
  from `state' \<in> Q` `(state0, stateMin) \<in> transitionRelation decisionVars`
    `transition stateMin state' decisionVars`
  have "state' \<in> ?Q"
    unfolding transitionRelation_def
    using rtrancl_into_rtrancl[of "state0" "stateMin" "{(stateA, stateB). transition stateA stateB decisionVars}" "state'"]
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
  "InvariantUniq (getM state)" and
  "InvariantConsistent (getM state)" and
  "InvariantImpliedLiterals (getF state) (getM state)"
  "\<not> applicableBackjump state" and
  "formulaFalse (getF state) (elements (getM state))"  
  shows
  "decisions (getM state) = []"
proof-
  from `InvariantUniq (getM state)`
  have "uniq (elements (getM state))"
    unfolding InvariantUniq_def
    .
  from `InvariantConsistent (getM state)`
  have "consistent (elements (getM state))"
    unfolding InvariantConsistent_def
    .

  let ?c = "oppositeLiteralList (decisions (getM state))"
  {
    assume "\<not> ?thesis"
    hence "?c \<noteq> []"
      using oppositeLiteralListNonempty[of "decisions (getM state)"]
      by simp
    moreover
    have "clauseFalse ?c (elements (getM state))"
    proof-
      {
        fix l::Literal
        assume "l el ?c"
        hence "opposite l el decisions (getM state)"
          using literalElListIffOppositeLiteralElOppositeLiteralList [of "l" "?c"]
          by simp
        hence "literalFalse l (elements (getM state))"
          using markedElementsAreElements[of "opposite l" "getM state"]
          by simp
      } 
      thus ?thesis
        using clauseFalseIffAllLiteralsAreFalse[of "?c" "elements (getM state)"]
        by simp
    qed
    moreover
    let ?l = "getLastAssertedLiteral (oppositeLiteralList ?c) (elements (getM state))"
    have "isLastAssertedLiteral ?l (oppositeLiteralList ?c) (elements (getM state))"
      using `InvariantUniq (getM state)`
      using getLastAssertedLiteralCharacterization[of "?c" "elements (getM state)"]
        `?c \<noteq> []` `clauseFalse ?c (elements (getM state))`
      unfolding InvariantUniq_def
      by simp
    moreover
    have "\<forall> l. l el ?c \<longrightarrow> (opposite l) el (decisions (getM state))"
    proof-
      {
        fix l::Literal
        assume "l el ?c"
        hence "(opposite l) el (oppositeLiteralList ?c)"
          using literalElListIffOppositeLiteralElOppositeLiteralList[of "l" "?c"]
          by simp
      }
      thus ?thesis
        by simp
    qed
    ultimately
    have "\<exists> level. (isBackjumpLevel level (opposite ?l) ?c (getM state))"
      using `uniq (elements (getM state))`
      using allDecisionsThenExistsBackjumpLevel[of "getM state" "?c" "opposite ?l"]
      by simp
    then obtain level::nat
      where "isBackjumpLevel level (opposite ?l) ?c (getM state)"
      by auto
    with `consistent (elements (getM state))` `uniq (elements (getM state))` `clauseFalse ?c (elements (getM state))`
    have "isUnitClause ?c (opposite ?l) (elements (prefixToLevel level (getM state)))"
      using isBackjumpLevelEnsuresIsUnitInPrefix[of "getM state" "?c" "level" "opposite ?l"]
      by simp
    moreover
    have "formulaEntailsClause (getF state) ?c"
    proof-
      from `clauseFalse ?c (elements (getM state))` `consistent (elements (getM state))`
      have "\<not> clauseTautology ?c"
        using tautologyNotFalse[of "?c" "elements (getM state)"]
        by auto

      from `formulaFalse (getF state) (elements (getM state))` `InvariantImpliedLiterals (getF state) (getM state)`
      have "\<not> satisfiable ((getF state) @ val2form (decisions (getM state)))"
        using InvariantImpliedLiteralsAndFormulaFalseThenFormulaAndDecisionsAreNotSatisfiable
        by simp
      hence "\<not> satisfiable ((getF state) @ val2form (oppositeLiteralList ?c))"
        by simp
      with `\<not> clauseTautology ?c`
      show ?thesis
        using unsatisfiableFormulaWithSingleLiteralClauses
        by simp
    qed
    moreover 
    have "var ?l \<in> vars (getF state) \<union> vars (elements (getM state))"
    proof-
      from `isLastAssertedLiteral ?l (oppositeLiteralList ?c) (elements (getM state))`
      have "?l el (oppositeLiteralList ?c)"
        unfolding isLastAssertedLiteral_def
        by simp
      hence "literalTrue ?l (elements (getM state))"
        by (simp add: markedElementsAreElements)
      hence "var ?l \<in> vars (elements (getM state))"
        using valuationContainsItsLiteralsVariable[of "?l" "elements (getM state)"]
        by simp
      thus ?thesis
        by simp
    qed
    moreover 
    have "0 \<le> level" "level < (currentLevel (getM state))"
    proof-
      from `isBackjumpLevel level (opposite ?l) ?c (getM state)`
      have "0 \<le> level" "level < (elementLevel ?l (getM state))"
        unfolding isBackjumpLevel_def
        by auto
      thus "0 \<le> level" "level < (currentLevel (getM state))"
        using elementLevelLeqCurrentLevel[of "?l" "getM state"]
        by auto
    qed
    ultimately
    have "applicableBackjump state"
      unfolding applicableBackjumpCharacterization
      by force
    with `\<not> applicableBackjump state`
    have "False"
      by simp
  }
  thus ?thesis
    by auto
qed

lemma finalStateCharacterizationLemma:
  fixes state :: State
  assumes 
  "InvariantUniq (getM state)" and
  "InvariantConsistent (getM state)" and
  "InvariantImpliedLiterals (getF state) (getM state)"
  "\<not> applicableDecide state decisionVars"  and
  "\<not> applicableBackjump state"
  shows
  "(\<not> formulaFalse (getF state) (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
   (formulaFalse (getF state) (elements (getM state)) \<and> decisions (getM state) = [])"
proof (cases "formulaFalse (getF state) (elements (getM state))")
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
  "(state0, state) \<in> transitionRelation decisionVars" and
  "isFinalState state decisionVars"
  shows 
  "(\<not> formulaFalse (getF state) (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
   (formulaFalse (getF state) (elements (getM state)) \<and> decisions (getM state) = [])"
(*----------------------------------------------------------------------------*)
proof-
  from `isInitialState state0 F0` `(state0, state) \<in> transitionRelation decisionVars`
  have "invariantsHoldInState state F0 decisionVars"
    using invariantsHoldInValidRunsFromInitialState
    by simp
  hence 
    *: "InvariantUniq (getM state)" 
    "InvariantConsistent (getM state)"
    "InvariantImpliedLiterals (getF state) (getM state)"
    unfolding invariantsHoldInState_def
    by auto

  from `isFinalState state decisionVars` 
  have **: 
    "\<not> applicableBackjump state"
    "\<not> applicableDecide state decisionVars"
    unfolding finalStateNonApplicable
    by auto

  from * **
  show ?thesis
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
  "(state0, state) \<in> transitionRelation decisionVars" and
  "isFinalState state decisionVars"
  shows "\<not> formulaFalse (getF state) (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars"
(*----------------------------------------------------------------------------*)
proof-
  from assms
  have *: "(\<not> formulaFalse (getF state) (elements (getM state))  \<and> vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
    (formulaFalse (getF state) (elements (getM state)) \<and> decisions (getM state) = [])"
    using finalStateCharacterization[of "state0" "F0" "state" "decisionVars"]
    by auto
  {
    assume "formulaFalse (getF state) (elements (getM state))"
    with * 
    have "formulaFalse (getF state) (elements (getM state))" "decisions (getM state) = []"
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
  "(state0, state) \<in> transitionRelation decisionVars" and
  "isFinalState state decisionVars"
  shows 
  "formulaFalse (getF state) (elements (getM state)) \<and> decisions (getM state) = []"
(*----------------------------------------------------------------------------*)
proof-
  from assms
  have *: 
  "(\<not> formulaFalse (getF state) (elements (getM state)) \<and> vars (elements (getM state)) \<supseteq> decisionVars) \<or> 
   (formulaFalse (getF state) (elements (getM state))  \<and> decisions (getM state) = [])"
    using finalStateCharacterization[of "state0" "F0" "state" "decisionVars"]
    by auto
  {
    assume "\<not> formulaFalse (getF state) (elements (getM state))"
    with *
    have "\<not> formulaFalse (getF state) (elements (getM state))" "vars (elements (getM state)) \<supseteq> decisionVars"
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
  "(state0, state) \<in> transitionRelation decisionVars" and
  "isFinalState state decisionVars"
  shows 
  "satisfiable F0 = (\<not> formulaFalse (getF state) (elements (getM state)))"
(*----------------------------------------------------------------------------*)
using assms
using completenessForUNSAT[of "F0" "decisionVars" "state0" "state"]
using completenessForSAT[of "F0" "state0" "state" "decisionVars"]
by auto

end
