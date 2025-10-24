section \<open>Relative Security Unwinding Incompleteness example\<close>

text \<open>Demonstrating a counterexample which is secure but fails in the infinatary unwinding\<close>

theory Incomplete
  imports Unwinding 
begin


no_notation bot ("\<bottom>")

(* This will be used for non-informative entities, e.g., a noninformative output: *)
abbreviation noninform ("\<bottom>") where "\<bottom> \<equiv> undefined"


text \<open>Demonstrating a counterexample which is secure but fails in the unwinding\<close>
datatype State = ss | ss' 
type_synonym secret = "State"



fun transit::"State \<Rightarrow> State \<Rightarrow> bool"(infix "\<rightarrow>I" 55) where 
  "transit s s' = (if (s = ss \<and> s' = ss') then True else False)"

lemma transit_singlv:"ss \<rightarrow>I ss'" by auto

lemma transit_iff:"s \<rightarrow>I s' \<longleftrightarrow> (s = ss \<and> s' = ss')" by auto

definition "final x \<equiv> \<forall>y. \<not> (\<rightarrow>I) x y"

lemma final_sv'[simp]:"final ss'" unfolding final_def transit_iff by auto

lemma final_iff: "final s \<longleftrightarrow> s = ss'" unfolding final_def transit_iff by (auto,metis State.exhaust)

text \<open>Vanilla-semantics system model\<close>
type_synonym stateV = State
fun validTransV where "validTransV (s,s') = s \<rightarrow>I s'"

text \<open>No secrets or interaction\<close>
fun isIntV :: "stateV \<Rightarrow> bool" where "isIntV s = False"
fun getIntV::"stateV \<Rightarrow> nat \<times> nat" where "getIntV s = (\<bottom>,\<bottom>)"

definition isSecV :: "stateV \<Rightarrow> bool" where "isSecV s = False"
fun getSecV :: "stateV \<Rightarrow> secret" where "getSecV s = s"

(* *)

text \<open>The optimization-enhanced system model\<close>

type_synonym stateO = State
fun validTransO where "validTransO (s,s') = s \<rightarrow>I s'"

text \<open>No interaction, only isSec at starting state\<close>
fun isIntO :: "stateO \<Rightarrow> bool" where "isIntO s = False"
fun getIntO::"stateO \<Rightarrow> nat \<times> nat" where "getIntO s = (\<bottom>,\<bottom>)"

definition isSecO :: "stateO \<Rightarrow> bool" where "isSecO s = (if s = ss then True else False)"
fun getSecO :: "stateO \<Rightarrow> secret" where "getSecO s = s"

text \<open>corrState\<close>
fun corrState :: "stateV \<Rightarrow> stateO \<Rightarrow> bool" where 
"corrState cfgO cfgA = True"

interpretation Rel_Sec 
  where validTransV = validTransV and istateV = "\<lambda>s. s = ss" 
  and finalV = final 
  and isSecV = isSecV and getSecV = getSecV
  and isIntV = isIntV and getIntV = getIntV
  (* *)
  and validTransO = validTransO and istateO = "\<lambda>s. s = ss"
  and finalO = final
  and isSecO = isSecO  and getSecO = getSecO
  and isIntO = isIntO and getIntO = getIntO
  and corrState = corrState 
  apply(unfold_locales)
  subgoal by (auto simp: final_def)
  subgoal by (auto simp: final_def)
  subgoal by (auto simp: final_def isSecV_def)
  subgoal by (auto simp: final_def)
  subgoal by (auto simp: final_def)
  subgoal by (auto simp: final_iff isSecO_def) .


(*transition*)
lemma validTrFinite:"Opt.lvalidFromS ss tr1 \<Longrightarrow> lfinite tr1"
  unfolding Opt.lvalidFromS_def Opt.lvalidS_def 
  by (auto,metis State.distinct(1) enat_ord_code(4) idiff_infinity llength_eq_infty_conv_lfinite)


lemma tr1_shape:"Opt.lvalidFromS ss tr1 \<Longrightarrow> lcompletedFromO ss tr1 \<Longrightarrow> tr1 = [[ss, ss']]"  
  unfolding Opt.lcompletedFrom_def apply(erule impE)
  subgoal by(simp add: validTrFinite)
  apply(frule validTrFinite)
  unfolding Opt.lvalidFromS_def Opt.lvalidS_def final_iff 
  apply(cases tr1, auto split: if_splits)
  subgoal for tr1' 
    apply(unfold nth_list_of[symmetric, of tr1'])
    apply(unfold nth_list_of[symmetric, of "(ss $ tr1')", unfolded lfinite_LCons])
    apply(unfold length_list_of[symmetric])
    apply(cases tr1', simp)
    subgoal premises p 
      using p apply-apply(erule allE[of _ 0], simp split: if_splits, metis llist_of.simps(1) llist_of_list_of)
      using p apply-by(erule allE[of _ 1], simp split: if_splits) . .


lemma tr1_shape':"s1 = ss \<Longrightarrow> Opt.lvalidFromS s1 tr1 \<Longrightarrow> lcompletedFromO s1 tr1 \<Longrightarrow> tr1 = [[ss, ss']]"  
  using tr1_shape by auto

(*Systems are relatively insecure*)
proposition "lrsecure"
  unfolding lrsecure_def2
  apply(intro allI impI, elim conjE)
  apply(rule exI[of _ "ss"],rule exI[of _ "[[ss, ss']]"])
  apply(rule exI[of _ "ss"],rule exI[of _ "[[ss, ss']]"])
  by(frule tr1_shape', simp_all)+


(*Unwinding**)

lemma validSS:"Opt.validS [ss, ss']" unfolding Opt.validS_def by auto
lemma validSS_van:"Van.validS [ss, ss']" unfolding Van.validS_def by auto

lemma reachOs:"reachO ss" using Opt.reach.Istate by auto
lemma reachVs:"reachV ss" using Van.reach.Istate by auto
lemma reachO':"reachO ss'" using Opt.validS_reach[of "[ss, ss']", OF _ validSS] by auto
lemma reachV':"reachV ss'" using Van.validS_reach[of "[ss, ss']", OF _ validSS_van] by auto

lemma impE_eq:"x = x \<longrightarrow> Q \<Longrightarrow> (Q \<Longrightarrow> Rs) \<Longrightarrow> Rs" by auto

lemma isSecOs:"isSecO ss" unfolding isSecO_def by auto
lemma neq_Sec:"\<not>eqSec ss ss" unfolding eqSec_def isSecO_def isSecV_def by auto

lemma statOs: "(sstatO' Eq ss ss) = Eq" unfolding sstatO'_def by auto




lemma noUnwind: shows init: "\<Delta> \<infinity> \<infinity> \<infinity> ss ss Eq ss ss Eq \<Longrightarrow> unwindCond \<Delta> \<Longrightarrow> False"
  subgoal premises unwind using unwind(2)[unfolded unwindCond_def]
  (*step1*)
  apply-apply(erule allE[of _ "\<infinity>"],erule allE[of _ "\<infinity>"],erule allE[of _ "\<infinity>"])
  apply(erule allE[of _ "ss"], erule allE[of _ "ss"])
  apply(erule allE[of _ "Eq"])
  apply(erule allE[of _ "ss"], erule allE[of _ "ss"])
  apply(erule allE[of _ "Eq"], erule impE)
  subgoal using reachOs reachVs unwind(1) by auto
  apply(elim conjE disjE impE_eq)
  (*Proact*)
  subgoal apply(elim exE conjE, unfold proact_def, elim disjE)
    (************************)
    (*move 1 and next unwind*)
    (************************)
    subgoal for v unfolding move_1_def apply (simp split: if_splits)
      using unwind(2)[unfolded unwindCond_def]
      apply-apply(erule allE[of _ "v"],erule allE[of _ "\<infinity>"],erule allE[of _ "\<infinity>"])
      apply(erule allE[of _ "ss"], erule allE[of _ "ss"])
      apply(erule allE[of _ "Eq"])
      apply(erule allE[of _ "ss'"], erule allE[of _ "ss"])
      apply(erule allE[of _ "Eq"], erule impE)
      subgoal using reachOs reachVs reachV' unwind(1) by auto
      apply(elim conjE disjE impE_eq)
      (*Proact*)
      subgoal apply(elim exE conjE, unfold proact_def, elim disjE)
        (*move 1 not possible*)
        subgoal for v unfolding move_1_def by (simp split: if_splits) 
        (*Move 2 step*)
        subgoal for v' unfolding move_2_def apply (simp split: if_splits)
          using unwind(2)[unfolded unwindCond_def]
          apply-apply(erule allE[of _ "v'"],erule allE[of _ "\<infinity>"],erule allE[of _ "\<infinity>"])
          apply(erule allE[of _ "ss"], erule allE[of _ "ss"])
          apply(erule allE[of _ "Eq"])
          apply(erule allE[of _ "ss'"], erule allE[of _ "ss'"])
          apply(erule allE[of _ "Eq"], erule impE)
          subgoal using reachOs reachVs reachV' reachO' by auto
          apply(elim conjE disjE impE_eq)
          (*proact not possible*)    
          subgoal by(unfold proact_def, auto simp: move_1_def move_2_def move_12_def)
          (*React*)
          subgoal unfolding react_def match1_def match1_1_def match1_12_def 
              apply(elim conjE impE, simp)
            by(erule allE[of _ ss'], auto simp: neq_Sec isSecOs) .
        (*move12 not possible*)
        subgoal unfolding move_12_def by auto .
        (*react not possible*)
        unfolding react_def match1_def match1_1_def match1_12_def 
        apply(elim conjE impE, simp) by(erule allE[of _ ss'], auto simp: neq_Sec isSecOs) 

    (************************)
    (*move 2 and next unwind*)
    (************************)
    subgoal for v unfolding move_2_def apply (simp split: if_splits)
      using unwind(2)[unfolded unwindCond_def]
      apply-apply(erule allE[of _ "v"],erule allE[of _ "\<infinity>"],erule allE[of _ "\<infinity>"])
      apply(erule allE[of _ "ss"], erule allE[of _ "ss"])
      apply(erule allE[of _ "Eq"])
      apply(erule allE[of _ "ss"], erule allE[of _ "ss'"])
      apply(erule allE[of _ "Eq"], erule impE)
      subgoal using reachOs reachVs reachV' unwind(1) by auto
      apply(elim conjE disjE impE_eq)
      (*Proact*)
      subgoal apply(elim exE conjE, unfold proact_def, elim disjE)
        (*move 1 step*)
        subgoal for v' unfolding move_1_def apply (simp split: if_splits)
          using unwind(2)[unfolded unwindCond_def]
          apply-apply(erule allE[of _ "v'"],erule allE[of _ "\<infinity>"],erule allE[of _ "\<infinity>"])
          apply(erule allE[of _ "ss"], erule allE[of _ "ss"])
          apply(erule allE[of _ "Eq"])
          apply(erule allE[of _ "ss'"], erule allE[of _ "ss'"])
          apply(erule allE[of _ "Eq"], erule impE)
          subgoal using reachOs reachVs reachV' reachO' by auto
          apply(elim conjE disjE impE_eq)
          (*proact not possible*)    
          subgoal by(auto simp: proact_def move_1_def move_2_def move_12_def)
          (*React*)
          subgoal unfolding react_def match1_def match1_1_def match1_12_def 
              apply(elim conjE impE, simp)
            by(erule allE[of _ ss'], auto simp: neq_Sec isSecOs) .
        (*Move 2 not possible*)
        subgoal for v unfolding move_2_def by (simp split: if_splits) 
        (*move12 not possible*)
        subgoal unfolding move_12_def by auto .
        (*react not possible*)
        unfolding react_def match1_def match1_1_def match1_12_def 
        apply(elim conjE impE, simp) by(erule allE[of _ ss'], auto simp: neq_Sec isSecOs) 

    (************************)
    (*move 12*)
    (************************)
      subgoal for v unfolding move_12_def apply (simp split: if_splits)
      using unwind(2)[unfolded unwindCond_def]
      apply-apply(erule allE[of _ "v"],erule allE[of _ "\<infinity>"],erule allE[of _ "\<infinity>"])
      apply(erule allE[of _ "ss"], erule allE[of _ "ss"])
      apply(erule allE[of _ "Eq"])
      apply(erule allE[of _ "ss'"], erule allE[of _ "ss'"])
      apply(erule allE[of _ "Eq"], erule impE)
      subgoal using reachOs reachVs reachV' reachO' by (auto simp: statOs)
      apply(elim conjE disjE impE_eq)
      (*proact not possible*)    
      subgoal by(auto simp: proact_def move_1_def move_2_def move_12_def)
      (*react*)
      subgoal unfolding react_def match1_def match1_12_def match1_1_def apply(elim conjE impE, simp)
              by(erule allE[of _ ss'], auto simp: neq_Sec isSecOs) . .
  (*React*)
  subgoal unfolding react_def match1_def apply(elim conjE impE, simp)
    by(erule allE[of _ ss'], auto simp: neq_Sec isSecOs) . .

lemma incomplete_inf:
    assumes init: "initCond \<Delta>"
    and unwind: "unwindCond \<Delta>"
  shows "False"
  using noUnwind assms[unfolded initCond_def] by auto

end
