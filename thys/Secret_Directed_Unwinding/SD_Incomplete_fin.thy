section \<open>Secret Directed (Finatary) Unwinding Incompleteness example\<close>

text \<open>Demonstrating a counterexample which is secure but fails in the finatary unwinding\<close>
theory SD_Incomplete_fin
  imports SD_Unwinding_fin
begin


no_notation bot ("\<bottom>")

(* This will be used for non-informative entities, e.g., a noninformative output: *)
abbreviation noninform ("\<bottom>") where "\<bottom> \<equiv> undefined"



datatype State = s\<^sub>0 | s\<^sub>0' | s\<^sub>1 | s\<^sub>1' | s\<^sub>2 
type_synonym secret = "State"

fun transit::"State \<Rightarrow> State \<Rightarrow> bool"(infix "\<rightarrow>I" 55) where 
  "transit s s' = 

      (if (s = s\<^sub>0 \<and> s' = s\<^sub>1) \<or>
          (s = s\<^sub>1 \<and> s' = s\<^sub>2) \<or>
          (s = s\<^sub>0' \<and> s' = s\<^sub>1') \<or>
          (s = s\<^sub>1' \<and> s' = s\<^sub>2) then True 
      else False)"
(*s0 \<rightarrow> s1 \<rightarrow> s2*)
lemma transit_s0_s1:"s\<^sub>0 \<rightarrow>I s\<^sub>1" by auto
lemma transit_s1_s2:"s\<^sub>1 \<rightarrow>I s\<^sub>2" by auto


(*s0' \<rightarrow> s1' \<rightarrow> s2*)
lemma transit_s0'_s1':"s\<^sub>0' \<rightarrow>I s\<^sub>1'" by auto
lemma transit_s1'_s2:"s\<^sub>1' \<rightarrow>I s\<^sub>2" by auto

lemma transit_iff:"s \<rightarrow>I s' \<longleftrightarrow> (s = s\<^sub>0 \<and> s' = s\<^sub>1) \<or>
          (s = s\<^sub>1 \<and> s' = s\<^sub>2) \<or>
          (s = s\<^sub>0' \<and> s' = s\<^sub>1') \<or>
          (s = s\<^sub>1' \<and> s' = s\<^sub>2)" by auto

definition "final x \<equiv> \<forall>y. \<not> (\<rightarrow>I) x y"

lemma final_s2[simp]:"final s\<^sub>2" unfolding final_def transit_iff by auto

lemma final_iff: "final s \<longleftrightarrow> s = s\<^sub>2" unfolding final_def transit_iff by (auto,metis State.exhaust)

text \<open>Vanilla-semantics system model\<close>
type_synonym stateV = State
fun validTransV where "validTransV (s,s') = s \<rightarrow>I s'"

text \<open>Secrets at initial states, interaction at everywhere besides final (i.e. s2)\<close>
fun isIntV :: "stateV \<Rightarrow> bool" where "isIntV s = (s \<noteq> s\<^sub>2)"

(*need:
  1) getAct s\<^sub>0 = getAct s\<^sub>0' 
  2) getObs s\<^sub>0 \<noteq> getObs s\<^sub>0'
  3) getAct s\<^sub>1 \<noteq> getAct s\<^sub>1' *)
fun getIntV :: "stateV \<Rightarrow> nat \<times> nat" where 
"getIntV s = 
 (case s of 
    s\<^sub>0  \<Rightarrow> (1, 0)
   |s\<^sub>0' \<Rightarrow> (1, 1)
   |s\<^sub>1  \<Rightarrow> (0, \<bottom>)
   |s\<^sub>1' \<Rightarrow> (1, \<bottom>)
   |_ \<Rightarrow> (\<bottom>,\<bottom>)
 )"

definition isSecV :: "stateV \<Rightarrow> bool" where "isSecV s = (s \<in> {s\<^sub>0, s\<^sub>0'})"
fun getSecV :: "stateV \<Rightarrow> secret" where "getSecV s = s"

lemma getSecV_neq: "getSecV s\<^sub>0 \<noteq> getSecV s\<^sub>0'" by auto

(* *)

text \<open>The optimization-enhanced system model\<close>

type_synonym stateO = State
fun validTransO where "validTransO (s,s') = s \<rightarrow>I s'"

text \<open>Secrets and interaction at initial states\<close>
fun isIntO :: "stateO \<Rightarrow> bool" where "isIntO s = (s \<in> {s\<^sub>0, s\<^sub>0'})"


(*need:
  1) getAct s\<^sub>0 = getAct s\<^sub>0' 
  2) getObs s\<^sub>0 \<noteq> getObs s\<^sub>0'
  3) getAct s\<^sub>1 \<noteq> getAct s\<^sub>1' *)
fun getIntO :: "stateO \<Rightarrow> nat \<times> nat" where 
"getIntO s = 
 (case s of 
    s\<^sub>0  \<Rightarrow> (1, 0)
   |s\<^sub>0' \<Rightarrow> (1, 1)
   |_ \<Rightarrow> (\<bottom>,\<bottom>)
 )"

definition isSecO :: "stateO \<Rightarrow> bool" where "isSecO s = (s \<in> {s\<^sub>0, s\<^sub>0'})"
lemma isSec0[simp]:"isSecO s\<^sub>0" unfolding isSecO_def by auto
lemma isSec1[simp]:"\<not>isSecO s\<^sub>1" unfolding isSecO_def by auto

lemma isSec0'[simp]:"isSecO s\<^sub>0'" unfolding isSecO_def by auto
lemma isSec1'[simp]:"\<not>isSecO s\<^sub>1'" unfolding isSecO_def by auto

fun getSecO :: "stateO \<Rightarrow> secret" where "getSecO s = s"

text \<open>corrState\<close>
fun corrState :: "stateV \<Rightarrow> stateO \<Rightarrow> bool" where 
"corrState cfgO cfgA = True"

interpretation Rel_Sec 
  where validTransV = validTransV and istateV = "\<lambda>s. s = s\<^sub>0 \<or> s = s\<^sub>0'" 
  and finalV = final 
  and isSecV = isSecV and getSecV = getSecV
  and isIntV = isIntV and getIntV = getIntV
  (* *)
  and validTransO = validTransO and istateO = "\<lambda>s. s = s\<^sub>0 \<or> s = s\<^sub>0'"
  and finalO = final
  and isSecO = isSecO  and getSecO = getSecO
  and isIntO = isIntO and getIntO = getIntO
  and corrState = corrState 
  apply(unfold_locales)
  subgoal by (auto simp: final_def)
  subgoal by (auto simp: final_iff)
  subgoal by (auto simp: final_iff isSecV_def)
  subgoal by (auto simp: final_def)
  subgoal by (auto simp: final_iff)
  subgoal by (auto simp: final_iff isSecO_def) .


lemma getAct0:"getActO s\<^sub>0 = getActO s\<^sub>0'" unfolding Opt.getAct_def by auto
lemma getObs0:"getObsO s\<^sub>0 \<noteq> getObsO s\<^sub>0'" unfolding Opt.getObs_def by auto


lemma getActV0:"getActV s\<^sub>0 = getActV s\<^sub>0'" unfolding Van.getAct_def by auto
lemma getObsV0:"getObsV s\<^sub>0 \<noteq> getObsV s\<^sub>0'" unfolding Van.getObs_def by auto


lemma getAct1:"getActV s\<^sub>1 \<noteq> getActV s\<^sub>1'" unfolding Van.getAct_def by auto

(*transition*)
lemma validFromO:"Opt.validFromS s\<^sub>0 [s\<^sub>0, s\<^sub>1, s\<^sub>2]" unfolding Opt.validFromS_def Opt.validS_def apply clarsimp
  by (metis less_Suc0 not_less_less_Suc_eq nth_Cons_0
      nth_Cons_Suc)

lemma validFromO':"Opt.validFromS s\<^sub>0' [s\<^sub>0', s\<^sub>1', s\<^sub>2]" unfolding Opt.validFromS_def Opt.validS_def apply clarsimp
  by (metis less_Suc0 not_less_less_Suc_eq nth_Cons_0
      nth_Cons_Suc)


(*infer traces*)
lemma tr1_shape_s0_aux:"Van.validFromS s\<^sub>0 tr1 \<Longrightarrow> completedFromO s\<^sub>0 tr1 \<Longrightarrow> tr1 = [s\<^sub>0, s\<^sub>1, s\<^sub>2]"  
  unfolding completedFromO_def apply(erule disjE)
  subgoal by(simp add: final_iff)
  unfolding Van.validFromS_def Van.validS_def final_iff 
  apply(cases tr1, auto split: if_splits) 
  subgoal for tr1' apply(cases tr1', auto split: if_splits, force+)
    subgoal premises p for a tr1''
      using p apply-apply(erule allE[of _ 0], auto)
      using p apply-apply(erule allE[of _ 1], auto)
      using p apply-apply(erule allE[of _ 2], auto)
      by (metis Suc_lessI gr0I length_0_conv length_Suc_conv nth_Cons_0) . .

lemma tr1_shape_s0:"s1 = s\<^sub>0 \<Longrightarrow> Van.validFromS s1 tr1 \<Longrightarrow> completedFromO s1 tr1 \<Longrightarrow> tr1 = [s\<^sub>0, s\<^sub>1, s\<^sub>2]"  
  using tr1_shape_s0_aux by auto


lemma tr1_shape_s0'_aux:"Van.validFromS s\<^sub>0' tr1 \<Longrightarrow> completedFromO s\<^sub>0' tr1 \<Longrightarrow> tr1 = [s\<^sub>0', s\<^sub>1', s\<^sub>2]"  
  unfolding completedFromO_def apply(erule disjE)
  subgoal by(simp add: final_iff)
  unfolding Van.validFromS_def Van.validS_def final_iff
  apply(cases tr1, auto split: if_splits) 
  subgoal for tr1' apply(cases tr1', auto split: if_splits, force+)
    subgoal premises p for a tr1''
      using p apply-apply(erule allE[of _ 0], auto)
      using p apply-apply(erule allE[of _ 1], auto)
      using p apply-apply(erule allE[of _ 2], auto)
      by (metis Suc_lessI gr0I length_0_conv length_Suc_conv nth_Cons_0) . .

lemma tr1_shape_s0':"s1 = s\<^sub>0' \<Longrightarrow> Van.validFromS s1 tr1 \<Longrightarrow> completedFromO s1 tr1 \<Longrightarrow> tr1 = [s\<^sub>0', s\<^sub>1', s\<^sub>2]"  
  using tr1_shape_s0'_aux by auto

(*Systems are relatively insecure*)
proposition "\<not>rsecure"
  unfolding rsecure_def2 unfolding not_all not_imp
  apply(rule exI[of _ s\<^sub>0],rule exI[of _ "[s\<^sub>0, s\<^sub>1, s\<^sub>2]"])
  apply(rule exI[of _ s\<^sub>0'],rule exI[of _ "[s\<^sub>0', s\<^sub>1', s\<^sub>2]"])
  apply(intro conjI, simp_all add: validFromO validFromO' getAct0 getObs0)
  apply(intro allI)
  subgoal for sv1 apply(cases sv1, simp_all,intro allI impI)
     (*sv1 = s\<^sub>0*)
     subgoal for trv1 sv2 apply(cases sv2, simp_all, intro allI impI)
       (*sv2 = s\<^sub>0*)
       subgoal for trv2 
         apply(frule tr1_shape_s0[of _ trv1], simp_all)
         by(frule tr1_shape_s0[of _ trv2], simp_all)
       apply(intro allI impI)
       subgoal for trv2 
         apply(frule tr1_shape_s0[of _ trv1], simp_all)
         by(frule tr1_shape_s0'[of _ trv2], simp_all add: getAct1) .
     (*sv1 = s\<^sub>0' *)
     apply(intro allI impI)
     subgoal for trv1 sv2 apply(cases sv2, simp_all, intro allI impI)
       (*sv2 = s\<^sub>0*)
       subgoal for trv2 
         apply(frule tr1_shape_s0'[of _ trv1], simp_all)
         apply(frule tr1_shape_s0[of _ trv2], simp_all)
         using getAct1 by auto
       apply(intro allI impI)
       subgoal for trv2 
         apply(frule tr1_shape_s0'[of _ trv1], simp_all)
         by(frule tr1_shape_s0'[of _ trv2], simp_all add: getAct1) . . .


 thm unwindSD_rsecure





(*infer traces*)
lemma tr1_shape_s0_auxOpt:"Opt.validFromS s\<^sub>0 tr1 \<Longrightarrow> completedFromO s\<^sub>0 tr1 \<Longrightarrow> tr1 = [s\<^sub>0, s\<^sub>1, s\<^sub>2]"  
  unfolding completedFromO_def apply(erule disjE)
  subgoal by(simp add: final_iff)
  unfolding Opt.validFromS_def Opt.validS_def final_iff
  apply(cases tr1, auto split: if_splits) 
  subgoal for tr1' apply(cases tr1', auto split: if_splits, force+)
    subgoal premises p for a tr1''
      using p apply-apply(erule allE[of _ 0], auto)
      using p apply-apply(erule allE[of _ 1], auto)
      using p apply-apply(erule allE[of _ 2], auto)
      by (metis Suc_lessI gr0I length_0_conv length_Suc_conv nth_Cons_0) . .

lemma tr1_shape_s0_Opt:"s1 = s\<^sub>0 \<Longrightarrow> Opt.validFromS s1 tr1 \<Longrightarrow> completedFromO s1 tr1 \<Longrightarrow> tr1 = [s\<^sub>0, s\<^sub>1, s\<^sub>2]"  
  using tr1_shape_s0_auxOpt by auto


lemma tr1_shape_s0'_auxOpt:"Opt.validFromS s\<^sub>0' tr1 \<Longrightarrow> completedFromO s\<^sub>0' tr1 \<Longrightarrow> tr1 = [s\<^sub>0', s\<^sub>1', s\<^sub>2]"  
  unfolding completedFromO_def apply(erule disjE)
  subgoal by(simp add: final_iff)
  unfolding Opt.validFromS_def Opt.validS_def final_iff
  apply(cases tr1, auto split: if_splits) 
  subgoal for tr1' apply(cases tr1', auto split: if_splits, force+)
    subgoal premises p for a tr1''
      using p apply-apply(erule allE[of _ 0], auto)
      using p apply-apply(erule allE[of _ 1], auto)
      using p apply-apply(erule allE[of _ 2], auto)
      by (metis Suc_lessI gr0I length_0_conv length_Suc_conv nth_Cons_0) . .

lemma tr1_shape_s0'_Opt:"s1 = s\<^sub>0' \<Longrightarrow> Opt.validFromS s1 tr1 \<Longrightarrow> completedFromO s1 tr1 \<Longrightarrow> tr1 = [s\<^sub>0', s\<^sub>1', s\<^sub>2]"  
  using tr1_shape_s0'_auxOpt by auto

lemma OptS[simp]:"Opt.S [s\<^sub>0, s\<^sub>1, s\<^sub>2] = [s\<^sub>0]" unfolding Opt.S_def by auto
lemma OptS'[simp]:"Opt.S [s\<^sub>0', s\<^sub>1', s\<^sub>2] = [s\<^sub>0']" unfolding Opt.S_def by auto


lemma reachO0:"reachO s\<^sub>0" using Opt.reach.Istate by auto
lemma reachV0:"reachV s\<^sub>0" using Van.reach.Istate by auto
lemma reachO0':"reachO s\<^sub>0'" using Opt.reach.Istate by auto
lemma reachV0':"reachV s\<^sub>0'" using Van.reach.Istate by auto


(*incompleteness*)
lemma SD_incomplete:
  assumes
"s1 = s\<^sub>0 \<or> s1 = s\<^sub>0'"
"Opt.validFromS s1 tr1"
"completedFromO s1 tr1"
"s4 = s\<^sub>0 \<or> s4 = s\<^sub>0'"
"Opt.validFromS s4 tr2"
"completedFromO s4 tr2"
"Opt.A tr1 = Opt.A tr2"
"Opt.O tr1 \<noteq> Opt.O tr2" 
"\<And>sv1 sv2.
    sv1 = s\<^sub>0 \<or> sv1 = s\<^sub>0' \<Longrightarrow>
    corrState sv1 s1 \<Longrightarrow> sv2 = s\<^sub>0 \<or> sv2 = s\<^sub>0' \<Longrightarrow> corrState sv2 s4 \<Longrightarrow> \<Gamma> sv1 (Opt.S tr1) sv2 (Opt.S tr2)"
"unwindSDCond \<Gamma>"
shows "False"
  using assms(9)[OF assms(1) _ assms(4), simplified] assms(1,4)
  apply-apply(elim disjE)
  subgoal using tr1_shape_s0_Opt[OF _ assms(2,3), simplified]
                tr1_shape_s0_Opt[OF _ assms(5,6), simplified]
                assms(7,8) by simp
  
  subgoal using tr1_shape_s0_Opt[OF _ assms(2,3), simplified]
                tr1_shape_s0'_Opt[OF _ assms(5,6), simplified]
                assms(7,8) apply simp
    using assms(10)[unfolded unwindSDCond_def]
    apply-apply(erule allE[of _ "s\<^sub>0"], erule allE[of _ "[s\<^sub>0]"])   
    apply-apply(erule allE[of _ "s\<^sub>0'"], elim allE[of _ "[s\<^sub>0']"] impE)
    subgoal using reachV0' reachV0 by auto
    by (auto simp: getActV0 getObsV0)

  subgoal using tr1_shape_s0'_Opt[OF _ assms(2,3), simplified]
                tr1_shape_s0_Opt[OF _ assms(5,6), simplified]
                assms(7,8) apply simp
    using assms(10)[unfolded unwindSDCond_def]
    apply-apply(erule allE[of _ "s\<^sub>0'"], erule allE[of _ "[s\<^sub>0']"])   
    apply-apply(erule allE[of _ "s\<^sub>0"], elim allE[of _ "[s\<^sub>0]"] impE)
    subgoal using reachV0' reachV0 by auto
    using getActV0 getObsV0 by auto
  subgoal using tr1_shape_s0'_Opt[OF _ assms(2,3), simplified]
                tr1_shape_s0'_Opt[OF _ assms(5,6), simplified]
                assms(7,8) by simp . 


end
