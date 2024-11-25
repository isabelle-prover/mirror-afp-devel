section \<open>Unwinding Proof Method for Relative Security\<close>

text \<open> This theory formalizes the notion of unwinding for relative security, 
and proves its soundness.  \<close>

theory Unwinding
imports Relative_Security 
begin


subsection \<open> The types and operators underlying unwinding: status, matching operators, etc.  \<close>

context Rel_Sec
begin 

(* Observation status *)
datatype status = Eq | Diff 

fun newStat :: "status \<Rightarrow> bool \<times> 'a \<Rightarrow> bool \<times> 'a \<Rightarrow> status" where 
 "newStat Eq (True,a) (True,a') = (if a = a' then Eq else Diff)"
|"newStat stat _ _ = stat"

definition "sstatO' statO sv1 sv2 = newStat statO (isIntV sv1, getObsV sv1) (isIntV sv2, getObsV sv2)"
definition "sstatA' statA s1 s2 = newStat statA (isIntO s1, getObsO s1) (isIntO s2, getObsO s2)"

lemma newStat_EqI: 
  assumes \<open>R = S\<close>
    shows \<open>newStat Eq (P, R) (Q, S) = Eq\<close>
  apply (cases P)  
  apply (metis assms newStat.simps(1) newStat.simps(4))
  by (cases Q) auto

lemma newStat_diff:"newStat stat r r = Diff \<Longrightarrow> stat = Diff"
  by (metis newStat.elims newStat.simps(1))


(* *)

definition initCond :: 
"(enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'stateO \<Rightarrow> 'stateO \<Rightarrow> status \<Rightarrow> 'stateV \<Rightarrow> 'stateV \<Rightarrow> status \<Rightarrow> bool) \<Rightarrow> bool" where 
"initCond \<Delta> \<equiv> \<forall>s1 s2. 
   istateO s1 \<and> istateO s2 
   \<longrightarrow> 
   (\<exists>sv1 sv2. istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 
            \<and> \<Delta> \<infinity> \<infinity> \<infinity> s1 s2 Eq sv1 sv2 Eq)"


(* *)

definition "match1_1 \<Delta> w1 w2 s1 s1' s2 statA sv1 sv2 statO \<equiv> 
  \<exists>sv1'. validTransV (sv1,sv1') \<and>        
     \<Delta> \<infinity> w1 w2 s1' s2 statA sv1' sv2 statO"

definition "match1_12 \<Delta> w1 w2 s1 s1' s2 statA sv1 sv2 statO \<equiv> 
  (\<exists>sv1' sv2'. 
    let statO' = sstatO' statO sv1 sv2 in 
    validTransV (sv1,sv1') \<and> 
    validTransV (sv2,sv2') \<and>      
    \<Delta> \<infinity> w1 w2 s1' s2 statA sv1' sv2' statO')"

definition "match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<equiv> 
  \<not> isIntO s1 \<longrightarrow> 
   (\<forall>s1'. validTransO (s1,s1') 
      \<longrightarrow> 
      (\<exists>w1'< w1. \<exists>w2'< w2. \<not> isSecO s1 \<and> \<Delta> \<infinity> w1' w2' s1' s2 statA sv1 sv2 statO) \<or> 
      (\<exists>w2'< w2. eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> match1_1 \<Delta> \<infinity> w2' s1 s1' s2 statA sv1 sv2 statO) \<or> 
      (eqSec sv1 s1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> match1_12 \<Delta> \<infinity> \<infinity> s1 s1' s2 statA sv1 sv2 statO))"

lemmas match1_defs = match1_def match1_1_def match1_12_def

lemma match1_1_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match1_1 \<Delta> w1 w2 s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> 
  match1_1 \<Delta>' w1 w2 s1 s1' s2 statA sv1 sv2 statO"
unfolding le_fun_def match1_1_def by auto

lemma match1_12_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match1_12 \<Delta> w1 w2 s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> 
 match1_12 \<Delta>' w1 w2 s1 s1' s2 statA sv1 sv2 statO"
unfolding le_fun_def match1_12_def by fastforce

lemma match1_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> match1 \<Delta>' w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding match1_def apply clarify subgoal for s1' apply(erule allE[of _ s1'])
using match1_1_mono[OF assms, of _ _ s1 s1' s2 statA sv1 sv2 statO] 
      match1_12_mono[OF assms, of _ _ s1 s1' s2 statA sv1 sv2 statO] 
      assms[unfolded le_fun_def, rule_format, of _ _ _ s1' s2 statA sv1 sv2 statO]
by fastforce .

(*  *)

definition "match2_1 \<Delta> w1 w2 s1 s2 s2' statA sv1 sv2 statO \<equiv> 
  \<exists>sv2'. validTransV (sv2,sv2') \<and>   
        \<Delta> \<infinity> w1 w2 s1 s2' statA sv1 sv2' statO"

definition "match2_12 \<Delta> w1 w2 s1 s2 s2' statA sv1 sv2 statO \<equiv> 
  \<exists>sv1' sv2'.   
    let statO' = sstatO' statO sv1 sv2 in 
    validTransV (sv1,sv1') \<and> 
    validTransV (sv2,sv2') \<and>         
    \<Delta> \<infinity> w1 w2 s1 s2' statA sv1' sv2' statO'"

definition "match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<equiv> 
  \<not> isIntO s2 \<longrightarrow>
  (\<forall>s2'. validTransO (s2,s2') 
     \<longrightarrow> 
     (\<exists>w1'< w1. \<exists>w2'< w2. \<not> isSecO s2 \<and> \<Delta> \<infinity> w1' w2' s1 s2' statA sv1 sv2 statO) \<or> 
     (\<exists>w1'< w1. eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> match2_1 \<Delta> w1' \<infinity> s1 s2 s2' statA sv1 sv2 statO) \<or>
     (\<not> isSecV sv1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and> match2_12 \<Delta> \<infinity> \<infinity> s1 s2 s2' statA sv1 sv2 statO))"

lemmas match2_defs = match2_def match2_1_def match2_12_def

lemma match2_1_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match2_1 \<Delta> w1 w2 s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> match2_1 \<Delta>' w1 w2 s1 s1' s2 statA sv1 sv2 statO"
unfolding le_fun_def match2_1_def by auto

lemma match2_12_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match2_12 \<Delta> w1 w2 s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> match2_12 \<Delta>' w1 w2 s1 s1' s2 statA sv1 sv2 statO"
unfolding le_fun_def match2_12_def by fastforce

lemma match2_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> match2 \<Delta>' w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding match2_def apply clarify subgoal for s2' apply(erule allE[of _ s2'])
using match2_1_mono[OF assms, of _ _ s1 s2 s2' statA sv1 sv2 statO] 
      match2_12_mono[OF assms, of _ _ s1 s2 s2' statA sv1 sv2 statO] 
      assms[unfolded le_fun_def, rule_format, of _ _ _ s1 s2' statA sv1 sv2 statO]
by fastforce .

(* *)

definition "match12_1 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<equiv> 
  \<exists>sv1'. validTransV (sv1,sv1') \<and>   
        \<Delta> \<infinity> w1 w2 s1' s2' statA' sv1' sv2 statO"

definition "match12_2 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<equiv> 
  \<exists>sv2'. validTransV (sv2,sv2') \<and>  
        \<Delta> \<infinity> w1 w2 s1' s2' statA' sv1 sv2' statO"

definition "match12_12 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<equiv> 
  \<exists>sv1' sv2'.  
    let statO' = sstatO' statO sv1 sv2 in 
    validTransV (sv1,sv1') \<and>   
    validTransV (sv2,sv2') \<and>  
    (statA' = Diff \<longrightarrow> statO' = Diff) \<and>       
    \<Delta> \<infinity> w1 w2 s1' s2' statA' sv1' sv2' statO'"

definition "match12 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<equiv> 
\<forall>s1' s2'. 
   let statA' = sstatA' statA s1 s2 in
   validTransO (s1,s1') \<and> 
   validTransO (s2,s2') \<and> 
   Opt.eqAct s1 s2 \<and> 
   isIntO s1 \<and> isIntO s2
   \<longrightarrow> 
   (\<exists>w1'< w1. \<exists>w2'< w2. \<not> isSecO s1 \<and> \<not> isSecO s2 \<and> (statA = statA' \<or> statO = Diff) \<and> 
       \<Delta> \<infinity> w1' w2' s1' s2' statA' sv1 sv2 statO)
   \<or> 
   (\<exists>w2'< w2. \<not> isSecO s2 \<and> eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> 
    (statA = statA' \<or> statO = Diff) \<and> 
    match12_1 \<Delta> \<infinity> w2' s1' s2' statA' sv1 sv2 statO)  
   \<or> 
   (\<exists>w1'< w1. \<not> isSecO s1 \<and> eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> 
    (statA = statA' \<or> statO = Diff) \<and> 
    match12_2 \<Delta> w1' \<infinity> s1' s2' statA' sv1 sv2 statO)  
   \<or> 
   (eqSec sv1 s1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and>   
    match12_12 \<Delta> \<infinity> \<infinity> s1' s2' statA' sv1 sv2 statO)"

lemmas match12_defs = match12_def match12_1_def match12_2_def match12_12_def

(* A sufficient critetion for match12, removing the assymmetric conditions 
and the isInt assumptions: *)
lemma match12_simpleI: 
assumes "\<And>s1' s2' statA'. 
   statA' = sstatA' statA s1 s2 \<Longrightarrow> 
   validTransO (s1,s1') \<Longrightarrow> 
   validTransO (s2,s2') \<Longrightarrow>
   Opt.eqAct s1 s2 \<Longrightarrow> 
   (\<exists>w1'< w1. \<exists>w2'< w2. \<not> isSecO s1 \<and> \<not> isSecO s2 \<and> (statA = statA' \<or> statO = Diff) \<and> 
      \<Delta> \<infinity> w1' w2' s1' s2' statA' sv1 sv2 statO)
   \<or> 
   (eqSec sv1 s1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and>   
    match12_12 \<Delta> \<infinity> \<infinity> s1' s2' statA' sv1 sv2 statO)"
shows "match12 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
using assms unfolding match12_def Let_def by blast

lemma match12_1_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match12_1 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<Longrightarrow> match12_1 \<Delta>' w1 w2 s1' s2' statA' sv1 sv2 statO"
unfolding le_fun_def match12_1_def by auto

lemma match12_2_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match12_2 \<Delta> w1 w2 s1 s2' statA' sv1 sv2 statO \<Longrightarrow> match12_2 \<Delta>' w1 w2 s1 s2' statA' sv1 sv2 statO"
unfolding le_fun_def match12_2_def by auto

lemma match12_12_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match12_12 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<Longrightarrow> match12_12 \<Delta>' w1 w2 s1' s2' statA' sv1 sv2 statO"
unfolding le_fun_def match12_12_def by fastforce

lemma match12_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "match12 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> match12 \<Delta>' w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding match12_def apply clarify subgoal for s1' s2' apply(erule allE[of _ s1']) apply(erule allE[of _ s2'])
using match12_1_mono[OF assms, of _ _ s1' s2' _ sv1 sv2 statO] 
      match12_2_mono[OF assms, of _ _ s1' s2' _ sv1 sv2 statO] 
      match12_12_mono[OF assms, of _ _ s1' s2' _ sv1 sv2 statO]
      assms[unfolded le_fun_def, rule_format, of _ _ _ s1' s2' 
       "sstatA' statA s1 s2" sv1 sv2 statO] 
apply simp by blast .

(* *)

definition "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<equiv> 
 match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO 
 \<and>
 match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO 
 \<and> 
 match12 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"

lemmas react_defs = match1_def match2_def match12_def
lemmas match_deep_defs = match1_defs match2_defs match12_defs

lemma match_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> react \<Delta>' w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding react_def using match1_mono[OF assms] match2_mono[OF assms] match12_mono[OF assms] by auto    

(* *)

definition "move_1 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<equiv> 
 \<exists>sv1'. validTransV (sv1,sv1') \<and>  
   \<Delta> w w1 w2 s1 s2 statA sv1' sv2 statO"

definition "move_2 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<equiv> 
 \<exists>sv2'. validTransV (sv2,sv2') \<and>    
   \<Delta> w w1 w2 s1 s2 statA sv1 sv2' statO"

definition "move_12 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<equiv> 
 \<exists>sv1' sv2'.  
   let statO' = sstatO' statO sv1 sv2 in 
   validTransV (sv1,sv1') \<and> validTransV (sv2,sv2') \<and>     
   \<Delta> w w1 w2 s1 s2 statA sv1' sv2' statO'" 

definition "proact \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<equiv> 
 (\<not> isSecV sv1 \<and> \<not> isIntV sv1 \<and> move_1 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO) 
 \<or> 
 (\<not> isSecV sv2 \<and> \<not> isIntV sv2 \<and> move_2 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO) 
 \<or> 
 (\<not> isSecV sv1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> move_12 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO)"

lemmas proact_defs = proact_def move_1_def move_2_def move_12_def

lemma move_1_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> move_1 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> move_1 \<Delta>' w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding le_fun_def move_1_def by auto

lemma move_2_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> move_2 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> move_2 \<Delta>' w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding le_fun_def move_2_def by auto

lemma move_12_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> move_12 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> move_12 \<Delta>' w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding le_fun_def move_12_def by fastforce

lemma proact_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "proact \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> proact \<Delta>' w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding proact_def using move_1_mono[OF assms] move_2_mono[OF assms] move_12_mono[OF assms] by auto


subsection \<open> The definition of unwinding \<close>

definition unwindCond :: 
"(enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'stateO \<Rightarrow> 'stateO \<Rightarrow> status \<Rightarrow> 'stateV \<Rightarrow> 'stateV \<Rightarrow> status \<Rightarrow> bool) \<Rightarrow> bool" 
where 
"unwindCond \<Delta> \<equiv> \<forall>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO 
 \<longrightarrow> 
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2) 
 \<and> 
 (statA = Eq \<longrightarrow> (isIntO s1 \<longleftrightarrow> isIntO s2))
 \<and>
 ((\<exists>v < w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) 
  \<or> 
  react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO
 )"

(* *)

(* A sufficient criterion for unwindCond, removing the proact part: *)
lemma unwindCond_simpleI:
assumes  
 "\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2)"
and 
"\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> statA = Eq 
 \<Longrightarrow>
 isIntO s1 \<longleftrightarrow> isIntO s2"
and 
"\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
shows "unwindCond \<Delta>"
using assms unfolding unwindCond_def by auto



subsection \<open> The soundness of unwinding \<close>

text \<open> The proof of soundness for general unwinding is significantly 
more elaborate than that for the finitary case.  \<close>

definition "\<psi> s1 tr1 s2 tr2 statO sv1 trv1 sv2 trv2 \<equiv> 
  trv1 \<noteq> [] \<and> trv2 \<noteq> [] \<and> 
  Van.validFromS sv1 trv1 \<and> 
  Van.validFromS sv2 trv2 \<and> 
  (finalV (lastt sv1 trv1) \<longleftrightarrow> finalO (lastt s1 tr1)) \<and> (finalV (lastt sv2 trv2) \<longleftrightarrow> finalO (lastt s2 tr2)) \<and> 
  Van.S trv1 = Opt.S tr1 \<and> Van.S trv2 = Opt.S tr2 \<and> 
  Van.A trv1 = Van.A trv2 \<and> 
  (statO = Eq \<and> Opt.O tr1 \<noteq> Opt.O tr2 \<longrightarrow> Van.O trv1 \<noteq> Van.O trv2)"

lemma \<psi>_completedFrom: "completedFromO s1 tr1 \<Longrightarrow> completedFromO s2 tr2 \<Longrightarrow> 
  \<psi> s1 tr1 s2 tr2 statO sv1 trv1 sv2 trv2 
  \<Longrightarrow> completedFromV sv1 trv1 \<and> completedFromV sv2 trv2"
unfolding \<psi>_def Opt.completedFrom_def Van.completedFrom_def lastt_def
by presburger

lemma completedFromO_lastt: "completedFromO s1 tr1 \<Longrightarrow> finalO (lastt s1 tr1)"
unfolding Opt.completedFrom_def lastt_def by auto

(* A sufficient criterion that prepares the way for incremental (unwinding) proof
of relative security: *)

lemma rsecure_strong:
assumes 
"\<And>s1 tr1 s2 tr2.
   istateO s1 \<and> Opt.validFromS s1 tr1 \<and> completedFromO s1 tr1 \<and> 
   istateO s2 \<and> Opt.validFromS s2 tr2 \<and> completedFromO s2 tr2 \<and> 
   Opt.A tr1 = Opt.A tr2 
   \<Longrightarrow> 
   \<exists>sv1 trv1 sv2 trv2. 
     istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 \<and> 
     \<psi> s1 tr1 s2 tr2 Eq sv1 trv1 sv2 trv2" 
shows rsecure
unfolding rsecure_def2 apply safe
subgoal for s1 tr1 s2 tr2
using assms[of s1 tr1 s2 tr2] 
using \<psi>_completedFrom \<psi>_def completedFromO_lastt apply clarsimp by metis .

(* The mode is not needed in the inductive case... *)
proposition unwindCond_ex_\<psi>:
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" and stat: "(statA = Diff \<longrightarrow> statO = Diff)" 
and v: "Opt.validFromS s1 tr1" "Opt.completedFrom s1 tr1" "Opt.validFromS s2 tr2" "Opt.completedFrom s2 tr2"
and tr14: "Opt.A tr1 = Opt.A tr2" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
shows "\<exists>trv1 trv2. \<psi> s1 tr1 s2 tr2 statO sv1 trv1 sv2 trv2"
using assms(2-)  
proof(induction "length tr1 + length tr2" w 
   arbitrary: w1 w2 s1 s2 statA sv1 sv2 statO tr1 tr2 rule: less2_induct')
  case (less w tr1 tr2 w1 w2 s1 s2 statA sv1 sv2 statO)
  note ok = `statA = Diff \<longrightarrow> statO = Diff` 
  note \<Delta> = `\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO`
  note A34 = `Opt.A tr1 = Opt.A tr2`
  note r34 = less.prems(8,9) note r12 = less.prems(10,11)
  note r = r34 r12 
  note r3 = r34(1) note r4 = r34(2) note r1 = r12(1) note r2 = r12(2)

  have i34: "statA = Eq \<longrightarrow> isIntO s1 = isIntO s2"
  and f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2"
    using \<Delta> unwind[unfolded unwindCond_def] r by auto

  have proact_match: "(\<exists>v<w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
    using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w"
    assume "proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
      assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      then obtain sv1'
      where 0: "validTransV (sv1,sv1')" 
      and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2 statO"  
      unfolding move_1_def by auto
      have r1': "reachV sv1'" using r1 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2 tr2 statO sv1' trv1 sv2 trv2"  
      using less(2)[OF v, of tr1 tr2 w1 w2 s1 s2 statA sv1' sv2 statO, simplified, OF \<Delta> ok _ _ _ _ _ r34 r1' r2] 
      using A34 less.prems(3-6) by blast
      show ?thesis apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
      using \<psi> ok 0 sv1 unfolding \<psi>_def Van.completedFrom_def by auto
    next 
      assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      then obtain sv2'
      where 0: "validTransV (sv2,sv2')"  
      and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1 sv2' statO"  
      unfolding move_2_def by auto
      have r2': "reachV sv2'" using r2 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2 tr2 statO sv1 trv1 sv2' trv2"  
      using less(2)[OF v, of tr1 tr2 w1 w2 s1 s2 statA sv1 sv2' statO, simplified, OF \<Delta> ok _ _ _ _ _ r34 r1 r2']  
      using A34 less.prems(3-6) by blast
      show ?thesis apply(rule exI[of _ trv1]) apply(rule exI[of _ "sv2 # trv2"])
      using \<psi> ok 0 sv2 unfolding \<psi>_def Van.completedFrom_def by auto 
    next
      assume sv12: "\<not> isSecV sv1" "\<not> isSecV sv2" "Van.eqAct sv1 sv2" 
      and "move_12 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      then obtain sv1' sv2' statO'
      where 0: "statO' = sstatO' statO sv1 sv2" 
      "validTransV (sv1,sv1') " "\<not> isSecV sv1"
      "validTransV (sv2,sv2')" "\<not> isSecV sv2"  
      "Van.eqAct sv1 sv2"  
      and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2' statO'"  
      unfolding move_12_def by auto
      have r12': "reachV sv1'" "reachV sv2'" using r1 r2 0 by (metis Van.reach.Step fst_conv snd_conv)+
      have ok': "statA = Diff \<longrightarrow> statO' = Diff" using ok 0 unfolding sstatO'_def by (cases statO, auto) 
      obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2 tr2 statO' sv1' trv1 sv2' trv2" 
      using less(2)[OF v, of tr1 tr2 w1 w2 s1 s2 statA sv1' sv2' statO', simplified, OF \<Delta> ok' _ _ _ _ _ r34 r12']   
      using A34 less.prems(3-6) by blast
      show ?thesis apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
      using \<psi> ok' 0 sv12 unfolding \<psi>_def sstatO'_def Van.completedFrom_def
      using Van.A.Cons_unfold Van.eqAct_def completedFromO_lastt less.prems(4) 
      less.prems(6) by auto 
    qed
  next
    assume m: "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
    show ?thesis
    proof(cases "length tr1 \<le> Suc 0") 
      case True note tr1 = True
      hence "tr1 = [] \<or> tr1 = [s1]" 
      by (metis Simple_Transition_System.validFromS_Cons_iff Suc_length_conv le_Suc_eq le_zero_eq length_0_conv less.prems(3))  
      hence "finalO s1" using less(3-6)  
        using Opt.completed_Cons Opt.completed_Nil by blast
      hence f4: "finalO s2" using f34 by blast
      hence tr2: "tr2 = [] \<or> tr2 = [s2]"  
        by (metis Opt.final_def Simple_Transition_System.validFromS_Cons_iff less.prems(5) neq_Nil_conv) 
      show ?thesis apply(rule exI[of _ "[sv1]"], rule exI[of _ "[sv2]"]) using tr1 tr2 
      using f4 f34  
      using completedFromO_lastt less.prems(4) 
      by (auto simp add: lastt_def \<psi>_def)
    next
      case False 
      then obtain s13 tr1' where tr1: "tr1 = s13 # tr1'" and tr1'NE: "tr1' \<noteq> []"
        by (cases tr1, auto) 
      have s13[simp]: "s13 = s1" using `Opt.validFromS s1 tr1`  
          by (simp add: Opt.validFromS_Cons_iff tr1)
      obtain s1' where
      trn3: "validTransO (s1,s1')" and 
      tr1': "Opt.validFromS s1' tr1'" using `Opt.validFromS s1 tr1` 
      unfolding tr1 s13 by (metis tr1'NE Simple_Transition_System.validFromS_Cons_iff)
      have r3': "reachO s1'" using r3 trn3 by (metis Opt.reach.Step fst_conv snd_conv)
      have f3: "\<not> finalO s1" using Opt.final_def trn3 by blast
      hence f4: "\<not> finalO s2" using f34 by blast
      hence tr2: "\<not> length tr2 \<le> Suc 0" 
      by (metis Opt.completed_Cons Simple_Transition_System.validFromS_Cons_iff 
      bot_nat_0.extremum completedFromO_def length_Cons less.prems(5) less.prems(6) neq_Nil_conv not_less_eq_eq)
   
      then obtain s24 tr2' where tr2: "tr2 = s24 # tr2'" and tr2'NE: "tr2' \<noteq> []"
      by (cases tr2, auto)  
      have s24[simp]: "s24 = s2" using `Opt.validFromS s2 tr2`  
      by (simp add: Opt.validFromS_Cons_iff tr2)
      obtain s2' where
      trn4: "validTransO (s2,s2') \<or> (s2 = s2' \<and> tr2' = [])" and 
      tr2': "Opt.validFromS s2' tr2'" using `Opt.validFromS s2 tr2` 
      unfolding tr2 s24 using Opt.validFromS_Cons_iff by auto
      have r34': "reachO s1'" "reachO s2'" 
      using r3 trn3 r4 trn4 by (metis Opt.reach.Step fst_conv snd_conv)+
      note r3' = r34'(1)  note r4' = r34'(2)
      define statA' where statA': "statA' = sstatA' statA s1 s2"         
      have "\<not> isIntO s1 \<or> \<not> isIntO s2 \<or> (isIntO s1 \<and> isIntO s2)"
      by auto
      thus ?thesis
      proof safe
        assume isAO3: "\<not> isIntO s1"  
        have O33': "Opt.O tr1 = Opt.O tr1'" "Opt.A tr1 = Opt.A tr1'" 
        using isAO3 unfolding tr1 by auto  
        have A34': "Opt.A tr1' = Opt.A tr2"  
        using A34 O33'(2) by auto 
        have m: "match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
        have "(\<exists>w1'<w1. \<exists>w2'<w2. \<not> isSecO s1 \<and> \<Delta> \<infinity> w1' w2' s1' s2 statA sv1 sv2 statO) \<or> 
              (\<exists>w2'<w2. eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> match1_1 \<Delta> \<infinity> w2' s1 s1' s2 statA sv1 sv2 statO) \<or> 
              (eqSec sv1 s1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> match1_12 \<Delta> \<infinity> \<infinity> s1 s1' s2 statA sv1 sv2 statO)" 
        using m isAO3 trn3 ok unfolding match1_def by auto  
        thus ?thesis 
        proof safe 
          fix w1' w2'
          assume "\<not> isSecO s1" and \<Delta>: "\<Delta> \<infinity> w1' w2' s1' s2 statA sv1 sv2 statO"
          hence S3: "Opt.S tr1' = Opt.S tr1" unfolding tr1 by auto            
          obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1' s2 tr2 statO sv1 trv1 sv2 trv2"
          using less(1)[of tr1' tr2, OF _ \<Delta> _ _ _ _ _ _ r3' r4 r12, unfolded O33', simplified]
          using less.prems tr1' ok A34' f3 f4 unfolding tr1 Opt.completedFrom_def
          by (auto split: if_splits simp: \<psi>_def lastt_def)
          show ?thesis apply(rule exI[of _ trv1]) apply(rule exI[of _ trv2])
          using \<psi> O33' S3 unfolding \<psi>_def 
          using completedFromO_lastt less.prems(4) 
          by (auto simp add: tr1 tr1'NE)
        next
          fix w2'
          assume trn13: "eqSec sv1 s1" and
          Atrn1: "\<not> isIntV sv1" and "match1_1 \<Delta> \<infinity> w2' s1 s1' s2 statA sv1 sv2 statO"
          then obtain sv1' where  
          trn1: "validTransV (sv1,sv1') " and              
          \<Delta>: "\<Delta> \<infinity> \<infinity> w2' s1' s2 statA sv1' sv2 statO"
          unfolding match1_1_def by auto 
          have r1': "reachV sv1'"using r1 trn1 by (metis Van.reach.Step fst_conv snd_conv)
          obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1' s2 tr2 statO sv1' trv1 sv2 trv2"
          using less(1)[of tr1' tr2, OF _ \<Delta> _ _ _ _ _ _ r3' r4 r1' r2, unfolded O33', simplified]
          using less.prems tr1' ok A34' f3 f4 unfolding tr1 tr2 Opt.completedFrom_def 
          by (auto simp: \<psi>_def lastt_def split: if_splits)
          show ?thesis apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
          using \<psi> O33' unfolding tr1 tr2  Van.completedFrom_def
          using Van.validFromS_Cons trn1 tr1'NE tr2'NE
          using isAO3 ok Atrn1 eqSec_S_Cons trn13  
          unfolding \<psi>_def using completedFromO_lastt less.prems(4) tr1 by auto        
        next
          assume sv2: "\<not> isSecV sv2" and trn13: "eqSec sv1 s1" and
          Atrn12: "Van.eqAct sv1 sv2" and "match1_12 \<Delta> \<infinity> \<infinity> s1 s1' s2 statA sv1 sv2 statO"
          then obtain sv1' sv2' statO' where
          statO': "statO' = sstatO' statO sv1 sv2" and  
          trn1: "validTransV (sv1,sv1') " and 
          trn2: "validTransV (sv2,sv2')" and 
          \<Delta>: "\<Delta> \<infinity> \<infinity> \<infinity> s1' s2 statA sv1' sv2' statO'"
          unfolding match1_12_def by auto 
          have r12': "reachV sv1'" "reachV sv2'" 
          using r1 trn1 r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)+
          obtain trv1 trv2 where \<psi>: "\<psi> s1' tr1' s2 tr2 statO' sv1' trv1 sv2' trv2"
          using less(1)[of tr1' tr2, OF _ \<Delta> _ _ _ _ _ _ r3' r4 r12', unfolded O33', simplified]
          using less.prems tr1' ok A34' f3 f4 unfolding tr1 tr2 Opt.completedFrom_def statO' sstatO'_def
          by auto presburger+
          show ?thesis apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
          using \<psi> O33' tr1'NE tr2'NE sv2 
          using Van.validFromS_Cons trn1 trn2 
          using isAO3 ok Atrn12 eqSec_S_Cons trn13 f3 f34 s13
          unfolding \<psi>_def tr1 Van.completedFrom_def Van.eqAct_def statO' sstatO'_def
          using Van.A.Cons_unfold tr1' trn3 by auto
        qed
      next
        assume isAO4: "\<not> isIntO s2"  
        have O44': "Opt.O tr2 = Opt.O tr2'" "Opt.A tr2 = Opt.A tr2'" 
        using isAO4 unfolding tr2 by auto  
        have A34': "Opt.A tr1 = Opt.A tr2'"  
        using A34 O44'(2) by auto 
        have m: "match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto 
        have "(\<exists>w1'<w1. \<exists>w2'<w2. \<not> isSecO s2 \<and> \<Delta> \<infinity> w1' w2' s1 s2' statA sv1 sv2 statO) \<or> 
              (\<exists>w1'<w1. eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> match2_1 \<Delta> w1' \<infinity> s1 s2 s2' statA sv1 sv2 statO) \<or> 
              (\<not> isSecV sv1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and> match2_12 \<Delta> \<infinity> \<infinity> s1 s2 s2' statA sv1 sv2 statO)" 
        using m isAO4 trn4 ok tr2'NE  unfolding match2_def by auto
        thus ?thesis 
        proof safe 
          fix w1' w2'
          assume "\<not> isSecO s2" and \<Delta>: "\<Delta> \<infinity> w1' w2' s1 s2' statA sv1 sv2 statO"
          hence S4: "Opt.S tr2' = Opt.S tr2" unfolding tr2 by auto            
          obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2' tr2' statO sv1 trv1 sv2 trv2"
          using less(1)[of tr1 tr2', OF _ \<Delta> _ _ _ _ _ _ r3 r4', simplified]
          using less.prems tr2' ok A34' tr1'NE tr2'NE unfolding tr1 tr2 Opt.completedFrom_def by (cases "isIntO s2", auto)  
          show ?thesis apply(rule exI[of _ trv1]) apply(rule exI[of _ trv2])
          using \<psi> O44' S4 unfolding \<psi>_def 
          using completedFromO_lastt less.prems(6)  
          unfolding Opt.completedFrom_def using tr2 tr2'NE by auto
        next
          fix w1'
          assume trn24: "eqSec sv2 s2" and
          Atrn2: "\<not> isIntV sv2" and "match2_1 \<Delta> w1' \<infinity> s1 s2 s2' statA sv1 sv2 statO"
          then obtain sv2' where trn2: "validTransV (sv2,sv2')" and              
          \<Delta>: "\<Delta> \<infinity> w1' \<infinity> s1 s2' statA sv1 sv2' statO"
          unfolding match2_1_def by auto 
          have r2': "reachV sv2'" using r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)
          obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2' tr2' statO sv1 trv1 sv2' trv2"
          using less(1)[of tr1 tr2', OF _ \<Delta> _ _ _ _ _ _ r3 r4' r1 r2', simplified]
          using less.prems tr2' ok A34' tr1'NE tr2'NE unfolding tr1 tr2 Opt.completedFrom_def by (cases "isIntO s2", auto)   
          show ?thesis apply(rule exI[of _ trv1]) apply(rule exI[of _ "sv2 # trv2"])
          using \<psi> tr1'NE tr2'NE 
          using Van.validFromS_Cons trn2 
          using isAO4 ok Atrn2 eqSec_S_Cons trn24  
          unfolding \<psi>_def tr1 tr2 s13 s24 Van.completedFrom_def lastt_def by auto
        next     
          assume sv1: "\<not> isSecV sv1" and trn24: "eqSec sv2 s2" and
          Atrn12: "Van.eqAct sv1 sv2" and  "match2_12 \<Delta> \<infinity> \<infinity> s1 s2 s2' statA sv1 sv2 statO"
          then obtain sv1' sv2' statO' where
          statO': "statO' = sstatO' statO sv1 sv2" and 
          trn1: "validTransV (sv1,sv1')" and               
          trn2: "validTransV (sv2,sv2')" and               
          \<Delta>: "\<Delta> \<infinity> \<infinity> \<infinity> s1 s2' statA sv1' sv2' statO'"
          unfolding match2_12_def by auto  
          have r12': "reachV sv1'" "reachV sv2'" 
          using r1 trn1 r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)+
          obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2' tr2' statO' sv1' trv1 sv2' trv2"
          using less(1)[of tr1 tr2', OF _ \<Delta> _ _ _ _ _ _ r3 r4' r12', simplified]
          using less.prems tr2' ok A34' tr1'NE tr2'NE unfolding tr1 tr2 Opt.completedFrom_def statO' sstatO'_def
          by (cases "isIntO s2", auto) 
          show ?thesis apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
          using \<psi> O44' tr1'NE tr2'NE sv1
          using Van.validFromS_Cons trn1 trn2 
          using isAO4 ok Atrn12 eqSec_S_Cons trn24 
          unfolding \<psi>_def tr2 tr1'NE Van.completedFrom_def Van.eqAct_def 
          statO' sstatO'_def
          using Van.A.Cons_unfold tr2' trn4 by auto
        qed
      next
        assume isAO34: "isIntO s1" "isIntO s2"
        have A34': "getActO s1 = getActO s2" "Opt.A tr1' = Opt.A tr2'"  
        using A34 isAO34  tr1'NE tr2'NE unfolding tr1 tr2 by auto 
        have O33': "Opt.O tr1 = getObsO s1 # Opt.O tr1'" and 
             O44': "Opt.O tr2 = getObsO s2 # Opt.O tr2'"  
        using isAO34 tr1'NE tr2'NE unfolding tr1 s13 tr2 s24 by auto     
        have m: "match12 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding statA' react_def by auto
        have trn34: "getObsO s1 = getObsO s2 \<or> statA' = Diff"
        using isAO34 unfolding statA' sstatA'_def by (cases statA,auto)  
        have "(\<exists>w1'<w1. \<exists>w2'<w2. \<not> isSecO s1 \<and> \<not> isSecO s2 \<and> (statA = statA' \<or> statO = Diff) \<and> 
                  \<Delta> \<infinity> w1' w2' s1' s2' statA' sv1 sv2 statO) 
              \<or> 
              (\<exists>w2'<w2. \<not> isSecO s2 \<and> eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and>
               (statA = statA' \<or> statO = Diff) \<and> 
               match12_1 \<Delta> \<infinity> w2' s1' s2' statA' sv1 sv2 statO)  
              \<or> 
              (\<exists>w1'<w1. \<not> isSecO s1 \<and> eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> 
               (statA = statA' \<or> statO = Diff) \<and> 
               match12_2 \<Delta> w1' \<infinity> s1' s2' statA' sv1 sv2 statO)  
              \<or> 
              (eqSec sv1 s1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and> 
               match12_12 \<Delta> \<infinity> \<infinity> s1' s2' statA' sv1 sv2 statO)"
        (is "?K1 \<or> ?K2 \<or> ?K3 \<or> ?K4")
        using m[unfolded match12_def, rule_format, of s1' s2'] 
        isAO34 A34' trn3 trn4 tr1'NE tr2'NE 
        unfolding s13 s24 trn34 statA' Opt.eqAct_def sstatA'_def by auto
        thus ?thesis proof (elim disjE)
          assume K1: "?K1" 
          then obtain w1' w2' where \<Delta>: "\<Delta> \<infinity> w1' w2' s1' s2' statA' sv1 sv2 statO" by auto
          have ok': "(statA' = Diff \<longrightarrow> statO = Diff)" 
          using ok K1 unfolding statA' using isAO34 by auto
          obtain trv1 trv2 where \<psi>: "\<psi> s1' tr1' s2' tr2' statO sv1 trv1 sv2 trv2"
          using less(1)[of tr1' tr2', OF _ \<Delta> _ _ _ _ _ _ r34' r12, simplified]
          using less.prems tr1' tr2' ok' A34' isAO34 tr1'NE tr2'NE unfolding tr1 tr2 Opt.completedFrom_def by auto
          show ?thesis apply(rule exI[of _ trv1]) apply(rule exI[of _ trv2])
          using \<psi> trn34 O33' O44' K1 ok unfolding \<psi>_def tr1 tr2 
          using completedFromO_lastt less.prems(4,6) 
          unfolding Opt.completedFrom_def using tr1 tr2 tr1'NE tr2'NE by auto
        next
          assume K2: "?K2" 
          then obtain w2' sv1' where  
          trn1: "validTransV (sv1,sv1') " and 
          trn13: "eqSec sv1 s1" and
          Atrn1: "\<not> isIntV sv1" and  ok': "(statA' = statA \<or> statO = Diff)" and 
          \<Delta>: "\<Delta> \<infinity> \<infinity> w2' s1' s2' statA' sv1' sv2 statO"
          unfolding match12_1_def by auto 
          have r1': "reachV sv1'" using r1 trn1 by (metis Van.reach.Step fst_conv snd_conv)
          obtain trv1 trv2 where \<psi>: "\<psi> s1' tr1' s2' tr2' statO sv1' trv1 sv2 trv2"
          using less(1)[of tr1' tr2', OF _ \<Delta> _ _ _ _ _ _ r34' r1' r2,  simplified]
          using less.prems tr1' tr2' ok' A34' tr1'NE tr2'NE unfolding tr1 tr2 Opt.completedFrom_def by auto 
          show ?thesis apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
          using \<psi> O33' O44' tr1'NE tr2'NE unfolding tr1 tr2  
          using Van.validFromS_Cons trn1 ok
          using K2 ok' Atrn1 eqSec_S_Cons trn13 trn34 
          unfolding statA' Van.completedFrom_def eqSec_def 
          using s13 tr1 tr1' tr2' trn3 trn4   
          by simp (smt (verit, best) Opt.S.Cons_unfold Simple_Transition_System.lastt_Cons 
          Van.A.Cons_unfold Van.O.Cons_unfold \<psi>_def completedFromO_lastt f3 f34 lastt_Nil 
          less.prems(4) status.simps(1)) 
        next
          assume K3: "?K3" 
          then obtain w1' sv2' where  
          trn2: "validTransV (sv2,sv2')" and 
          trn24: "eqSec sv2 s2" and
          Atrn2: "\<not> isIntV sv2" and  ok': "(statA' = statA \<or> statO = Diff)" and 
          \<Delta>: "\<Delta> \<infinity> w1' \<infinity> s1' s2' statA' sv1 sv2' statO"
          unfolding match12_2_def by auto 
          have r2': "reachV sv2'" using r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)
          obtain trv1 trv2 where \<psi>: "\<psi> s1' tr1' s2' tr2' statO sv1 trv1 sv2' trv2"
          using less(1)[of tr1' tr2', OF _ \<Delta> _ _ _ _ _ _ r34' r1 r2', simplified]
          using less.prems tr1' tr2' ok' A34' tr1'NE tr2'NE unfolding tr1 tr2 Opt.completedFrom_def by auto   
          show ?thesis apply(rule exI[of _ trv1]) apply(rule exI[of _ "sv2 # trv2"])
          using \<psi> O33' O44' tr1'NE tr2'NE unfolding \<psi>_def tr1 tr2  
          using Van.validFromS_Cons trn2 ok
          using K3 ok' Atrn2 eqSec_S_Cons trn24 trn34 
          unfolding statA' Van.completedFrom_def 
          using tr1' tr2' trn3 trn4 by force 
        next
          assume K4: "?K4"
          then obtain sv1' sv2' statO' where 0: 
            "statO' = sstatO' statO sv1 sv2"
            "validTransV (sv1,sv1') "
            "eqSec sv1 s1"
            "validTransV (sv2,sv2')"
            "eqSec sv2 s2"
            "Van.eqAct sv1 sv2"
            and ok': "statA' = Diff \<longrightarrow> statO' = Diff" and \<Delta>: "\<Delta> \<infinity> \<infinity> \<infinity> s1' s2' statA' sv1' sv2' statO'"
          unfolding match12_12_def by auto
          have r12': "reachV sv1'" "reachV sv2'" using r1 r2 0 
          by (metis Van.reach.Step fst_conv snd_conv)+
          obtain trv1 trv2 where \<psi>: "\<psi> s1' tr1' s2' tr2' statO' sv1' trv1 sv2' trv2"
          using less(1)[of tr1' tr2', OF _ \<Delta> _ _ _ _ _ _ r34' r12', simplified]
          using less.prems tr1' tr2' ok' A34' tr1'NE tr2'NE unfolding tr1 tr2 Opt.completedFrom_def by auto                    
          show ?thesis apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
          using trn34 
          using \<psi> O33' O44' isAO34 tr1'NE tr2'NE unfolding \<psi>_def tr1 tr2  
          using Van.validFromS_Cons 0 
          using K4 eqSec_S_Cons 
          unfolding statA' Van.eqAct_def Van.completedFrom_def match12_12_def sstatO'_def 
          by simp (smt (z3) Simple_Transition_System.lastt_Cons Van.A.Cons_unfold Van.O.Cons_unfold list.inject status.exhaust status.simps(1) tr1' tr2' trn3 trn4 newStat.simps(4) newStat_diff)
        qed
      qed
    qed
  qed
qed

(* *)

lemma unwindCond_final: 
"unwindCond \<Delta> \<Longrightarrow> reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2)"
unfolding unwindCond_def 
unfolding proact_def react_def match1_def match1_1_def
by auto

(* The crucial properties in lifting unwinding proof method from finite to infinite traces:  *)

definition "\<phi> \<Delta> w w1 w2 w1' w2' statA s1 tr1 s2 tr2 statAA statO sv1 trv1 sv2 trv2 statOO \<equiv> 
  trv1 \<noteq> [] \<and> trv2 \<noteq> [] \<and> 
  (length trv1 > Suc 0 \<or> w1' \<le> w1) \<and> (length trv2 > Suc 0 \<or> w2' \<le> w2) \<and> 
  Van.validFromS sv1 trv1 \<and> 
  Van.validFromS sv2 trv2 \<and>   
  Van.S trv1 = Opt.S tr1 \<and> Van.S trv2 = Opt.S tr2 \<and> 
  Van.A trv1 = Van.A trv2 \<and>  
  (statO = Eq \<longrightarrow> (statOO = Diff \<longleftrightarrow> Van.O trv1 \<noteq> Van.O trv2)) \<and>
  (statA = Eq \<longrightarrow> (statAA = Diff \<longleftrightarrow> Opt.O tr1 \<noteq> Opt.O tr2)) \<and>
  \<comment> \<open>\<close>
  (statO = Diff \<longrightarrow> statOO = Diff) \<and> 
  (statAA = Diff \<longrightarrow> statOO = Diff) \<and>  
  \<Delta> w w1' w2' (lastt s1 tr1) (lastt s2 tr2) statAA (lastt sv1 trv1) (lastt sv2 trv2) statOO"

lemma \<phi>_final: 
assumes unw: "unwindCond \<Delta>"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and vtr14: "Opt.validFromS s1 tr1" "Opt.validFromS s2 tr2"
and \<phi>: "\<phi> \<Delta> w w1 w2 w1' w2' statA s1 tr1 s2 tr2 statAA statO sv1 trv1 sv2 trv2 statOO" 
shows "(finalV (lastt sv1 trv1) \<longleftrightarrow> finalO (lastt s1 tr1)) \<and> (finalV (lastt sv2 trv2) \<longleftrightarrow> finalO (lastt s2 tr2))"
proof-
  have rsv12: "Van.validFromS sv1 trv1 \<longrightarrow> reachV (lastt sv1 trv1)" 
           "Van.validFromS sv2 trv2 \<longrightarrow> reachV (lastt sv2 trv2)" using r 
    by (simp add: Van.reach_validFromS_reach lastt_def)+
  have rs14: "Opt.validFromS s1 tr1 \<longrightarrow> reachO (lastt s1 tr1)" 
           "Opt.validFromS s2 tr2 \<longrightarrow> reachO (lastt s2 tr2)" using r 
    by (simp add: Opt.reach_validFromS_reach lastt_def)+
  show ?thesis using \<phi>[unfolded \<phi>_def] rsv12 rs14 using unw[unfolded unwindCond_def, rule_format, 
     of "lastt s1 tr1" "lastt s2 tr2" "lastt sv1 trv1" "lastt sv2 trv2" w w1' w2' statAA statOO]
  using vtr14(1) vtr14(2) by auto
qed

lemma \<phi>_completedFrom: "unwindCond \<Delta> \<Longrightarrow> 
reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
Opt.validFromS s1 tr1 \<Longrightarrow> completedFromO s1 tr1 \<Longrightarrow> 
Opt.validFromS s2 tr2 \<Longrightarrow> completedFromO s2 tr2 \<Longrightarrow> 
\<phi> \<Delta> statA w w1 w2 w1' w2' s1 tr1 s2 tr2 statAA statO sv1 trv1 sv2 trv2 statOO 
\<Longrightarrow> completedFromV sv1 trv1 \<and> completedFromV sv2 trv2"
using \<phi>_final  
by (metis Van.completedFrom_def completedFromO_lastt lastt_def)

lemma unwindCond_ex_\<phi>:
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "(statA = Diff \<longrightarrow> statO = Diff)" 
and v: "Opt.validFromS s1 tr1" "Opt.validFromS s2 tr2" 
and i: "isIntO (lastt s1 tr1)" "isIntO (lastt s2 tr2)"  
and nev: "never isIntO (butlast tr1)" "never isIntO (butlast tr2)"
shows "\<exists>w' w1' w2' trv1 trv2 statAA statOO. \<phi> \<Delta> w' w1 w2 w1' w2' statA s1 tr1 s2 tr2 statAA statO sv1 trv1 sv2 trv2 statOO"
using assms(2-) 
proof(induction "length tr1 + length tr2" w
   arbitrary: w1 w2 s1 s2 statA sv1 sv2 statO tr1 tr2 rule: less2_induct')
  case (less w tr1 tr2 w1 w2 s1 s2 statA sv1 sv2 statO)
  note ok = `statA = Diff \<longrightarrow> statO = Diff` 
  note \<Delta> = `\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO`
  note r34 = less(4,5) note r12 = less(6,7)
  note r = r34 r12 
  note r3 = r34(1) note r4 = r34(2) note r1 = r12(1) note r2 = r12(2)
  note nev34 = less(13,14)
  note nev3 = nev34(1) note nev4 = nev34(2)

  have i34: "statA = Eq \<longrightarrow> isIntO s1 = isIntO s2"
  and f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2" 
    using \<Delta> unwind[unfolded unwindCond_def] r by auto

  note is1 = `isIntO (lastt s1 tr1)`
  note is2 = `isIntO (lastt s2 tr2)`
  note vtr1 = `Opt.validFromS s1 tr1` 
  note vtr2 = `Opt.validFromS s2 tr2` 

  have proact_match: "(\<exists>v<w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
  using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w" 
    assume "proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
     assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv1'
     where 0: "validTransV (sv1,sv1')" 
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2 statO"  
     unfolding move_1_def by auto
     have r1': "reachV sv1'" using r1 0 by (metis Van.reach.Step fst_conv snd_conv)
     obtain w' w1' w2' trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> w' w1 w2 w1' w2' statA s1 tr1 s2 tr2 statAA statO sv1' trv1 sv2 trv2 statOO" 
     using less(2)[OF v, of tr1 tr2 w1 w2 s1 s2 statA sv1' sv2 statO, simplified, OF \<Delta> r34 r1' r2 ok]  
     using is1 is2 nev3 nev4 vtr1 vtr2 by blast 
     show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) 
     apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
     using \<phi> ok 0 sv1 unfolding \<phi>_def by auto
    next 
     assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv2'
     where 0: "validTransV (sv2,sv2')"  
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1 sv2' statO"  
     unfolding move_2_def by auto
     have r2': "reachV sv2'" using r2 0 by (metis Van.reach.Step fst_conv snd_conv)
     obtain w' w1' w2' trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> w' w1 w2 w1' w2' statA s1 tr1 s2 tr2 statAA statO sv1 trv1 sv2' trv2 statOO" 
     using less(2)[OF v, of tr1 tr2 w1 w2 s1 s2 statA sv1 sv2' statO, simplified, OF \<Delta> r34 r1 r2' ok]   
     using is1 is2 nev3 nev4 vtr1 vtr2 by blast 
     show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
     apply(rule exI[of _ trv1]) apply(rule exI[of _ "sv2 # trv2"])
     using \<phi> ok 0 sv2 unfolding \<phi>_def by auto 
    next
     assume sv12: "\<not> isSecV sv1" "\<not> isSecV sv2" "Van.eqAct sv1 sv2" 
     and "move_12 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv1' sv2' statO'
     where 0: "statO' = sstatO' statO sv1 sv2" 
     "validTransV (sv1,sv1') " "\<not> isSecV sv1"
     "validTransV (sv2,sv2')" "\<not> isSecV sv2"  
     "Van.eqAct sv1 sv2"  
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2' statO'"  
     unfolding move_12_def by auto
     have r12': "reachV sv1'" "reachV sv2'" using r1 r2 0 by (metis Van.reach.Step fst_conv snd_conv)+
     have ok': "statA = Diff \<longrightarrow> statO' = Diff" 
     using ok 0 unfolding sstatO'_def by (cases statO, auto) 
     obtain w' w1' w2' trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> w' w1 w2 w1' w2' statA s1 tr1 s2 tr2 statAA statO' sv1' trv1 sv2' trv2 statOO" 
     using less(2)[OF v, of tr1 tr2 w1 w2 s1 s2 statA sv1' sv2' statO', simplified, OF \<Delta> r34 r12' ok']  
     using is1 is2 nev3 nev4 vtr1 vtr2 by blast  
     show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
     apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
     apply(rule exI[of _ statAA]) apply(rule exI[of _ statOO])
     using \<phi> ok' 0 sv12 nev unfolding \<phi>_def sstatO'_def 
     by simp (smt (verit, ccfv_SIG) Statewise_Attacker_Mod.eqAct_def 
     Van.A.Cons_unfold Van.O.Cons_unfold Van.Statewise_Attacker_Mod_axioms 
     Van.validFromS_Cons list.inject newStat.simps(1) newStat.simps(4)) 
    qed
  next
    assume m: "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
    define statA' where statA': "statA' = sstatA' statA s1 s2" 
    show ?thesis
    proof(cases "length tr1 \<le> Suc 0") 
     case True  
     hence tr1e: "tr1 = [] \<or> tr1 = [s1]"   
     by (metis Opt.validFromS_singl_iff Suc_length_conv le_Suc_eq le_zero_eq length_0_conv vtr1)
     hence "Opt.A tr1 = []" by (simp add: True) 
     hence "Opt.A tr2 = []" using Opt.A.eq_Nil_iff nev4 by blast  
     show ?thesis 
     proof(cases "length tr2 \<le> Suc 0")
       case True 
       hence tr2e: "tr2 = [] \<or> tr2 = [s2]"  
        by (metis Opt.validFromS_def Suc_length_conv le_Suc_eq le_zero_eq length_0_conv list.sel(1) vtr2)
       show ?thesis apply(rule exI[of _ w]) apply(rule exI[of _ w1]) apply(rule exI[of _ w2])
       apply(rule exI[of _ "[sv1]"], rule exI[of _ "[sv2]"], rule exI[of _ statA], rule exI[of _ statO]) 
       using tr1e tr2e
       using f34 \<Delta> apply (clarsimp simp: \<phi>_def lastt_def) 
       apply(cases statA, simp_all)  
       apply (metis Opt.O.simps(4) Opt.S.simps(4) last_ConsL)  
       by (metis Opt.S.simps(4) last.simps ok) 
     next
       case False
       then obtain s24 tr2' where tr2: "tr2 = s24 # tr2'" and tr2'NE: "tr2' \<noteq> []"
       by (cases tr2, auto)  
       have s24[simp]: "s24 = s2" using `Opt.validFromS s2 tr2`  
       by (simp add: Opt.validFromS_Cons_iff tr2)
       obtain s2' where
       trn4: "validTransO (s2,s2') \<or> (s2 = s2' \<and> tr2' = [])" and 
       tr2': "Opt.validFromS s2' tr2'" using `Opt.validFromS s2 tr2` 
       unfolding tr2 s24 using Opt.validFromS_Cons_iff by auto
       have r4': "reachO s2'" 
       using r4 trn4 by (metis Opt.reach.Step fst_conv snd_conv)+
       have nev4': "never isIntO (butlast tr2')"  
       by (metis Opt.O.Nil_iff Opt.O.eq_Nil_iff nev4 tr2)   
       have isAO4: "\<not> isIntO s2" 
       using \<open>Opt.A tr2 = []\<close> tr2 tr2'NE by auto 
       have O44': "Opt.O tr2 = Opt.O tr2'" "Opt.A tr2 = Opt.A tr2'" 
       using isAO4 \<open>Opt.A tr2 = []\<close> tr2 by auto
       have m: "match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto 
       have "(\<exists>w1'<w1. \<exists>w2'<w2. \<not> isSecO s2 \<and> \<Delta> \<infinity> w1' w2' s1 s2' statA sv1 sv2 statO) \<or> 
            (\<exists>w1'<w1. eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> match2_1 \<Delta> w1' \<infinity> s1 s2 s2' statA sv1 sv2 statO) \<or> 
            (\<not> isSecV sv1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and> match2_12 \<Delta> \<infinity> \<infinity> s1 s2 s2' statA sv1 sv2 statO)" 
       using isAO4 trn4 ok tr2'NE 
       using m[unfolded match2_def, rule_format, of s2'] by auto
       thus ?thesis 
       proof safe 
         fix w1'' w2'' assume w12': "w1'' < w1" "w2'' < w2"  
         assume "\<not> isSecO s2" and \<Delta>: "\<Delta> \<infinity> w1'' w2'' s1 s2' statA sv1 sv2 statO"
         hence S4: "Opt.S tr2' = Opt.S tr2" unfolding tr2 by auto          
         obtain w' w1' w2' trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> w' w1'' w2'' w1' w2' statA s1 tr1 s2' tr2' statAA statO sv1 trv1 sv2 trv2 statOO"     
         using less(1)[of tr1 tr2', OF _ \<Delta> r3 r4' _ _ _ _ _ _ _ nev3 nev4', unfolded tr2, simplified] 
         using is1 is2 vtr1 vtr2 tr2' ok tr2'NE trn4 r1 r2 tr2 by auto
         show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ trv1]) apply(rule exI[of _ trv2])
         using \<phi> O44' S4 tr2 tr2'NE trn4 tr2' w12' unfolding \<phi>_def by auto
       next
         fix w1'' assume w1': "w1'' < w1" 
         assume trn24: "eqSec sv2 s2" and
         Atrn2: "\<not> isIntV sv2" and "match2_1 \<Delta> w1'' \<infinity> s1 s2 s2' statA sv1 sv2 statO"
         then obtain sv2' where trn2: "validTransV (sv2,sv2')" and            
         \<Delta>: "\<Delta> \<infinity> w1'' \<infinity> s1 s2' statA sv1 sv2' statO"
         unfolding match2_1_def by auto 
         have r2': "reachV sv2'" using r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)
         obtain w' w1' w2' trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> w' w1'' \<infinity> w1' w2' statA s1 tr1 s2' tr2' statAA statO sv1 trv1 sv2' trv2 statOO"
         using less(1)[of tr1 tr2', OF _ \<Delta> r3 r4' r1 r2' _ _ _ _ _ nev3 nev4', unfolded tr2, simplified]
         using is1 is2 tr2' tr2 vtr1 ok tr2'NE trn4 by auto
         show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ trv1]) apply(rule exI[of _ "sv2 # trv2"])
         using \<phi> tr2'NE 
         using Van.validFromS_Cons trn2 
         using isAO4 ok Atrn2 eqSec_S_Cons trn24 tr2' trn4 w1'
         unfolding \<phi>_def tr2 s24  
         by auto
       next     
         assume sv1: "\<not> isSecV sv1" and trn24: "eqSec sv2 s2" and
         Atrn12: "Van.eqAct sv1 sv2" and "match2_12 \<Delta> \<infinity> \<infinity> s1 s2 s2' statA sv1 sv2 statO"
         then obtain sv1' sv2' statO' where 
         statO': "statO' = sstatO' statO sv1 sv2" and 
         trn1: "validTransV (sv1,sv1')" and             
         trn2: "validTransV (sv2,sv2')" and             
         \<Delta>: "\<Delta> \<infinity> \<infinity> \<infinity> s1 s2' statA sv1' sv2' statO'"
         unfolding match2_12_def by auto  
         have r12': "reachV sv1'" "reachV sv2'" 
         using r1 trn1 r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)+
         obtain w' w1' w2' trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> w' \<infinity> \<infinity> w1' w2' statA s1 tr1 s2' tr2' statAA statO' sv1' trv1 sv2' trv2 statOO"
         using less(1)[of tr1 tr2', OF _ \<Delta> r3 r4' r12' _ _ _ _ _ nev3 nev4', simplified]
         using is1 is2 vtr1 tr2 tr2' ok tr2'NE trn4 unfolding tr2 statO' sstatO'_def by auto
         show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
         using \<phi> O44' tr2'NE sv1
         using Van.validFromS_Cons trn1 trn2 
         using isAO4 ok Atrn12 eqSec_S_Cons trn24 tr2' trn4
         unfolding \<phi>_def tr2 Van.completedFrom_def Van.eqAct_def statO' sstatO'_def 
         by simp (smt (verit, ccfv_threshold) Van.A.Cons_unfold i34 is1 last_ConsL 
         lastt_def status.exhaust tr1e newStat.simps(2))
      qed
     qed
    next
     case False 
     then obtain s13 tr1' where tr1: "tr1 = s13 # tr1'" and tr1'NE: "tr1' \<noteq> []"
       by (cases tr1, auto) 
     have s13[simp]: "s13 = s1" using `Opt.validFromS s1 tr1`  
         by (simp add: Opt.validFromS_Cons_iff tr1)
     obtain s1' where
     trn3: "validTransO (s1,s1')" and 
     tr1': "Opt.validFromS s1' tr1'" using `Opt.validFromS s1 tr1` 
     unfolding tr1 s13 by (metis tr1'NE Simple_Transition_System.validFromS_Cons_iff)
     have r3': "reachO s1'" using r3 trn3 by (metis Opt.reach.Step fst_conv snd_conv)
     have f3: "\<not> finalO s1" using Opt.final_def trn3 by blast
     hence f4: "\<not> finalO s2" using f34 by blast
     have nev3': "never isIntO (butlast tr1')"  
     using nev3 tr1 tr1'NE by auto  
     have isAO3: "\<not> isIntO s1" using less.prems(11) tr1 tr1'NE by auto 
     have O33': "Opt.O tr1 = Opt.O tr1'" "Opt.A tr1 = Opt.A tr1'" 
     using isAO3 unfolding tr1 by auto   
     have m: "match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
     have "(\<exists>w1'<w1. \<exists>w2'<w2. \<not> isSecO s1 \<and> \<Delta> \<infinity> w1' w2' s1' s2 statA sv1 sv2 statO) \<or> 
          (\<exists>w2'<w2. eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> match1_1 \<Delta> \<infinity> w2' s1 s1' s2 statA sv1 sv2 statO) \<or> 
          (eqSec sv1 s1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> match1_12 \<Delta> \<infinity> \<infinity> s1 s1' s2 statA sv1 sv2 statO)" 
     using m isAO3 trn3 ok unfolding match1_def by auto  
     thus ?thesis 
     proof safe 
       fix w1'' w2'' assume w12': "w1'' < w1" "w2'' < w2" 
       assume "\<not> isSecO s1" and \<Delta>: "\<Delta> \<infinity> w1'' w2'' s1' s2 statA sv1 sv2 statO"
       hence S3: "Opt.S tr1' = Opt.S tr1" unfolding tr1 by auto          
       obtain w' w1' w2' trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> w' w1'' w2'' w1' w2' statA s1' tr1' s2 tr2 statAA statO sv1 trv1 sv2 trv2 statOO"
       using less(1)[of tr1' tr2, OF _ \<Delta> r3' r4 r12, unfolded O33', simplified]
       using is1 is2 tr1' ok f3 f4 tr1'NE trn3 O33'(1) nev3' nev4 vtr2 unfolding tr1 by auto
       show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ trv1]) apply(rule exI[of _ trv2])
       using \<phi> O33' S3 tr1 tr1'NE tr1' trn3 w12' unfolding \<phi>_def by auto          
     next
       fix w2'' assume w2': "w2'' < w2"
       assume trn13: "eqSec sv1 s1" and
       Atrn1: "\<not> isIntV sv1" and "match1_1 \<Delta> \<infinity> w2'' s1 s1' s2 statA sv1 sv2 statO"
       then obtain sv1' where  
       trn1: "validTransV (sv1,sv1') " and            
       \<Delta>: "\<Delta> \<infinity> \<infinity> w2'' s1' s2 statA sv1' sv2 statO"
       unfolding match1_1_def by auto 
       have r1': "reachV sv1'"using r1 trn1 by (metis Van.reach.Step fst_conv snd_conv)
       obtain w' w1' w2' trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> w' \<infinity> w2'' w1' w2' statA s1' tr1' s2 tr2 statAA statO sv1' trv1 sv2 trv2 statOO"
       using less(1)[of tr1' tr2, OF _ \<Delta> r3' r4 r1' r2, unfolded O33', simplified]
       using is1 is2 tr1 nev3' nev4 vtr1 vtr2 tr1' ok f3 f4 tr1'NE trn3 O33'(1)
       unfolding tr1 by auto
       show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
       using \<phi>  O33' unfolding \<phi>_def tr1 Van.completedFrom_def
       using Van.validFromS_Cons trn1 tr1'NE tr1' trn3
       using isAO3 ok Atrn1 eqSec_S_Cons trn13 w2'  
       by auto       
     next
       assume sv2: "\<not> isSecV sv2" and trn13: "eqSec sv1 s1" and
       Atrn12: "Van.eqAct sv1 sv2" and "match1_12 \<Delta> \<infinity> \<infinity> s1 s1' s2 statA sv1 sv2 statO"
       then obtain sv1' sv2' statO' where 
       statO': "statO' = sstatO' statO sv1 sv2" and 
       trn1: "validTransV (sv1,sv1') " and 
       trn2: "validTransV (sv2,sv2')" and 
       \<Delta>: "\<Delta> \<infinity> \<infinity> \<infinity> s1' s2 statA sv1' sv2' statO'"
       unfolding match1_12_def by auto 
       have r12': "reachV sv1'" "reachV sv2'" 
       using r1 trn1 r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)+
       obtain w' w1' w2' trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> w' \<infinity> \<infinity> w1' w2' statA s1' tr1' s2 tr2 statAA statO' sv1' trv1 sv2' trv2 statOO"
       using less(1)[of tr1' tr2, OF _ \<Delta> r3' r4 r12', unfolded O33', simplified]
       using less.prems tr1' ok f3 f4 tr1'NE trn3 O33'(1) unfolding tr1 statO' sstatO'_def by auto

       have trv1NE: "trv1 \<noteq> []" and trv2NE: "trv2 \<noteq> []" using \<phi> unfolding \<phi>_def by auto
       have [simp]: "Van.O (sv1 # trv1) = Van.O (sv2 # trv2) \<longleftrightarrow> (isIntV sv1 \<longrightarrow> getObsV sv1 = getObsV sv2) \<and> Van.O trv1 = Van.O trv2"
       using Atrn12 trv1NE trv2NE unfolding Van.O.map_filter Van.eqAct_def by simp
       show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
       using \<phi> O33' tr1'NE sv2 
       using Van.validFromS_Cons trn1 trn2 
       using isAO3 ok Atrn12 eqSec_S_Cons trn13 f3 f34 s13 tr1' trn3
       unfolding \<phi>_def tr1 Van.completedFrom_def Van.eqAct_def statO' sstatO'_def apply clarsimp
       by (smt (verit, ccfv_SIG) Van.A.Cons_unfold newStat.simps(1) newStat.simps(2) newStat.simps(4))
     qed
    qed
  qed
qed

definition "\<phi>a \<Delta> w w1 w2 w1' w2' statA s1 tr1 s2 tr2 statAA statO sv1 trv1 sv2 trv2 statOO \<equiv> 
  trv1 \<noteq> [] \<and> trv2 \<noteq> [] \<and> 
  (length trv1 > Suc 0 \<or> w1' < w1) \<and> (length trv2 > Suc 0 \<or> w2' < w2) \<and> 
  Van.validFromS sv1 trv1 \<and> 
  Van.validFromS sv2 trv2 \<and>   
  Van.S trv1 = Opt.S tr1 \<and> Van.S trv2 = Opt.S tr2 \<and> 
  Van.A trv1 = Van.A trv2 \<and>  
  (statO = Eq \<longrightarrow> (statOO = Diff \<longleftrightarrow> Van.O trv1 \<noteq> Van.O trv2)) \<and>
  (statA = Eq \<longrightarrow> (statAA = Diff \<longleftrightarrow> Opt.O tr1 \<noteq> Opt.O tr2)) \<and>
  \<comment> \<open>\<close>
  (statO = Diff \<longrightarrow> statOO = Diff) \<and> 
  (statAA = Diff \<longrightarrow> statOO = Diff) \<and>  
  \<Delta> w w1' w2' (lastt s1 tr1) (lastt s2 tr2) statAA (lastt sv1 trv1) (lastt sv2 trv2) statOO"
     
lemma unwindCond_ex_\<phi>a_getActO: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r34: "reachO s1" "reachO s2" and r12: "reachV sv1" "reachV sv2" 
and stat: "(statA = Diff \<longrightarrow> statO = Diff)" 
and v: "validTransO (s1, s1')" "validTransO (s2, s2')" 
and i34: "isIntO s1" "isIntO s2" "getActO s1 = getActO s2"  
shows "\<exists>w1' w2' trv1 trv2 statOO.
       \<phi>a \<Delta> \<infinity> w1 w2 w1' w2' statA s1 [s1, s1'] s2 [s2, s2'] (sstatA' statA s1 s2) statO sv1 trv1 sv2 trv2 statOO"
using \<Delta> r12 stat
proof(induction w arbitrary: w1 w2 sv1 sv2 statO rule: less_induct)
  case (less w w1 w2 sv1 sv2 statO)
  note \<Delta> = `\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO`
  note r12 = less.prems(2,3)
  note r1 = r12(1) note r2 = r12(2)
  note r = r34 r12
  note stat = `statA = Diff \<longrightarrow> statO = Diff`

  have f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2" 
    using \<Delta> unwind[unfolded unwindCond_def] r by auto

  have proact_match: "(\<exists>v<w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
  using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w" 
    assume "proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
     assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv1'
     where 0: "validTransV (sv1,sv1')" 
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2 statO"  
     unfolding move_1_def by auto
     have r1': "reachV sv1'" using r1 0 by (metis Van.reach.Step fst_conv snd_conv)
     obtain w1' w2' trv1 trv2 statOO where 
     \<phi>: "\<phi>a \<Delta> \<infinity> w1 w2 w1' w2' statA s1 [s1, s1'] s2 [s2, s2'] (sstatA' statA s1 s2) statO sv1' trv1 sv2 trv2 statOO" 
     using less(1)[OF v \<Delta> r1' r2 stat] by auto
     show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
     using \<phi> 0 sv1 unfolding \<phi>a_def apply simp  
     by (metis Van.validFromS_Cons)
    next 
     assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv2'
     where 0: "validTransV (sv2,sv2')"  
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1 sv2' statO"  
     unfolding move_2_def by auto
     have r2': "reachV sv2'" using r2 0 by (metis Van.reach.Step fst_conv snd_conv)
     obtain w1' w2' trv1 trv2 statOO where 
     \<phi>: "\<phi>a \<Delta> \<infinity> w1 w2 w1' w2' statA s1 [s1, s1'] s2 [s2, s2'] (sstatA' statA s1 s2) statO sv1 trv1 sv2' trv2 statOO" 
     using less(1)[OF v \<Delta> r1 r2' stat] by auto
     show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "sv2 # trv2"])
     using \<phi> 0 sv2 unfolding \<phi>a_def apply simp by (metis Van.validFromS_Cons)
    next
     assume sv12: "\<not> isSecV sv1" "\<not> isSecV sv2" "Van.eqAct sv1 sv2" 
     and "move_12 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv1' sv2' statO'
     where 0: "statO' = sstatO' statO sv1 sv2" 
     "validTransV (sv1,sv1') " "\<not> isSecV sv1"
     "validTransV (sv2,sv2')" "\<not> isSecV sv2"  
     "Van.eqAct sv1 sv2"  
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2' statO'"  
     unfolding move_12_def by auto
     have r12': "reachV sv1'" "reachV sv2'" using r1 r2 0 by (metis Van.reach.Step fst_conv snd_conv)+
     have stat': "statA = Diff \<longrightarrow> statO' = Diff" 
     using stat 0 unfolding sstatO'_def by (cases statO, auto)  
     obtain w1' w2' trv1 trv2 statOO where 
     \<phi>: "\<phi>a \<Delta> \<infinity> w1 w2 w1' w2' statA s1 [s1, s1'] s2 [s2, s2'] (sstatA' statA s1 s2) statO' sv1' trv1 sv2' trv2 statOO" 
     using less(1)[OF v \<Delta> r12' stat'] unfolding \<phi>a_def apply simp by metis
     show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
     using \<phi> 0 unfolding \<phi>a_def sstatO'_def apply clarsimp  apply(intro conjI)
       subgoal by auto
       subgoal by auto
       subgoal by (metis Van.A.Cons_unfold Van.eqAct_def)
       subgoal apply(rule exI[of _ statOO]) apply simp  
       by (smt (verit, ccfv_threshold) Van.O.Cons_unfold Van.eqAct_def 
         list.inject newStat.simps(1) newStat.simps(3)) .
    qed
  next
    assume m: "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
    define statA' where statA': "statA' = sstatA' statA s1 s2" 
    have m: "match12 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
    have "(\<exists>w1' w2'. w1' < w1 \<and> w2'< w2 \<and> \<not> isSecO s1 \<and> \<not> isSecO s2 \<and> (statA = statA' \<or> statO = Diff) \<and> 
            \<Delta> \<infinity> w1' w2' s1' s2' statA' sv1 sv2 statO) 
          \<or>
          (\<exists>w2'< w2. \<not> isSecO s2 \<and>
            eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> (statA = statA' \<or> statO = Diff) \<and> 
            match12_1 \<Delta> \<infinity> w2' s1' s2' statA' sv1 sv2 statO) 
          \<or>
          (\<exists>w1'<w1. \<not> isSecO s1 \<and>
            eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> (statA = statA' \<or> statO = Diff) \<and> 
            match12_2 \<Delta> w1' \<infinity> s1' s2' statA' sv1 sv2 statO) 
          \<or>
          (eqSec sv1 s1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and> 
            match12_12 \<Delta> \<infinity> \<infinity> s1' s2' statA' sv1 sv2 statO)" 
    using m unfolding match12_def  
    by (simp add: Opt.eqAct_def i34(1) i34(2) i34(3) statA' v(1) v(2))
    thus ?thesis 
    apply(elim disjE exE)
      subgoal for w1' w2' apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
      apply(rule exI[of _ "[sv1]"]) apply(rule exI[of _ "[sv2]"])
      apply(rule exI[of _ statO])
      using stat unfolding \<phi>a_def statA'  
      by (auto simp add: i34(1) i34(2) sstatA'_def lastt_def) 
      subgoal for w2' apply(rule exI[of _ \<infinity>]) apply(rule exI[of _ w2'])
      unfolding match12_1_def apply(elim conjE exE) subgoal for sv1'
      apply(rule exI[of _ "[sv1,sv1']"]) apply(rule exI[of _ "[sv2]"])
      apply(rule exI[of _ statO])
      using stat unfolding \<phi>a_def statA'  
      by (auto simp add: i34(1) i34(2) sstatA'_def lastt_def) .
      subgoal for w1' apply(rule exI[of _ w1']) apply(rule exI[of _ \<infinity>])
      unfolding match12_2_def apply(elim conjE exE) subgoal for sv2'
      apply(rule exI[of _ "[sv1]"]) apply(rule exI[of _ "[sv2,sv2']"])
      apply(rule exI[of _ statO])
      using stat unfolding \<phi>a_def statA'  
      by (auto simp add: i34(1) i34(2) sstatA'_def lastt_def) .
      subgoal unfolding match12_12_def apply(elim conjE exE) subgoal for sv1' sv2'
      apply(rule exI[of _ \<infinity>]) apply(rule exI[of _ \<infinity>])
      apply(rule exI[of _ "[sv1,sv1']"]) apply(rule exI[of _ "[sv2,sv2']"])
      apply(rule exI[of _ "sstatO' statO sv1 sv2"])
      using stat unfolding \<phi>a_def statA'  
      by (auto simp add: i34 i34 sstatA'_def sstatO'_def lastt_def Van.eqAct_def) . .
  qed
qed

lemma unwindCond_ex_\<phi>a'_aux:
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2" 
and stat: "(statA = Diff \<longrightarrow> statO = Diff)" 
and tr14NE: "tr1 \<noteq> []" "tr2 \<noteq> []"
and v3': "Opt.validFromS s1 (tr1 ## s1')" and v4': "Opt.validFromS s2 (tr2 ## s2')" 
and i: "isIntO (lastt s1 tr1)" "isIntO (lastt s2 tr2)"  
and A34: "getActO (lastt s1 tr1) = getActO (lastt s2 tr2)" 
and nev: "never isIntO (butlast tr1)" "never isIntO (butlast tr2)"
shows "\<exists>w1' w2' trv1' trv2' statAA' statOO'. 
   \<phi>a \<Delta> \<infinity> w1 w2 w1' w2' statA s1 (tr1 ## s1') s2 (tr2 ## s2') statAA' statO sv1 trv1' sv2 trv2' statOO'"
proof-
  have v3: "Opt.validFromS s1 tr1" and s13': "validTransO (lastt s1 tr1,s1')"
  apply (metis v3' Opt.validFromS_def Opt.validS_append1 Nil_is_append_conv hd_append2)
  by (metis Opt.validFromS_def Opt.validS_validTrans append_is_Nil_conv lastt_def list.distinct(1) list.sel(1) tr14NE(1) v3')
  have v4: "Opt.validFromS s2 tr2" and s24': "validTransO (lastt s2 tr2,s2')"
  apply (metis v4' Opt.validFromS_def Opt.validS_append1 Nil_is_append_conv hd_append2)
  by (metis Opt.validFromS_def Opt.validS_validTrans append_is_Nil_conv lastt_def list.sel(1) list.simps(3) tr14NE(2) v4')
  
  obtain ww ww1 ww2 trv1 trv2 statAA statOO where \<phi>: "\<phi> \<Delta> ww w1 w2 ww1 ww2 statA s1 tr1 s2 tr2 statAA statO sv1 trv1 sv2 trv2 statOO"
  using unwindCond_ex_\<phi>[OF unwind \<Delta> r stat v3 v4 i nev] by auto

  have trv12NE: "trv1 \<noteq> []" "trv2 \<noteq> []" using \<phi> unfolding \<phi>_def by auto
  
  define ss1 ss2 ssv1 ssv2 where ss1: "ss1 \<equiv> lastt s1 tr1" and ss2: "ss2 \<equiv> lastt s2 tr2"
  and ssv1: "ssv1 \<equiv> lastt sv1 trv1" and ssv2: "ssv2 \<equiv> lastt sv2 trv2"

  have ss1l: "ss1 = last tr1" by (simp add: lastt_def ss1 tr14NE(1))
  have tr1l: "tr1 = butlast tr1 @ [ss1]" by (simp add: ss1l tr14NE(1)) 
  have ss2l: "ss2 = last tr2" by (simp add: lastt_def ss2 tr14NE(2))
  have tr2l: "tr2 = butlast tr2 @ [ss2]" by (simp add: ss2l tr14NE(2)) 
  have ssv1l: "ssv1 = last trv1" using \<phi> unfolding \<phi>_def by (metis lastt_def ssv1)
  have trv1l: "trv1 = butlast trv1 @ [ssv1]" by (simp add: ssv1l trv12NE(1))
  have ssv2l: "ssv2 = last trv2" using \<phi> unfolding \<phi>_def by (metis lastt_def ssv2)
  have trv2l: "trv2 = butlast trv2 @ [ssv2]" by (simp add: ssv2l trv12NE(2))

  have iss14[simp]: "isIntO ss1" "isIntO ss2" using i unfolding ss1 ss2 by auto
  have giss14[simp]: "getActO ss1 = getActO ss2"  
    using A34 ss1 ss2 by fastforce

  have [simp]: "Opt.O (tr1 ## s1') = Opt.O tr1 ## getObsO ss1"
  by (metis Opt.O_def \<open>isIntO ss1\<close> holds_filtermap_RCons snoc_eq_iff_butlast tr1l)
  have [simp]: "Opt.O (tr2 ## s2') = Opt.O tr2 ## getObsO ss2"
  by (metis Opt.O_def \<open>isIntO ss2\<close> holds_filtermap_RCons snoc_eq_iff_butlast tr2l) 

  have [simp]: "Opt.A (tr1 ## s1') = Opt.A tr1 ## getActO ss1"
  by (metis Opt.A_def \<open>isIntO ss1\<close> holds_filtermap_RCons snoc_eq_iff_butlast tr1l)
  have [simp]: "Opt.A (tr2 ## s2') = Opt.A tr2 ## getActO ss2"
  by (metis Opt.A_def \<open>isIntO ss2\<close> holds_filtermap_RCons snoc_eq_iff_butlast tr2l)
  have [simp]: "Opt.A (tr1 ## s1') = Opt.A (tr2 ## s2') \<longleftrightarrow> Opt.A tr1 = Opt.A tr2" by simp
  
  have rss: "reachO ss1" "reachO ss2" "reachV ssv1" "reachV ssv2" 
  using Opt.reach_validFromS_reach r ss1l tr14NE(1) v3 apply blast
  using Opt.reach_validFromS_reach r(2) ss2l tr14NE(2) v4 apply blast 
  using Van.reach_validFromS_reach \<phi>_def \<phi> r(3) ssv1l 
  apply (smt (verit, del_insts)) 
  using Van.reach_validFromS_reach \<phi>_def \<phi> r(4) ssv2l
  apply (smt (verit, del_insts)) .
 
  have stat: "statAA = Diff \<longrightarrow> statOO = Diff" 
  and \<Delta>: "\<Delta> ww ww1 ww2 ss1 ss2 statAA ssv1 ssv2 statOO"
  using \<phi> unfolding \<phi>_def ss1[symmetric] ss2[symmetric] ssv1[symmetric] ssv2[symmetric] by auto 

  note vs13 = s13'[unfolded ss1[symmetric]] note vs24 = s24'[unfolded ss2[symmetric]]
  have "\<exists> w1' w2' trv1' trv2' statA' statO'. 
  \<phi>a \<Delta> \<infinity> ww1 ww2 w1' w2' statAA ss1 [ss1,s1'] ss2 [ss2,s2'] (sstatA' statAA ss1 ss2) statOO ssv1 trv1' ssv2 trv2' statO'"
  using unwindCond_ex_\<phi>a_getActO[OF unwind \<Delta> rss stat vs13 vs24 iss14 giss14]
  by blast
 
  then obtain w1' w2' trv1' trv2' statA' statO' where 
  \<phi>1: "\<phi>a \<Delta> \<infinity> ww1 ww2 w1' w2' statAA ss1 [ss1,s1'] ss2 [ss2,s2'] statA' statOO ssv1 trv1' ssv2 trv2' statO'" by auto

  have trv12'NE: "trv1' \<noteq> []" "trv2' \<noteq> []" using \<phi>1 unfolding \<phi>a_def by auto

  have [simp]: "Van.O (butlast trv1 @ trv1') = Van.O trv1 @ Van.O trv1'"
  using trv12'NE unfolding \<phi>_def Van.O.map_filter Opt.O.map_filter apply(subst butlast_append) by simp

  have [simp]: "Van.O (butlast trv2 @ trv2') = Van.O trv2 @ Van.O trv2'"
  using trv12'NE unfolding \<phi>_def Van.O.map_filter Opt.O.map_filter apply(subst butlast_append) by simp

  have "Van.A trv1' = Van.A trv2'" using \<phi>1 unfolding \<phi>a_def by auto
  moreover have "length (Van.O trv1') = length (Van.A trv1') \<and> length (Van.O trv2') = length (Van.A trv2')" 
  unfolding Van.A.map_filter Van.O.map_filter by auto
  ultimately have "length (Van.O trv1') = length (Van.O trv2')" by auto
  hence [simp]: "Van.O trv1 @ Van.O trv1' = Van.O trv2 @ Van.O trv2' \<longleftrightarrow> 
    Van.O trv1 = Van.O trv2 \<and> Van.O trv1' = Van.O trv2'" by auto

  have len: "trv1 \<noteq> [] \<and> trv2 \<noteq> [] \<and> trv1' \<noteq> [] \<and> trv2' \<noteq> [] \<and>
    (Suc 0 < length trv1 \<or> ww1 \<le> w1) \<and> 
    (Suc 0 < length trv1' \<or> w1' < ww1) \<and> 
    (Suc 0 < length trv2 \<or> ww2 \<le> w2) \<and> 
    (Suc 0 < length trv2' \<or> w2' < ww2)"
  using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def by auto

  show ?thesis 
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ "butlast trv1 @ trv1'"]) apply(rule exI[of _ "butlast trv2 @ trv2'"])
  apply(rule exI[of _ statA']) apply(rule exI[of _ statO'])
  unfolding \<phi>a_def apply(intro conjI)
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def by auto
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def by auto
    subgoal using len  
    by simp (metis Suc_lessI add_is_1 diff_is_0_eq length_greater_0_conv linorder_not_less 
       order_trans trans_less_add2)
    subgoal using len 
    by simp (metis Suc_leI le_add_diff_inverse2 length_greater_0_conv nless_le order_le_less_trans trans_less_add2)
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def ssv1  
      using Van.validFromS_append by auto
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def ssv2  
      using Van.validFromS_append by auto
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def Van.S.map_filter Opt.S.map_filter 
    apply(subst tr1l) apply(subst butlast_append) by simp
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def Van.S.map_filter Opt.S.map_filter  
    apply(subst tr2l) apply(subst butlast_append) by simp
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def Van.A.map_filter Opt.A.map_filter  
    apply(subst trv1l) apply(subst trv2l) 
    apply(subst butlast_append) apply simp apply(subst butlast_append) by simp
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def apply simp 
    apply(cases "Opt.O tr1 = Opt.O tr2", simp_all) apply clarify  
      using status.exhaust by (metis (full_types))+
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def apply simp 
    apply(cases "Opt.O tr1 = Opt.O tr2", simp_all) apply clarify  
      apply (smt (verit, del_insts) status.exhaust)
      by (metis Opt.O.eq_Nil_iff nev(1) nev(2)) 
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def by simp
    subgoal using \<phi> \<phi>1 unfolding \<phi>_def \<phi>a_def by simp
    subgoal using \<phi>1 trv12'NE tr14NE unfolding \<phi>_def \<phi>a_def lastt_def by simp .
qed

lemma unwindCond_ex_\<phi>a_aux2:
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "(statA = Diff \<longrightarrow> statO = Diff)" 
and v3': "Opt.validFromS s1 (tr1 @ [s1',s1''])" and v4': "Opt.validFromS s2 (tr2 @ [s2',s2''])" 
and i: "isIntO s1'" "isIntO s2'"  
and A34: "getActO s1' = getActO s2'" 
and nev: "never isIntO tr1" "never isIntO tr2"
shows "\<exists>w1' w2' trv1 trv2 statAA statOO. 
   \<phi>a \<Delta> \<infinity> w1 w2 w1' w2' statA s1 (tr1 @ [s1',s1'']) s2 (tr2 @ [s2',s2'']) statAA statO sv1 trv1 sv2 trv2 statOO"
proof-
  have 0: "lastt s1 (tr1 ## s1') = s1'" "lastt s2 (tr2 ## s2') = s2'"
  unfolding lastt_def by auto
  show ?thesis 
  apply(rule unwindCond_ex_\<phi>a'_aux[OF unwind \<Delta> r stat, of "tr1 ## s1'" "tr2 ## s2'", unfolded 0, simplified])
  using assms by auto
qed

lemma lastt_snoc[simp]: "lastt s1 (tr1 @ [s1'']) = s1''"
unfolding lastt_def by auto

lemma lastt_snoc2[simp]: "lastt s1 (tr1 @ [s1', s1'']) = s1''"
unfolding lastt_def by auto

lemma append_snoc2: "tr1 @ [s1', s1''] = (tr1 ## s1') ## s1''"
by auto
 
(* final version to be used in corecursion for as long as there is an "isIntO" on ltr1 or ltr2:  *)
definition "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO \<equiv>
  (trv1 \<noteq> [] \<or> w1' < w1) \<and> (trv2 \<noteq> [] \<or> w2' < w2) \<and> 
  Van.validFromS sv1 (trv1 ## sv1'') \<and> Van.validFromS sv2 (trv2 ## sv2'') \<and>
  Van.S (trv1 ## sv1'') = Opt.S ((tr1 ## s1') ## s1'') \<and> Van.S (trv2 ## sv2'') = Opt.S ((tr2 ## s2') ## s2'') \<and>
  Van.A (trv1 ## sv1'') = Van.A (trv2 ## sv2'') \<and>
  (statO = Eq \<longrightarrow> (statOO = Diff) = (Van.O (trv1 ## sv1'') \<noteq> Van.O (trv2 ## sv2''))) \<and>
  (statA = Eq \<longrightarrow> (statAA = Diff) = (Opt.O ((tr1 ## s1') ## s1'') \<noteq> Opt.O ((tr2 ## s2') ## s2''))) \<and>
  (statO = Diff \<longrightarrow> statOO = Diff) \<and> (statAA = Diff \<longrightarrow> statOO = Diff) \<and> 
  \<Delta> \<infinity> w1' w2' s1'' s2'' statAA sv1'' sv2'' statOO"

proposition unwindCond_ex_\<phi>':
assumes unwind: "unwindCond \<Delta>" and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff" 
and v3': "Opt.validFromS s1 ((tr1 ## s1') ## s1'')" and v4': "Opt.validFromS s2 ((tr2 ## s2') ## s2'')" 
and i: "isIntO s1'" "isIntO s2'"  
and A34: "getActO s1' = getActO s2'" 
and nev: "never isIntO tr1" "never isIntO tr2"
shows "\<exists>w1' w2' trv1 sv1'' trv2 sv2'' statAA statOO. 
   \<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
using unwindCond_ex_\<phi>a_aux2[unfolded \<phi>_def, unfolded lastt_snoc lastt_snoc2 append_snoc2, OF assms]
unfolding \<phi>a_def apply(elim exE) subgoal for w1' w2' trv1 trv2 statAA statOO
apply(cases "trv1" rule: rev_cases)
  subgoal by auto
  apply(cases "trv2" rule: rev_cases)
    subgoal by auto
    subgoal unfolding \<phi>'_def apply simp by blast . .


(* FOR the NON-INTER PART, when ltr1 and ltr2 are now left with "never interA"
(i.e., interaction is exhausted)... 
First, when secrets are not yet exhausted: 
*)

definition "\<chi>3 \<Delta> w (w1::enat) w2 w1' w2' s1 tr1 s2 statAA sv1 trv1 sv2 trv2 statOO \<equiv> 
  trv1 \<noteq> [] \<and> trv2 \<noteq> [] \<and> (length trv2 > Suc 0 \<or> w2' \<le> w2) \<and> 
  Van.validFromS sv1 trv1 \<and> Van.validFromS sv2 trv2 \<and> 
  never isSecV (butlast trv1) \<and> 
  isSecV (lastt sv1 trv1) \<and> getSecV (lastt sv1 trv1) = getSecO (lastt s1 tr1) \<and> 
  never isSecV (butlast trv2) \<and> 
  Van.A trv1 = Van.A trv2 \<and> 
  \<Delta> w w1' w2' (lastt s1 tr1) s2 statAA (lastt sv1 trv1) (lastt sv2 trv2) statOO"

lemma \<chi>3_final: 
assumes unw: "unwindCond \<Delta>"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and vtr1: "Opt.validFromS s1 tr1" 
and \<chi>3: "\<chi>3 \<Delta> w w1 w2 w1' w2' s1 tr1 s2 statAA sv1 trv1 sv2 trv2 statOO" 
shows "(finalV (lastt sv1 trv1) \<longleftrightarrow> finalO (lastt s1 tr1)) \<and> (finalV (lastt sv2 trv2) \<longleftrightarrow> finalO s2)"
proof-
  have rsv12: "Van.validFromS sv1 trv1 \<longrightarrow> reachV (lastt sv1 trv1)" 
           "Van.validFromS sv2 trv2 \<longrightarrow> reachV (lastt sv2 trv2)" using r 
    by (simp add: Van.reach_validFromS_reach lastt_def)+
  have rs1: "Opt.validFromS s1 tr1 \<longrightarrow> reachO (lastt s1 tr1)" 
  using r 
    by (simp add: Opt.reach_validFromS_reach lastt_def)+
  show ?thesis using \<chi>3[unfolded \<chi>3_def] rsv12 rs1 using unw[unfolded unwindCond_def, rule_format, 
     of "lastt s1 tr1" s2 "lastt sv1 trv1" "lastt sv2 trv2" w w1' w2' statAA statOO]
  using vtr1 `reachO s2` by auto
qed

lemma \<chi>3_completedFrom: "unwindCond \<Delta> \<Longrightarrow> 
reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
Opt.validFromS s1 tr1 \<Longrightarrow> completedFromO s1 tr1 \<Longrightarrow>  
\<chi>3 \<Delta> w w1 w2 w1' w2' s1 tr1 s2 statAA sv1 trv1 sv2 trv2 statOO 
\<Longrightarrow> completedFromV sv1 trv1 \<and> completedFromV sv2 trv2"
by (metis Van.final_not_isSec \<chi>3_def \<chi>3_final completedFromO_lastt)

lemma unwindCond_ex_\<chi>3: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2" 
and vtr1: "Opt.validFromS s1 tr1"   
and nis1: "\<not> isIntO s1" and nis2: "\<not> isIntO s2"
and inter3: "never isIntO tr1" 
and sec: "never isSecO (butlast tr1)" "isSecO (lastt s1 tr1)" 
shows "\<exists>w' w1' w2' trv1 trv2 statOO. \<chi>3 \<Delta> w' w1 w2 w1' w2' s1 tr1 s2 statA sv1 trv1 sv2 trv2 statOO"
using assms(2-) 
proof(induction "length tr1" w
  arbitrary: w1 w2 s1 s2 statA sv1 sv2 statO tr1 rule: less2_induct')
  case (less w tr1 w1 w2 s1 s2 statA sv1 sv2 statO)
  note vtr1 = less(8)

  note \<Delta> = `\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO`
  note nis1 = less(9) note nis2 = less(10) 
  note inter3 = less(11)
  note sec3 = less(12,13)
  note r34 = less.prems(2,3) note r12 = less.prems(4,5)
  note r = r34 r12 
  note r3 = r34(1) note r4 = r34(2) note r1 = r12(1) note r2 = r12(2)

  have i34: "statA = Eq \<longrightarrow> isIntO s1 = isIntO s2"
  and f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2" 
    using \<Delta> unwind[unfolded unwindCond_def] r by auto 

  have proact_match: "(\<exists>v<w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
  using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w" 
    assume "proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
     assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv1'
     where 0:"validTransV (sv1,sv1')"
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2 statO"
     unfolding move_1_def by auto
     have r1': "reachV sv1'" using r1 0 by (metis Van.reach.Step fst_conv snd_conv)
     obtain w' w1' w2' trv1 trv2 statOO where \<chi>3: "\<chi>3 \<Delta> w' w1 w2 w1' w2' s1 tr1 s2 statA sv1' trv1 sv2 trv2 statOO" 
     using less(2)[OF v, of tr1 w1 w2 s1 s2 statA sv1' sv2 statO, 
                   simplified, OF \<Delta> r34 r1' r2 vtr1 nis1 nis2 inter3 sec3] by auto
     show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
     using \<chi>3 0 sv1 unfolding \<chi>3_def by auto
    next 
     assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv2'
     where 0: "validTransV (sv2,sv2')"
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1 sv2' statO"
     unfolding move_2_def by auto
     have r2': "reachV sv2'" using r2 0 by (metis Van.reach.Step fst_conv snd_conv)
     obtain w' w1' w2' trv1 trv2 statOO where \<chi>3: "\<chi>3 \<Delta> w' w1 w2 w1' w2' s1 tr1 s2 statA sv1 trv1 sv2' trv2 statOO" 
     using less(2)[OF v, of tr1 w1 w2 s1 s2 statA sv1 sv2' statO, 
          simplified, OF \<Delta> r34 r1 r2' vtr1 nis1 nis2 inter3 sec3] by auto
     show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ trv1]) apply(rule exI[of _ "sv2 # trv2"])
     using \<chi>3 0 sv2 unfolding \<chi>3_def by auto
    next
     assume sv12: "\<not> isSecV sv1" "\<not> isSecV sv2" "Van.eqAct sv1 sv2" 
     and "move_12 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv1' sv2' statO'
     where 0: "statO' = sstatO' statO sv1 sv2"
     "validTransV (sv1,sv1') " "\<not> isSecV sv1"
     "validTransV (sv2,sv2')" "\<not> isSecV sv2"
     "Van.eqAct sv1 sv2"
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2' statO'"
     unfolding move_12_def by auto
     have r12': "reachV sv1'" "reachV sv2'" using r1 r2 0 by (metis Van.reach.Step fst_conv snd_conv)+

     obtain w' w1' w2' trv1 trv2 statOO where \<chi>3: "\<chi>3 \<Delta> w' w1 w2 w1' w2' s1 tr1 s2 statA sv1' trv1 sv2' trv2 statOO" 
     using less(2)[OF v, of tr1 w1 w2 s1 s2 statA sv1' sv2' statO', 
                   simplified, OF \<Delta> r34 r12' vtr1 nis1 nis2 inter3 sec3] by auto
     show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
     apply(rule exI[of _ statOO])
     using \<chi>3 0 sv12 unfolding \<chi>3_def sstatO'_def
     by (auto simp: Van.eqAct_def)    
    qed
  next
    assume m: "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
    define statA' where statA': "statA' = sstatA' statA s1 s2" 
    show ?thesis
    proof(cases "length tr1 \<le> Suc 0") 
     case True
     hence tr1e: "tr1 = [] \<or> tr1 = [s1]" 
     by (metis Opt.validFromS_singl_iff Suc_length_conv le_Suc_eq le_zero_eq length_0_conv vtr1) 
     hence "Opt.A tr1 = []" by (simp add: True) 
     have is1: "isSecO s1" 
       by (metis last.simps lastt_def sec3(2) tr1e)
     hence "\<not> finalO s1" using Opt.final_not_isSec by blast
     then obtain s1' where s13': "validTransO (s1, s1')" unfolding Opt.final_def by auto
     hence isv1: "isSecV sv1 \<and> getSecV sv1 = getSecO s1" using m is1 nis1
     unfolding react_def match1_def eqSec_def by auto
     show ?thesis using tr1e isv1 apply-
       apply(rule exI[of _ w]) apply(rule exI[of _ w1]) apply(rule exI[of _ w2]) 
       apply(rule exI[of _ "[sv1]"], rule exI[of _ "[sv2]"], rule exI[of _ statO]) 
       using tr1e 
       using f34 \<Delta> by (clarsimp simp: \<chi>3_def lastt_def)
    next
     case False 
     then obtain s13 tr1' where tr1: "tr1 = s13 # tr1'" and tr1'NE: "tr1' \<noteq> []"
       by (cases tr1, auto) 
     have s13[simp]: "s13 = s1" using `Opt.validFromS s1 tr1`
         by (simp add: Opt.validFromS_Cons_iff tr1)
     obtain s1' where
     trn3: "validTransO (s1,s1')" and 
     tr1': "Opt.validFromS s1' tr1'" using `Opt.validFromS s1 tr1` 
     unfolding tr1 s13 by (metis tr1'NE Simple_Transition_System.validFromS_Cons_iff)
     have r3': "reachO s1'" using r3 trn3 by (metis Opt.reach.Step fst_conv snd_conv)
     have f3: "\<not> finalO s1" using Opt.final_def trn3 by blast
     hence f4: "\<not> finalO s2" using f34 by blast
     have nev3': "never isIntO tr1'"
     using inter3 tr1 tr1'NE by auto
     have isAO3: "\<not> isIntO s1" by (simp add: nis1)  
     have O33': "Opt.O tr1 = Opt.O tr1'" "Opt.A tr1 = Opt.A tr1'" 
     using isAO3 unfolding tr1 by auto
     have m: "match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
     have "(\<exists>w1'<w1. \<exists>w2'<w2. \<not> isSecO s1 \<and> \<Delta> \<infinity> w1' w2' s1' s2 statA sv1 sv2 statO) \<or> 
          (\<exists>w2'<w2. eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> match1_1 \<Delta> \<infinity> w2' s1 s1' s2 statA sv1 sv2 statO) \<or> 
          (eqSec sv1 s1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> match1_12 \<Delta> \<infinity> \<infinity> s1 s1' s2 statA sv1 sv2 statO)" 
     using m isAO3 trn3 unfolding match1_def by auto
     thus ?thesis 
     proof safe 
       fix w1'' w2'' assume w12': "w1'' < w1" "w2'' < w2"
       assume "\<not> isSecO s1" and \<Delta>: "\<Delta> \<infinity> w1'' w2'' s1' s2 statA sv1 sv2 statO"
       hence S3: "Opt.S tr1' = Opt.S tr1" unfolding tr1 by auto
       obtain w' w1' w2' trv1 trv2 statOO where \<chi>3: "\<chi>3 \<Delta> w' w1'' w2'' w1' w2' s1' tr1' s2 statA sv1 trv1 sv2 trv2 statOO"
       using less(1)[of tr1', OF _ \<Delta> r3' r4 r12 _] unfolding tr1   
       by simp (metis Opt.S.eq_Nil_iff(2) S3 Opt.validFromS_def \<open>\<not> isSecO s1\<close> last.simps 
       lastt_def list_all_hd nev3' nis2 s13 sec3(1) sec3(2) tr1 tr1')
       show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "trv1"]) apply(rule exI[of _ trv2])
       using \<chi>3 O33' unfolding \<chi>3_def tr1 Van.completedFrom_def
       using Van.validFromS_Cons tr1'NE tr1' trn3 isAO3 w12' by auto
     next
       fix w2'' assume w2': "w2'' < w2"
       assume trn13: "eqSec sv1 s1" and
       Atrn1: "\<not> isIntV sv1" and "match1_1 \<Delta> \<infinity> w2'' s1 s1' s2 statA sv1 sv2 statO"
       then obtain sv1' where
       trn1: "validTransV (sv1,sv1')" and
       \<Delta>: "\<Delta> \<infinity> \<infinity> w2'' s1' s2 statA sv1' sv2 statO"
       unfolding match1_1_def by auto 
       have r1': "reachV sv1'"using r1 trn1 by (metis Van.reach.Step fst_conv snd_conv)
       obtain w' w1' w2' trv1 trv2 statOO where \<chi>3: "\<chi>3 \<Delta> w' \<infinity> w2'' w1' w2' s1' tr1' s2 statA sv1' trv1 sv2 trv2 statOO"

       using less(1)[of tr1', OF _ \<Delta> r3' r4 r1' r2, unfolded O33', simplified]
       using less.prems tr1' f3 f4 tr1'NE trn3 O33'(1)
       unfolding tr1  
       by simp (metis Opt.validFromS_def list_all_hd)
       show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
       using \<chi>3 O33' unfolding \<chi>3_def tr1 Van.completedFrom_def
       using Van.validFromS_Cons trn1 tr1'NE tr1' trn3
       using isAO3 Atrn1 eqSec_S_Cons trn13 w2'  
       by simp (metis Opt.S.Nil_iff Opt.S.eq_Nil_iff(1) eqSec_def nless_le order_le_less_trans s13 sec3(1) tr1) 
     next
       assume sv2: "\<not> isSecV sv2" and trn13: "eqSec sv1 s1" and
       Atrn12: "Van.eqAct sv1 sv2" and "match1_12 \<Delta> \<infinity> \<infinity> s1 s1' s2 statA sv1 sv2 statO"
       then obtain sv1' sv2' statO' where 
       statO': "statO' = sstatO' statO sv1 sv2" and 
       trn1: "validTransV (sv1,sv1') " and 
       trn2: "validTransV (sv2,sv2')" and 
       \<Delta>: "\<Delta> \<infinity> \<infinity> \<infinity> s1' s2 statA sv1' sv2' statO'"
       unfolding match1_12_def by auto 
       have r12': "reachV sv1'" "reachV sv2'" 
       using r1 trn1 r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)+
       obtain w' w1' w2' trv1 trv2 statOO where \<chi>3: "\<chi>3 \<Delta> w' \<infinity> \<infinity> w1' w2' s1' tr1' s2 statA sv1' trv1 sv2' trv2 statOO"
       using less(1)[of tr1', OF _ \<Delta> r3' r4 r12', unfolded O33', simplified]
       using less.prems tr1' f3 f4 tr1'NE trn3 O33'(1) unfolding tr1 statO' sstatO'_def  
       by simp (metis Simple_Transition_System.validFromS_def list_all_hd)+
       show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
       using \<chi>3 O33' tr1'NE sv2 
       using Van.validFromS_Cons trn1 trn2 
       using isAO3 Atrn12 eqSec_S_Cons trn13 f3 f34 s13 tr1' trn3
       unfolding \<chi>3_def tr1 Van.completedFrom_def Van.eqAct_def  
       using Van.A.Cons_unfold eqSec_def sec3(1) tr1 by auto
     qed
    qed
  qed
qed

definition \<chi>3a where "\<chi>3a \<Delta> w (w1::enat) w2 w1' w2' s1 s1' s2 statAA sv1 trv1 sv2 trv2 statOO \<equiv>
trv1 \<noteq> [] \<and> trv2 \<noteq> [] \<and> (length trv2 > Suc 0 \<or> w2' < w2) \<and> 
Van.validFromS sv1 trv1 \<and> Van.validFromS sv2 trv2 \<and>
Van.S trv1 = [getSecO s1] \<and>
never isSecV (butlast trv2) \<and> 
Van.A trv1 = Van.A trv2 \<and> 
\<Delta> w w1' w2' s1' s2 statAA (lastt sv1 trv1) (lastt sv2 trv2) statOO"

lemma unwindCond_ex_\<chi>3a_getSec: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r34: "reachO s1" "reachO s2" and r12: "reachV sv1" "reachV sv2" 
and v: "validTransO (s1, s1')" 
and ii3: "\<not> isIntO s1" 
and is1: "isSecO s1" and isv13: "isSecV sv1" "getSecO s1 = getSecV sv1"  
shows "\<exists>w1' w2' trv1 trv2 statOO.
       \<chi>3a \<Delta> \<infinity> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv2 trv2 statOO"
using \<Delta> r12 isv13
proof(induction w arbitrary: w1 w2 sv1 sv2 statO rule: less_induct)
  case (less w w1 w2 sv1 sv2 statO)
  note \<Delta> = `\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO`
  note r12 = less.prems(2,3)
  note r1 = r12(1) note r2 = r12(2)
  note r = r34 r12
  note isv13 = `isSecV sv1` `getSecO s1 = getSecV sv1`

  have f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2" 
    using \<Delta> unwind[unfolded unwindCond_def] r by auto

  have proact_match: "(\<exists>v<w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
  using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w" 
    assume "proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
      assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      hence False using isv13 by blast
      thus ?thesis by auto
    next 
      assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      then obtain sv2'
      where 0: "validTransV (sv2,sv2')"  
      and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1 sv2' statO"  
      unfolding move_2_def by auto
      have r2': "reachV sv2'" using r2 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain w1' w2' trv1 trv2 statOO where 
      \<chi>3a: "\<chi>3a \<Delta> \<infinity> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv2' trv2 statOO" 
      using less(1)[OF v \<Delta> r1 r2' isv13] by auto
      show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "sv2 # trv2"])
      using \<chi>3a 0 sv2 unfolding \<chi>3a_def by auto
    next
      assume sv12: "\<not> isSecV sv1" "\<not> isSecV sv2" "Van.eqAct sv1 sv2" 
      and "move_12 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      hence False using isv13 by blast
      thus ?thesis by auto
    qed
  next
    assume m: "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" 
    have m: "match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
    have "(\<exists>w1' w2'. w1'<w1 \<and> w2'<w2 \<and> \<not> isSecO s1 \<and> \<Delta> \<infinity> w1' w2' s1' s2 statA sv1 sv2 statO) \<or> 
          (\<exists>w2'< w2. eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> match1_1 \<Delta> \<infinity> w2' s1 s1' s2 statA sv1 sv2 statO) \<or> 
          (eqSec sv1 s1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> match1_12 \<Delta> \<infinity> \<infinity> s1 s1' s2 statA sv1 sv2 statO)" 
    using m v ii3 unfolding match1_def by auto

    thus ?thesis 
    apply(elim disjE exE)
      subgoal for w1' w2' using is1 by auto
      subgoal for w2' apply(rule exI[of _ \<infinity>]) apply(rule exI[of _ w2'])
      unfolding match1_1_def apply(elim conjE exE) subgoal for sv1'
      apply(rule exI[of _ "[sv1,sv1']"]) apply(rule exI[of _ "[sv2]"])
      apply(rule exI[of _ statO])
      using is1 isv13 unfolding \<chi>3a_def  
      by (auto simp : sstatA'_def lastt_def) .
      subgoal apply(rule exI[of _ \<infinity>]) apply(rule exI[of _ \<infinity>])
      unfolding match1_12_def apply(elim conjE exE) subgoal for sv1' sv2'
      apply(rule exI[of _ "[sv1,sv1']"]) apply(rule exI[of _ "[sv2,sv2']"])
      apply(rule exI[of _ "sstatO' statO sv1 sv2"])
      using is1 isv13 unfolding \<chi>3a_def  
      by (auto simp : sstatA'_def sstatO'_def lastt_def Van.eqAct_def) . .
  qed
qed

(* 
thm unwindCond_ex_\<chi>3[no_vars]
thm \<chi>3_def[no_vars]
*)

definition "\<chi>3b \<Delta> w (w1::enat) w2 w1' w2' s1 tr1 s2 statAA sv1 trv1 sv2 trv2 statOO \<equiv>
trv1 \<noteq> [] \<and>
trv2 \<noteq> [] \<and> (length trv2 > Suc 0 \<or> w2' < w2) \<and> 
Van.validFromS sv1 trv1 \<and>
Van.validFromS sv2 trv2 \<and>
Van.S trv1 = Opt.S tr1 \<and> 
never isSecV (butlast trv2) \<and> Van.A trv1 = Van.A trv2 \<and> 
\<Delta> w w1' w2' (lastt s1 tr1) s2 statAA (lastt sv1 trv1) (lastt sv2 trv2) statOO"

lemma unwindCond_ex_\<chi>3b_aux: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" and 
r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"  
and tr1NE: "tr1 \<noteq> []" 
and v3': "Opt.validFromS s1 (tr1 ## s1')"   
and nis1: "\<not> isIntO s1" and nis2: "\<not> isIntO s2"
and ninter3': "never isIntO (tr1 ## s1')" 
and sec: "never isSecO (butlast tr1)" "isSecO (lastt s1 tr1)" 
shows "\<exists>w1' w2' trv1 trv2 statOO. \<chi>3b \<Delta> \<infinity> w1 w2 w1' w2' s1 (tr1 ## s1') s2 statA sv1 trv1 sv2 trv2 statOO"
proof-
  have v3: "Opt.validFromS s1 tr1" and s13': "validTransO (lastt s1 tr1,s1')"
  apply (metis v3' Opt.validFromS_def Opt.validS_append1 Nil_is_append_conv hd_append2)
  by (metis Opt.validFromS_def Opt.validS_validTrans lastt_def list.sel(1) not_Cons_self2 snoc_eq_iff_butlast tr1NE v3')

  have ninter3: "never isIntO tr1" and nis1': "\<not> isIntO s1'"
  using ninter3' by auto
  obtain ww ww1 ww2 trv1 trv2 statOO where \<chi>3: "\<chi>3 \<Delta> ww w1 w2 ww1 ww2 s1 tr1 s2 statA sv1 trv1 sv2 trv2 statOO"
  using unwindCond_ex_\<chi>3[OF unwind \<Delta> r v3 nis1 nis2 ninter3 sec] by auto

  have trv12NE: "trv1 \<noteq> []" "trv2 \<noteq> []" using \<chi>3 unfolding \<chi>3_def by auto
  
  define ss1 ssv1 ssv2 where ss1: "ss1 \<equiv> lastt s1 tr1" 
  and ssv1: "ssv1 \<equiv> lastt sv1 trv1" and ssv2: "ssv2 \<equiv> lastt sv2 trv2"

  have ss1l: "ss1 = last tr1" by (simp add: lastt_def ss1 tr1NE)
  have tr1l: "tr1 = butlast tr1 @ [ss1]" by (simp add: ss1l tr1NE)  
  have ssv1l: "ssv1 = last trv1" using \<chi>3 unfolding \<chi>3_def by (metis lastt_def ssv1)
  have trv1l: "trv1 = butlast trv1 @ [ssv1]" by (simp add: ssv1l trv12NE(1))
  have ssv2l: "ssv2 = last trv2" using \<chi>3 unfolding \<chi>3_def by (metis lastt_def ssv2)
  have trv2l: "trv2 = butlast trv2 @ [ssv2]" by (simp add: ssv2l trv12NE(2))

  have iss1[simp]: "isSecO ss1" using sec(2) unfolding ss1 by auto
  have issv1[simp]: "isSecV ssv1" and gissv13[simp]: "getSecO ss1 = getSecV ssv1"  
  using \<chi>3 unfolding \<chi>3_def ssv1 ss1 by auto

  have niss1: "\<not> isIntO ss1"  
    by (metis list_all_append list_all_simps(1) ninter3 tr1l)

  have rss1: "reachO ss1" and rssv12: "reachV ssv1" "reachV ssv2" 
  using Opt.reach_validFromS_reach r ss1l tr1NE v3 apply blast 
  apply (metis Van.reach_validFromS_reach \<chi>3_def \<chi>3 r(3) ssv1l)
  by (metis Van.reach_validFromS_reach \<chi>3_def \<chi>3 r(4) ssv2l)
 
  have \<Delta>: "\<Delta> ww ww1 ww2 ss1 s2 statA ssv1 ssv2 statOO"
  using \<chi>3 unfolding \<chi>3_def ss1[symmetric] ssv1[symmetric] ssv2[symmetric] by auto 

  have s13': "validTransO (ss1, s1')"  
    by (simp add: s13' ss1)

  note vs13 = s13'[unfolded ss1[symmetric]]  
  obtain w1' w2' trv1' trv2' statO' where 
  \<chi>3a: "\<chi>3a \<Delta> \<infinity> ww1 ww2 w1' w2' ss1 s1' s2 statA ssv1 trv1' ssv2 trv2' statO'"
  using unwindCond_ex_\<chi>3a_getSec[OF unwind \<Delta> rss1 r(2) rssv12 s13' niss1 iss1 issv1 gissv13] 
  by blast
 
  have trv12'NE: "trv1' \<noteq> []" "trv2' \<noteq> []" using \<chi>3a unfolding \<chi>3a_def by auto

  have [simp]: "Van.O (butlast trv1 @ trv1') = Van.O trv1 @ Van.O trv1'"
  using trv12'NE unfolding \<chi>3_def Van.O.map_filter Opt.O.map_filter apply(subst butlast_append) by simp

  have [simp]: "Van.O (butlast trv2 @ trv2') = Van.O trv2 @ Van.O trv2'"
  using trv12'NE unfolding \<chi>3_def Van.O.map_filter Opt.O.map_filter apply(subst butlast_append) by simp

  have "Van.A trv1' = Van.A trv2'" using \<chi>3a unfolding \<chi>3a_def by auto
  moreover have "length (Van.O trv1') = length (Van.A trv1') \<and> length (Van.O trv2') = length (Van.A trv2')" 
  unfolding Van.A.map_filter Van.O.map_filter by auto
  ultimately have "length (Van.O trv1') = length (Van.O trv2')" by auto
  hence [simp]: "Van.O trv1 @ Van.O trv1' = Van.O trv2 @ Van.O trv2' \<longleftrightarrow> 
    Van.O trv1 = Van.O trv2 \<and> Van.O trv1' = Van.O trv2'" by auto

  show ?thesis 
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ "butlast trv1 @ trv1'"]) apply(rule exI[of _ "butlast trv2 @ trv2'"])
  apply(rule exI[of _ statO'])
  unfolding \<chi>3b_def apply(intro conjI)
    subgoal using \<chi>3 \<chi>3a unfolding \<chi>3_def \<chi>3a_def by auto
    subgoal using \<chi>3 \<chi>3a unfolding \<chi>3_def \<chi>3a_def by auto
    subgoal using \<chi>3 \<chi>3a unfolding \<chi>3_def \<chi>3a_def 
    by simp (metis Simple_Transition_System.fromS_eq_Nil Simple_Transition_System.toS_fromS_nonSingl Van.toS_Nil diff_add_inverse2 linorder_not_less order_le_less_trans trans_less_add2 zero_less_diff) 
    subgoal using \<chi>3 \<chi>3a unfolding \<chi>3_def \<chi>3a_def ssv1  
      using Van.validFromS_append by auto
    subgoal using \<chi>3 \<chi>3a unfolding \<chi>3_def \<chi>3a_def ssv2  
      using Van.validFromS_append by auto 
    subgoal using \<chi>3 \<chi>3a unfolding \<chi>3_def \<chi>3a_def unfolding Van.S.map_filter Opt.S.map_filter  
    apply(subst tr1l) apply(subst butlast_append)   
      by simp (metis Opt.S.map_filter Opt.S.eq_Nil_iff(2) Van.S.map_filter Van.S.eq_Nil_iff(2) sec(1))
    subgoal using \<chi>3 \<chi>3a unfolding \<chi>3_def \<chi>3a_def  
      by (simp add: butlast_append)
    subgoal using \<chi>3 \<chi>3a unfolding \<chi>3_def \<chi>3a_def Van.A.map_filter Opt.A.map_filter  
    apply(subst trv1l) apply(subst trv2l) by (simp add: butlast_append) 
    subgoal using \<chi>3a trv12'NE tr1NE unfolding \<chi>3a_def lastt_def by simp .
qed

lemma unwindCond_ex_\<chi>3b_aux2: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2" 
and v3': "Opt.validFromS s1 (tr1 @ [s1',s1''])"   
and nis1: "\<not> isIntO s1" and nis2: "\<not> isIntO s2"
and ninter3': "never isIntO (tr1 @ [s1',s1''])" 
and sec: "never isSecO tr1" "isSecO s1'" 
shows "\<exists>w1' w2' trv1 trv2 statOO. \<chi>3b \<Delta> \<infinity> w1 w2 w1' w2' s1 (tr1 @ [s1',s1'']) s2 statA sv1 trv1 sv2 trv2 statOO"
proof-
  have 0: "lastt s1 (tr1 ## s1') = s1'"  
  unfolding lastt_def by auto
  show ?thesis 
  using unwindCond_ex_\<chi>3b_aux[OF unwind \<Delta> r, of "tr1 ## s1'", unfolded 0, simplified]
  using assms by auto
qed

(* 
thm unwindCond_ex_\<chi>3b_aux2[unfolded \<phi>_def, unfolded lastt_snoc lastt_snoc2 append_snoc2]

thm \<chi>3b_def[where ?tr1.0 = "tr1 @ [s1', s1'']" and 
  ?trv1.0 = "trv1 ## sv1''" and ?trv2.0 = "trv2 ## sv2''", 
  unfolded lastt_snoc lastt_snoc2 append_snoc2, no_vars]
*)

definition "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statAA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO \<equiv>
  Van.validFromS sv1 (trv1 ## sv1'') \<and> Van.validFromS sv2 (trv2 ## sv2'') \<and>
  Van.S (trv1 ## sv1'') = Opt.S ((tr1 ## s1') ## s1'') \<and> never isSecV trv2 \<and> 
  Van.A (trv1 ## sv1'') = Van.A (trv2 ## sv2'') \<and> 
  trv1 \<noteq> [] \<and> (trv2 \<noteq> [] \<or> w2' < w2) \<and> 
  \<Delta> \<infinity> w1' w2' s1'' s2 statAA sv1'' sv2'' statOO"

(* Final version, for non-inter and left-sec corecursive step: *)
proposition unwindCond_ex_\<chi>3': 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" and 
r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2" 
and v3': "Opt.validFromS s1 ((tr1 ## s1') ## s1'')"   
and nis1: "\<not> isIntO s1" and nis2: "\<not> isIntO s2"
and ninter3': "never isIntO ((tr1 ## s1') ## s1'')" 
and sec: "never isSecO tr1" "isSecO s1'" 
shows "\<exists>w1' w2' trv1 sv1'' trv2 sv2'' statOO. \<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
using unwindCond_ex_\<chi>3b_aux2[unfolded \<phi>_def, unfolded lastt_snoc lastt_snoc2 append_snoc2, OF assms]
unfolding \<chi>3b_def apply(elim exE) subgoal for w1' w2' trv1 trv2 statOO
apply(cases "trv1" rule: rev_cases)
  subgoal by auto
  subgoal for trv1' sv1'' apply(cases "trv2" rule: rev_cases)
    subgoal by auto
    subgoal for trv2' sv2'' unfolding \<chi>3'_def 
    apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
    apply(rule exI[of _ trv1']) apply(rule exI[of _ sv1''])
    apply(rule exI[of _ trv2']) apply(rule exI[of _ sv2''])
    apply(rule exI[of _ statOO]) 
    by simp (metis Opt.S.Nil_iff Opt.S.eq_Nil_iff(1) Van.S.simps(4) append_snoc2 list_all_append sec(2) 
    self_append_conv2 snoc_eq_iff_butlast) . . .

(* finally, for when the secrets are exhausted too: *)
definition "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statAA sv1 trv1 sv1' sv2 trv2 sv2' statOO \<equiv>
  Van.validFromS sv1 (trv1 ## sv1') \<and> Van.validFromS sv2 (trv2 ## sv2') \<and>
  never isSecV trv1 \<and> never isSecV trv2 \<and>  
  Van.A (trv1 ## sv1') = Van.A (trv2 ## sv2') \<and> 
  (trv1 \<noteq> [] \<or> w1' < w1) \<and> (trv2 \<noteq> [] \<or> w2' < w2) \<and> 
  \<Delta> \<infinity> w1' w2' s1' s2 statAA sv1' sv2' statOO"

proposition unwindCond_ex_\<omega>3: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r34: "reachO s1" "reachO s2" and r12: "reachV sv1" "reachV sv2" 
and v3: "validTransO (s1,s1')"   
and nis1: "\<not> isIntO s1" "\<not> isIntO s1'" "\<not> isSecO s1"  
and nis2: "\<not> isIntO s2"
shows "\<exists>w1' w2' trv1 sv1' trv2 sv2' statOO. \<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
using \<Delta> r12  
proof(induction w arbitrary: w1 w2 sv1 sv2 statO rule: less_induct)
  case (less w w1 w2 sv1 sv2 statO)
  note \<Delta> = `\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO`
  note r12 = less.prems(2,3)
  note r1 = r12(1) note r2 = r12(2)
  note r = r34 r12 

  have f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2" 
    using \<Delta> unwind[unfolded unwindCond_def] r by auto

  have proact_match: "(\<exists>v<w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
  using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w" 
    assume "proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
      assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      then obtain sv1' where 0: "validTransV (sv1, sv1')" and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2 statO" 
      unfolding move_1_def by auto
      have r1': "reachV sv1'" using r1 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain w1' w2' trv1 sv1'' trv2 sv2' statOO where 
      \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1' trv1 sv1'' sv2 trv2 sv2' statOO" 
      using less(1)[OF v \<Delta> r1' r2] by auto 
      show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv1''"]) 
      apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "sv2'"])
      using \<omega>3 0 sv1 unfolding \<omega>3_def by auto
    next 
      assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      then obtain sv2'
      where 0: "validTransV (sv2,sv2')"  
      and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1 sv2' statO"  
      unfolding move_2_def by auto
      have r2': "reachV sv2'" using r2 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain w1' w2' trv1 sv1' trv2 sv2'' statOO where 
      \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2' trv2 sv2'' statOO" 
      using less(1)[OF v \<Delta> r1 r2'] by auto 
      show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
      apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "sv1'"])
      apply(rule exI[of _ "sv2 # trv2"]) apply(rule exI[of _ "sv2''"]) 
      using \<omega>3 0 sv2 unfolding \<omega>3_def by auto
    next
      assume sv1: "\<not> isSecV sv1" and  sv2: "\<not> isSecV sv2"  and 
      "move_12 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO" and 
      sv12: "Van.eqAct sv1 sv2"
      then obtain sv1' sv2' statO'
      where statO': "statO' = sstatO' statO sv1 sv2"
      and 0: "validTransV (sv1,sv1')"  "validTransV (sv2,sv2')"  
      and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2' statO'"  
      unfolding move_12_def by auto
      have r1': "reachV sv1'" and r2': "reachV sv2'" using r1 r2 0 
      by (metis Van.reach.Step fst_conv snd_conv)+
      obtain w1' w2' trv1 sv1'' trv2 sv2'' statOO where 
      \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1' trv1 sv1'' sv2' trv2 sv2'' statOO" 
      using less(1)[OF v \<Delta> r1' r2'] by auto 
      show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
      apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv1''"]) 
      apply(rule exI[of _ "sv2 # trv2"]) apply(rule exI[of _ "sv2''"]) 
      using \<omega>3 0 sv1 sv2 sv12 unfolding \<omega>3_def statO' by (auto simp: Van.eqAct_def)
    qed
  next
    assume m: "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" 
    have m: "match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
    have "(\<exists>w1' w2'. w1' < w1 \<and> w2'<w2 \<and> \<not> isSecO s1 \<and> \<Delta> \<infinity> w1' w2' s1' s2 statA sv1 sv2 statO) \<or> 
          (\<exists>w2'<w2. eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> match1_1 \<Delta> \<infinity> w2' s1 s1' s2 statA sv1 sv2 statO) \<or> 
          (eqSec sv1 s1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> match1_12 \<Delta> \<infinity> \<infinity> s1 s1' s2 statA sv1 sv2 statO)" 
    using m v3 nis1 unfolding match1_def by auto

    thus ?thesis 
    apply(elim disjE exE) 
      subgoal for w1' w2'   
      apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w2'"])
      apply(rule exI[of _ "[]"]) apply(rule exI[of _ "sv1"]) 
      apply(rule exI[of _ "[]"]) apply(rule exI[of _ "sv2"]) 
      apply(rule exI[of _ statO]) unfolding \<omega>3_def 
      by auto  
      subgoal for w2'
      apply(rule exI[of _ "\<infinity>"]) apply(rule exI[of _ "w2'"])
      unfolding match1_1_def apply(elim conjE exE) subgoal for sv1'
      apply(rule exI[of _ "[sv1]"]) apply(rule exI[of _ "sv1'"]) 
      apply(rule exI[of _ "[]"]) apply(rule exI[of _ "sv2"]) 
      apply(rule exI[of _ statO])
      unfolding \<omega>3_def using nis1(3) by (auto simp: eqSec_def) .
      subgoal 
      apply(rule exI[of _ "\<infinity>"]) apply(rule exI[of _ "\<infinity>"])
      unfolding match1_12_def apply(elim conjE exE) subgoal for sv1' sv2'
      apply(rule exI[of _ "[sv1]"]) apply(rule exI[of _ "sv1'"]) 
      apply(rule exI[of _ "[sv2]"]) apply(rule exI[of _ "sv2'"]) 
      apply(rule exI[of _ "sstatO' statO sv1 sv2"])
      unfolding \<omega>3_def using nis1(3) apply (auto simp: eqSec_def
      sstatA'_def sstatO'_def lastt_def Van.eqAct_def) . . .
  qed
qed


(* Now on the right-side: *)

definition "\<chi>4 \<Delta> w w1 (w2::enat) w1' w2' s1 s2 tr2 statAA sv1 trv1 sv2 trv2 statOO \<equiv> 
  trv1 \<noteq> [] \<and> trv2 \<noteq> [] \<and> (length trv1 > Suc 0 \<or> w1' \<le> w1) \<and> 
  Van.validFromS sv1 trv1 \<and> Van.validFromS sv2 trv2 \<and> 
  never isSecV (butlast trv1) \<and> 
  never isSecV (butlast trv2) \<and> 
  isSecV (lastt sv2 trv2) \<and> getSecV (lastt sv2 trv2) = getSecO (lastt s2 tr2) \<and> 
  Van.A trv1 = Van.A trv2 \<and> 
  \<Delta> w w1' w2' s1 (lastt s2 tr2) statAA (lastt sv1 trv1) (lastt sv2 trv2) statOO"

lemma \<chi>4_final: 
assumes unw: "unwindCond \<Delta>"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and vtr2: "Opt.validFromS s2 tr2" 
and \<chi>4: "\<chi>4 \<Delta> w w1 w2 w1' w2' s1 s2 tr2 statAA sv1 trv1 sv2 trv2 statOO" 
shows "(finalV (lastt sv1 trv1) \<longleftrightarrow> finalO s1) \<and> (finalV (lastt sv2 trv2) \<longleftrightarrow> finalO (lastt s2 tr2))"
proof-
  have rsv12: "Van.validFromS sv1 trv1 \<longrightarrow> reachV (lastt sv1 trv1)" 
           "Van.validFromS sv2 trv2 \<longrightarrow> reachV (lastt sv2 trv2)" using r 
    by (simp add: Van.reach_validFromS_reach lastt_def)+
  have rs2: "Opt.validFromS s2 tr2 \<longrightarrow> reachO (lastt s2 tr2)" 
  using r 
    by (simp add: Opt.reach_validFromS_reach lastt_def)+
  show ?thesis using \<chi>4[unfolded \<chi>4_def] rsv12 rs2 using unw[unfolded unwindCond_def, rule_format, 
     of s1 "lastt s2 tr2" "lastt sv1 trv1" "lastt sv2 trv2" w w1' w2' statAA statOO]
  using vtr2 `reachO s1` by auto
qed

lemma \<chi>4_completedFrom: "unwindCond \<Delta> \<Longrightarrow> 
reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
Opt.validFromS s2 tr2 \<Longrightarrow> completedFromO s2 tr2 \<Longrightarrow>  
\<chi>4 \<Delta> w w1 w2 w1' w2' s1 s2 tr2 statAA sv1 trv1 sv2 trv2 statOO 
\<Longrightarrow> completedFromV sv1 trv1 \<and> completedFromV sv2 trv2"
by (metis Van.final_not_isSec \<chi>4_def \<chi>4_final completedFromO_lastt)

proposition unwindCond_ex_\<chi>4: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2" 
and vtr2: "Opt.validFromS s2 tr2"   
and nis2: "\<not> isIntO s1" and nis2: "\<not> isIntO s2"
and inter4: "never isIntO tr2" 
and sec: "never isSecO (butlast tr2)" "isSecO (lastt s2 tr2)" 
shows "\<exists>w' w1' w2' trv1 trv2 statOO. \<chi>4 \<Delta> w' w1 w2 w1' w2' s1 s2 tr2 statA sv1 trv1 sv2 trv2 statOO"
using assms(2-) 
proof(induction "length tr2" w
  arbitrary: w1 w2 s1 s2 statA sv1 sv2 statO tr2 rule: less2_induct')
  case (less w tr2 w1 w2 s1 s2 statA sv1 sv2 statO)
  note vtr2 = less(8)
  note \<Delta> = `\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO`
  note nis1 = less(9) note nis2 = less(10) 
  note inter4 = less(11)
  note sec4 = less(12,13)
  note r34 = less.prems(2,3) note r12 = less.prems(4,5)
  note r = r34 r12 
  note r3 = r34(1) note r4 = r34(2) note r1 = r12(1) note r2 = r12(2)

  have i34: "statA = Eq \<longrightarrow> isIntO s1 = isIntO s2"
  and f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2" 
    using \<Delta> unwind[unfolded unwindCond_def] r by auto 

  have proact_match: "(\<exists>v<w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
  using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w" 
    assume "proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
     assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv1'
     where 0:"validTransV (sv1,sv1')"
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2 statO"
     unfolding move_1_def by auto
     have r1': "reachV sv1'" using r1 0 by (metis Van.reach.Step fst_conv snd_conv)
     obtain w' w1' w2' trv1 trv2 statOO where \<chi>4: "\<chi>4 \<Delta> w' w1 w2 w1' w2' s1 s2 tr2 statA sv1' trv1 sv2 trv2 statOO" 
     using less(2)[OF v, of tr2 w1 w2 s1 s2 statA sv1' sv2 statO, 
                   simplified, OF \<Delta> r34 r1' r2 vtr2 nis1 nis2 inter4 sec4] by auto
     show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
     using \<chi>4 0 sv1 unfolding \<chi>4_def by auto
    next 
     assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv2'
     where 0: "validTransV (sv2,sv2')"
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1 sv2' statO"
     unfolding move_2_def by auto
     have r2': "reachV sv2'" using r2 0 by (metis Van.reach.Step fst_conv snd_conv)
     obtain w1' w2' w' trv1 trv2 statOO where \<chi>4: "\<chi>4 \<Delta> w' w1 w2 w1' w2' s1 s2 tr2 statA sv1 trv1 sv2' trv2 statOO" 
     using less(2)[OF v, of tr2 w1 w2 s1 s2 statA sv1 sv2' statO, 
          simplified, OF \<Delta> r34 r1 r2' vtr2 nis1 nis2 inter4 sec4] by auto
     show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ trv1]) apply(rule exI[of _ "sv2 # trv2"])
     using \<chi>4 0 sv2 unfolding \<chi>4_def by auto
    next
     assume sv12: "\<not> isSecV sv1" "\<not> isSecV sv2" "Van.eqAct sv1 sv2" 
     and "move_12 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
     then obtain sv1' sv2' statO'
     where 0: "statO' = sstatO' statO sv1 sv2"
     "validTransV (sv1,sv1') " "\<not> isSecV sv1"
     "validTransV (sv2,sv2')" "\<not> isSecV sv2"
     "Van.eqAct sv1 sv2"
     and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2' statO'"
     unfolding move_12_def by auto
     have r12': "reachV sv1'" "reachV sv2'" using r1 r2 0 by (metis Van.reach.Step fst_conv snd_conv)+
     obtain w' w1' w2' trv1 trv2 statOO where \<chi>4: "\<chi>4 \<Delta> w' w1 w2 w1' w2' s1 s2 tr2 statA sv1' trv1 sv2' trv2 statOO" 
     using less(2)[OF v, of tr2 w1 w2 s1 s2 statA sv1' sv2' statO', 
                   simplified, OF \<Delta> r34 r12' vtr2 nis1 nis2 inter4 sec4] by auto
     show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
     apply(rule exI[of _ statOO])
     using \<chi>4 0 sv12 unfolding \<chi>4_def sstatO'_def
     by (auto simp: Van.eqAct_def)    
    qed
  next
    assume m: "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
    define statA' where statA': "statA' = sstatA' statA s1 s2" 
    show ?thesis
    proof(cases "length tr2 \<le> Suc 0") 
     case True
     hence tr2e: "tr2 = [] \<or> tr2 = [s2]" 
       by (metis Opt.validFromS_def Suc_length_conv le_Suc_eq le_zero_eq length_0_conv list.sel(1) vtr2)
     hence "Opt.A tr2 = []" by (simp add: True) 
     have is2: "isSecO s2" 
       by (metis last.simps lastt_def sec4(2) tr2e)
     hence "\<not> finalO s2" using Opt.final_not_isSec by blast
     then obtain s2' where s24': "validTransO (s2, s2')" unfolding Opt.final_def by auto
     hence isv2: "isSecV sv2 \<and> getSecV sv2 = getSecO s2" using m is2 nis2
     unfolding react_def match2_def eqSec_def by auto
     show ?thesis using tr2e isv2 apply-
       apply(rule exI[of _ w]) apply(rule exI[of _ w1]) apply(rule exI[of _ w2]) 
       apply(rule exI[of _ "[sv1]"], rule exI[of _ "[sv2]"], rule exI[of _ statO]) 
       using tr2e 
       using f34 \<Delta> by(clarsimp simp: \<chi>4_def lastt_def)
    next
     case False 
     then obtain s24 tr2' where tr2: "tr2 = s24 # tr2'" and tr2'NE: "tr2' \<noteq> []"
       by (cases tr2, auto) 
     have s24[simp]: "s24 = s2" using `Opt.validFromS s2 tr2`
         by (simp add: Opt.validFromS_Cons_iff tr2)
     obtain s2' where
     trn4: "validTransO (s2,s2')" and 
     tr2': "Opt.validFromS s2' tr2'" using `Opt.validFromS s2 tr2` 
     unfolding tr2 s24 by (metis tr2'NE Simple_Transition_System.validFromS_Cons_iff)
     have r4': "reachO s2'" using r4 trn4 by (metis Opt.reach.Step fst_conv snd_conv)
     have f4: "\<not> finalO s2" using Opt.final_def trn4 by blast
     hence f3: "\<not> finalO s1" using f34 by blast
     have nev4': "never isIntO tr2'"
     using inter4 tr2 tr2'NE by auto
     have isAO4: "\<not> isIntO s2" by (simp add: nis2)  
     have O44': "Opt.O tr2 = Opt.O tr2'" "Opt.A tr2 = Opt.A tr2'" 
     using isAO4 unfolding tr2 by auto
     have m: "match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
     have "(\<exists>w1'<w1. \<exists>w2'<w2. \<not> isSecO s2 \<and> \<Delta> \<infinity> w1' w2' s1 s2' statA sv1 sv2 statO) \<or> 
          (\<exists>w1'<w1. eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> match2_1 \<Delta> w1' \<infinity> s1 s2 s2' statA sv1 sv2 statO) \<or> 
          (eqSec sv2 s2 \<and> \<not> isSecV sv1 \<and> Van.eqAct sv1 sv2 \<and> match2_12 \<Delta> \<infinity> \<infinity> s1 s2 s2' statA sv1 sv2 statO)" 
     using m isAO4 trn4 unfolding match2_def by auto
     thus ?thesis 
     proof safe 
       fix w1'' w2'' assume w12': "w1'' < w1" "w2'' < w2" 
       assume "\<not> isSecO s2" and \<Delta>: "\<Delta> \<infinity> w1'' w2'' s1 s2' statA sv1 sv2 statO"
       hence S4: "Opt.S tr2' = Opt.S tr2" unfolding tr2 by auto
       obtain w' w1' w2' trv1 trv2 statOO where \<chi>4: "\<chi>4 \<Delta> w' w1'' w2'' w1' w2' s1 s2' tr2' statA sv1 trv1 sv2 trv2 statOO"
       using less(1)[of tr2', OF _ \<Delta> r3 r4' r12] unfolding tr2   
       by simp (metis Opt.S.eq_Nil_iff(2) S4 Simple_Transition_System.validFromS_def last.simps lastt_def 
       list.discI list_all_hd nev4' nis1 sec4(1) sec4(2) tr2 tr2' tr2'NE) 
       show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "trv1"]) apply(rule exI[of _ trv2])
       using \<chi>4 O44' unfolding \<chi>4_def tr2 Van.completedFrom_def
       using Van.validFromS_Cons tr2'NE tr2' trn4 isAO4 w12' by auto 
     next
       fix w1'' assume w1': "w1'' < w1"
       assume trn24: "eqSec sv2 s2" and
       Atrn2: "\<not> isIntV sv2" and "match2_1 \<Delta> w1'' \<infinity> s1 s2 s2' statA sv1 sv2 statO"
       then obtain sv2' where
       trn2: "validTransV (sv2,sv2') " and
       \<Delta>: "\<Delta> \<infinity> w1'' \<infinity> s1 s2' statA sv1 sv2' statO"
       unfolding match2_1_def by auto 
       have r2': "reachV sv2'"using r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)
       obtain w' w1' w2' trv1 trv2 statOO where \<chi>4: "\<chi>4 \<Delta> w' w1'' \<infinity> w1' w2' s1 s2' tr2' statA sv1 trv1 sv2' trv2 statOO"
       using less(1)[of tr2', OF _ \<Delta> r3 r4' r1 r2', unfolded O44', simplified]
       using less.prems tr2' f3 f4 tr2'NE trn4 O44'(1)
       unfolding tr2 
       by simp (metis Opt.validFromS_def list_all_hd)
       show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "sv2 # trv2"])
       using \<chi>4 O44' unfolding \<chi>4_def tr2 Van.completedFrom_def
       using Van.validFromS_Cons trn2 tr2'NE tr2' trn4
       using isAO4 Atrn2 eqSec_S_Cons trn24 w1'   
       by simp (metis Opt.S.Nil_iff Opt.S.eq_Nil_iff(1) eqSec_def nless_le order_le_less_trans s24 sec4(1) tr2)
     next
       assume sv1: "\<not> isSecV sv1" and trn24: "eqSec sv2 s2" and
       Atrn12: "Van.eqAct sv1 sv2" and "match2_12 \<Delta> \<infinity> \<infinity> s1 s2 s2' statA sv1 sv2 statO"
       then obtain sv1' sv2' statO' where 
       statO': "statO' = sstatO' statO sv1 sv2" and 
       trn1: "validTransV (sv1,sv1') " and 
       trn2: "validTransV (sv2,sv2')" and 
       \<Delta>: "\<Delta> \<infinity> \<infinity> \<infinity> s1 s2' statA sv1' sv2' statO'"
       unfolding match2_12_def by auto 
       have r12': "reachV sv1'" "reachV sv2'" 
       using r1 trn1 r2 trn2 by (metis Van.reach.Step fst_conv snd_conv)+
       obtain w' w1' w2' trv1 trv2 statOO where \<chi>4: "\<chi>4 \<Delta> w' \<infinity> \<infinity> w1' w2' s1 s2' tr2' statA sv1' trv1 sv2' trv2 statOO"
       using less(1)[of tr2', OF _ \<Delta> r3 r4' r12', unfolded O44', simplified]
       using less.prems tr2' f3 f4 tr2'NE trn4 O44'(1) unfolding tr2 statO' sstatO'_def 
       by simp (metis Simple_Transition_System.validFromS_def list_all_hd)
       show ?thesis apply(rule exI[of _ w']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
       apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
       using \<chi>4 O44' tr2'NE sv1
       using Van.validFromS_Cons trn1 trn2 
       using isAO4 Atrn12 eqSec_S_Cons trn24 f3 f34 s24 tr2' trn4
       unfolding \<chi>4_def tr2 Van.completedFrom_def Van.eqAct_def  
       using Van.A.Cons_unfold eqSec_def sec4(1) tr2 by auto
     qed
    qed
  qed
qed

definition \<chi>4a where "\<chi>4a \<Delta> w w1 (w2::enat) w1' w2' s1 s2 s2' statAA sv1 trv1 sv2 trv2 statOO \<equiv>
trv1 \<noteq> [] \<and> trv2 \<noteq> [] \<and> (length trv1 > Suc 0 \<or> w1' < w1) \<and> 
Van.validFromS sv1 trv1 \<and> Van.validFromS sv2 trv2 \<and>
never isSecV (butlast trv1) \<and> 
Van.S trv2 = [getSecO s2] \<and>
Van.A trv1 = Van.A trv2 \<and>  
\<Delta> w w1' w2' s1 s2' statAA (lastt sv1 trv1) (lastt sv2 trv2) statOO"

lemma unwindCond_ex_\<chi>4a_getSec: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r34: "reachO s1" "reachO s2" and r12: "reachV sv1" "reachV sv2" 
and v: "validTransO (s2, s2')" 
and ii4: "\<not> isIntO s2" 
and is2: "isSecO s2" and isv24: "isSecV sv2" "getSecO s2 = getSecV sv2"  
shows "\<exists>w1' w2' trv1 trv2 statOO.
       \<chi>4a \<Delta> \<infinity> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv2 trv2 statOO"
using \<Delta> r12 isv24
proof(induction w arbitrary: w1 w2 sv1 sv2 statO rule: less_induct)
  case (less w w1 w2 sv1 sv2 statO)
  note \<Delta> = `\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO`
  note r12 = less.prems(2,3)
  note r1 = r12(1) note r2 = r12(2)
  note r = r34 r12
  note isv24 = `isSecV sv2` `getSecO s2 = getSecV sv2`

  have f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2" 
    using \<Delta> unwind[unfolded unwindCond_def] r by auto

  have proact_match: "(\<exists>v<w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
  using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w" 
    assume "proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
      assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      then obtain sv1'
      where 0: "validTransV (sv1,sv1')"  
      and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2 statO"  
      unfolding move_1_def by auto
      have r1': "reachV sv1'" using r1 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain w1' w2' trv1 trv2 statOO where 
      \<chi>4a: "\<chi>4a \<Delta> \<infinity> w1 w2 w1' w2' s1 s2 s2' statA sv1' trv1 sv2 trv2 statOO" 
      using less(1)[OF v \<Delta> r1' r2 isv24] by auto
      show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "trv2"])
      using \<chi>4a 0 sv1 unfolding \<chi>4a_def by auto
    next
      assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      hence False using isv24 by blast
      thus ?thesis by auto
    next
      assume sv12: "\<not> isSecV sv1" "\<not> isSecV sv2" "Van.eqAct sv1 sv2" 
      and "move_12 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      hence False using isv24 by blast
      thus ?thesis by auto
    qed
  next
    assume m: "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" 
    have m: "match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
    have "(\<exists>w1' w2'. w1'<w1 \<and> w2'<w2 \<and> \<not> isSecO s2 \<and> \<Delta> \<infinity> w1' w2' s1 s2' statA sv1 sv2 statO) \<or> 
          (\<exists>w1'<w1. eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> match2_1 \<Delta> w1' \<infinity> s1 s2 s2' statA sv1 sv2 statO) \<or> 
          (eqSec sv2 s2 \<and> \<not> isSecV sv1 \<and> Van.eqAct sv1 sv2 \<and> match2_12 \<Delta> \<infinity> \<infinity> s1 s2 s2' statA sv1 sv2 statO)" 
    using m v ii4 unfolding match2_def by auto

    thus ?thesis 
    apply(elim disjE exE)
      subgoal for w1' w2' using is2 by auto
      subgoal for w1' apply(rule exI[of _ w1']) apply(rule exI[of _ \<infinity>])
      unfolding match2_1_def apply(elim conjE exE) subgoal for sv2'
      apply(rule exI[of _ "[sv1]"]) apply(rule exI[of _ "[sv2,sv2']"])
      apply(rule exI[of _ statO])
      using is2 isv24 unfolding \<chi>4a_def  
      by (auto simp : sstatA'_def lastt_def) .
      subgoal apply(rule exI[of _ \<infinity>]) apply(rule exI[of _ \<infinity>])
      unfolding match2_12_def apply(elim conjE exE) subgoal for sv1' sv2'
      apply(rule exI[of _ "[sv1,sv1']"]) apply(rule exI[of _ "[sv2,sv2']"])
      apply(rule exI[of _ "sstatO' statO sv1 sv2"])
      using is2 isv24 unfolding \<chi>4a_def  
      by (auto simp : sstatA'_def sstatO'_def lastt_def Van.eqAct_def) . .
  qed
qed

definition "\<chi>4b \<Delta> w w1 w2 w1' (w2'::enat) s1 s2 tr2 statAA sv1 trv1 sv2 trv2 statOO \<equiv>
trv1 \<noteq> [] \<and> trv2 \<noteq> [] \<and> (length trv1 > Suc 0 \<or> w1' < w1) \<and> 
Van.validFromS sv1 trv1 \<and> Van.validFromS sv2 trv2 \<and>
never isSecV (butlast trv1) \<and> 
Van.S trv2 = Opt.S tr2 \<and> 
Van.A trv1 = Van.A trv2 \<and> 
\<Delta> w w1' w2' s1 (lastt s2 tr2) statAA (lastt sv1 trv1) (lastt sv2 trv2) statOO"

lemma unwindCond_ex_\<chi>4b_aux: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2" 
and tr2NE: "tr2 \<noteq> []" 
and v4': "Opt.validFromS s2 (tr2 ## s2')"   
and nis1: "\<not> isIntO s1" and nis2: "\<not> isIntO s2"
and ninter4': "never isIntO (tr2 ## s2')" 
and sec: "never isSecO (butlast tr2)" "isSecO (lastt s2 tr2)" 
shows "\<exists>w1' w2' trv1 trv2 statOO. \<chi>4b \<Delta> \<infinity> w1 w2 w1' w2' s1 s2 (tr2 ## s2') statA sv1 trv1 sv2 trv2 statOO"
proof-
  have v4: "Opt.validFromS s2 tr2" and s24': "validTransO (lastt s2 tr2,s2')"
  apply (metis v4' Opt.validFromS_def Opt.validS_append1 Nil_is_append_conv hd_append2)
  by (metis Opt.validFromS_def Opt.validS_validTrans append_is_Nil_conv lastt_def list.distinct(1) list.sel(1) tr2NE v4')
  
  have ninter4: "never isIntO tr2" and nis2': "\<not> isIntO s2'"
  using ninter4' by auto
  obtain ww ww1 ww2 trv1 trv2 statOO where \<chi>4: "\<chi>4 \<Delta> ww w1 w2 ww1 ww2 s1 s2 tr2 statA sv1 trv1 sv2 trv2 statOO"
  using unwindCond_ex_\<chi>4[OF unwind \<Delta> r v4 nis1 nis2 ninter4 sec] 
  by auto

  have trv12NE: "trv1 \<noteq> []" "trv2 \<noteq> []" using \<chi>4 unfolding \<chi>4_def by auto
  
  define ss2 ssv1 ssv2 where ss2: "ss2 \<equiv> lastt s2 tr2" 
  and ssv1: "ssv1 \<equiv> lastt sv1 trv1" and ssv2: "ssv2 \<equiv> lastt sv2 trv2"

  have ss2l: "ss2 = last tr2" by (simp add: lastt_def ss2 tr2NE)
  have tr2l: "tr2 = butlast tr2 @ [ss2]" by (simp add: ss2l tr2NE)  
  have ssv1l: "ssv1 = last trv1" using \<chi>4 unfolding \<chi>4_def by (metis lastt_def ssv1)
  have trv1l: "trv1 = butlast trv1 @ [ssv1]" by (simp add: ssv1l trv12NE(1))
  have ssv2l: "ssv2 = last trv2" using \<chi>4 unfolding \<chi>4_def by (metis lastt_def ssv2)
  have trv2l: "trv2 = butlast trv2 @ [ssv2]" by (simp add: ssv2l trv12NE(2))

  have iss2[simp]: "isSecO ss2" using sec(2) unfolding ss2 by auto
  have issv2[simp]: "isSecV ssv2" and gissv24[simp]: "getSecO ss2 = getSecV ssv2"  
  using \<chi>4 unfolding \<chi>4_def ssv2 ss2 by auto

  have niss2: "\<not> isIntO ss2"  
    by (metis list_all_append list_all_simps(1) ninter4 tr2l)

  have rss2: "reachO ss2" and rssv12: "reachV ssv1" "reachV ssv2" 
  using Opt.reach_validFromS_reach r ss2l tr2NE v4 apply blast 
  unfolding ssv1 ssv2 using r(3,4) using \<chi>4 unfolding \<chi>4_def  
  using Van.reach_validFromS_reach ssv1 ssv2 ssv1l ssv2l by auto metis+

  have \<Delta>: "\<Delta> ww ww1 ww2 s1 ss2 statA ssv1 ssv2 statOO"
  using \<chi>4 unfolding \<chi>4_def ss2[symmetric] ssv1[symmetric] ssv2[symmetric] by auto 

  have s13': "validTransO (ss2, s2')"  
    by (simp add: s24' ss2)

  note vs24 = s24'[unfolded ss2[symmetric]]  
  obtain w1' w2' trv1' trv2' statO' where 
  \<chi>4a: "\<chi>4a \<Delta> \<infinity> ww1 ww2 w1' w2' s1 ss2 s2' statA ssv1 trv1' ssv2 trv2' statO'"
  using unwindCond_ex_\<chi>4a_getSec[OF unwind \<Delta> r(1) rss2 rssv12 s13' niss2 iss2 issv2 gissv24]
  by blast
 
  have trv12'NE: "trv1' \<noteq> []" "trv2' \<noteq> []" using \<chi>4a unfolding \<chi>4a_def by auto

  have [simp]: "Van.O (butlast trv1 @ trv1') = Van.O trv1 @ Van.O trv1'"
  using trv12'NE unfolding \<chi>4_def Van.O.map_filter Opt.O.map_filter apply(subst butlast_append) by simp

  have [simp]: "Van.O (butlast trv2 @ trv2') = Van.O trv2 @ Van.O trv2'"
  using trv12'NE unfolding \<chi>4_def Van.O.map_filter Opt.O.map_filter apply(subst butlast_append) by simp

  have "Van.A trv1' = Van.A trv2'" using \<chi>4a unfolding \<chi>4a_def by auto
  moreover have "length (Van.O trv1') = length (Van.A trv1') \<and> length (Van.O trv2') = length (Van.A trv2')" 
  unfolding Van.A.map_filter Van.O.map_filter by auto
  ultimately have "length (Van.O trv1') = length (Van.O trv2')" by auto
  hence [simp]: "Van.O trv1 @ Van.O trv1' = Van.O trv2 @ Van.O trv2' \<longleftrightarrow> 
    Van.O trv1 = Van.O trv2 \<and> Van.O trv1' = Van.O trv2'" by auto

  show ?thesis 
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ "butlast trv1 @ trv1'"]) apply(rule exI[of _ "butlast trv2 @ trv2'"])
  apply(rule exI[of _ statO'])
  unfolding \<chi>4b_def apply(intro conjI)
    subgoal using \<chi>4 \<chi>4a unfolding \<chi>4_def \<chi>4a_def by auto
    subgoal using \<chi>4 \<chi>4a unfolding \<chi>4_def \<chi>4a_def by auto
    subgoal using \<chi>4 \<chi>4a unfolding \<chi>4_def \<chi>4a_def  
      by simp (metis Simple_Transition_System.fromS_eq_Nil Van.toS_Nil Van.toS_fromS_nonSingl 
      diff_add_inverse2 linorder_not_less order_le_less_trans trans_less_add2 zero_less_diff)  
    subgoal using \<chi>4 \<chi>4a unfolding \<chi>4_def \<chi>4a_def ssv1  
      using Van.validFromS_append by auto
    subgoal using \<chi>4 \<chi>4a unfolding \<chi>4_def \<chi>4a_def ssv2  
      using Van.validFromS_append by auto 
    subgoal using \<chi>4 \<chi>4a unfolding \<chi>4_def \<chi>4a_def  
      by (simp add: butlast_append)
    subgoal using \<chi>4 \<chi>4a unfolding \<chi>4_def \<chi>4a_def unfolding Van.S.map_filter Opt.S.map_filter  
    apply(subst tr2l) apply(subst butlast_append)  
      by simp (metis Opt.S.map_filter Opt.S.eq_Nil_iff Van.S.map_filter Van.S.eq_Nil_iff sec(1))
    subgoal using \<chi>4 \<chi>4a unfolding \<chi>4_def \<chi>4a_def Van.A.map_filter Opt.A.map_filter  
    apply(subst trv1l) apply(subst trv2l) 
    apply(subst butlast_append) apply simp apply(subst butlast_append) by simp
    subgoal using \<chi>4a trv12'NE tr2NE unfolding \<chi>4a_def lastt_def by simp .
qed

lemma unwindCond_ex_\<chi>4b_aux2: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" and 
r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2" 
and v4': "Opt.validFromS s2 (tr2 @ [s2',s2''])"   
and nis1: "\<not> isIntO s1" and nis2: "\<not> isIntO s2"
and ninter4': "never isIntO (tr2 @ [s2',s2''])" 
and sec: "never isSecO tr2" "isSecO s2'" 
shows "\<exists>w1' w2' trv1 trv2 statOO. \<chi>4b \<Delta> \<infinity> w1 w2 w1' w2' s1 s2 (tr2 @ [s2',s2'']) statA sv1 trv1 sv2 trv2 statOO"
proof-
  have 0: "lastt s2 (tr2 ## s2') = s2'"  
  unfolding lastt_def by auto
  show ?thesis 
  using unwindCond_ex_\<chi>4b_aux[OF unwind \<Delta> r, of "tr2 ## s2'", unfolded 0, simplified]
  using assms by auto
qed

(* 
thm unwindCond_ex_\<chi>4b_aux2[unfolded \<phi>_def, unfolded lastt_snoc lastt_snoc2 append_snoc2]

thm \<chi>4b_def[where ?tr2.0 = "tr2 @ [s2', s2'']" and 
  ?trv1.0 = "trv1 ## sv1''" and ?trv2.0 = "trv2 ## sv2''", 
  unfolded lastt_snoc lastt_snoc2 append_snoc2, no_vars]
*)

definition "\<chi>4' \<Delta> w1 w2 w1' (w2'::enat) s1 s2 tr2 s2' s2'' statAA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO \<equiv>
  Van.validFromS sv1 (trv1 ## sv1'') \<and> Van.validFromS sv2 (trv2 ## sv2'') \<and>
  never isSecV (butlast (trv1 ## sv1'')) \<and>
  Van.S (trv2 ## sv2'') = Opt.S ((tr2 ## s2') ## s2'') \<and>
  Van.A (trv1 ## sv1'') = Van.A (trv2 ## sv2'') \<and> 
  trv2 \<noteq> [] \<and> (trv1 \<noteq> [] \<or> w1' < w1) \<and> 
  \<Delta> \<infinity> w1' w2' s1 s2'' statAA sv1'' sv2'' statOO"

(* Final version, for non-inter right-sec corecursive step: *)
proposition unwindCond_ex_\<chi>4': 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" and 
r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2" 
and v4': "Opt.validFromS s2 ((tr2 ## s2') ## s2'')"   
and nis1: "\<not> isIntO s1" and nis2: "\<not> isIntO s2"
and ninter4': "never isIntO ((tr2 ## s2') ## s2'')" 
and sec: "never isSecO tr2" "isSecO s2'"  
shows "\<exists>w1' w2' trv1 sv1'' trv2 sv2'' statOO. \<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
using unwindCond_ex_\<chi>4b_aux2[unfolded \<phi>_def, unfolded lastt_snoc lastt_snoc2 append_snoc2, OF assms]
unfolding \<chi>4b_def apply(elim exE) subgoal for w1' w2' trv1 trv2 statOO
apply(cases "trv1" rule: rev_cases)
  subgoal by auto
  subgoal for trv1' sv1'' apply(cases "trv2" rule: rev_cases)
    subgoal by auto
    subgoal for trv2' sv2'' unfolding \<chi>4'_def 
    apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
    apply(rule exI[of _ trv1']) apply(rule exI[of _ sv1''])
    apply(rule exI[of _ trv2']) apply(rule exI[of _ sv2''])
    apply(rule exI[of _ statOO])   
    by simp (metis Opt.S.Nil_iff Opt.S.eq_Nil_iff(1) Van.S.simps(4) butlast_append 
     list.discI list_all_append sec(2) self_append_conv2) . . . 

(*****) 
(* finally, for when the secrets are exhausted too: *)
definition "\<omega>4 \<Delta> w1 w2 w1' (w2'::enat) s1 s2 s2' statAA sv1 trv1 sv1' sv2 trv2 sv2' statOO \<equiv>
  Van.validFromS sv1 (trv1 ## sv1') \<and> Van.validFromS sv2 (trv2 ## sv2') \<and>
  never isSecV trv1 \<and> never isSecV trv2 \<and>  
  Van.A (trv1 ## sv1') = Van.A (trv2 ## sv2') \<and> 
  (trv1 \<noteq> [] \<or> w1' < w1) \<and> (trv2 \<noteq> [] \<or> w2' < w2) \<and> 
  \<Delta> \<infinity> w1' w2' s1 s2' statAA sv1' sv2' statOO"

proposition unwindCond_ex_\<omega>4: 
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO" 
and r34: "reachO s1" "reachO s2" and r12: "reachV sv1" "reachV sv2"  
and nis1: "\<not> isIntO s1" 
and v4: "validTransO (s2,s2')" 
and nis2: "\<not> isIntO s2" "\<not> isIntO s2'" "\<not> isSecO s2"  
shows "\<exists>w1' w2' trv1 sv1' trv2 sv2' statOO. \<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
using \<Delta> r12  
proof(induction w arbitrary: w1 w2 sv1 sv2 statO rule: less_induct)
  case (less w w1 w2 sv1 sv2 statO)
  note \<Delta> = `\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO`
  note r12 = less.prems(2,3)
  note r1 = r12(1) note r2 = r12(2)
  note r = r34 r12 

  have f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2" 
    using \<Delta> unwind[unfolded unwindCond_def] r by auto

  have proact_match: "(\<exists>v<w. proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
  using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w" 
    assume "proact \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
      assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      then obtain sv1' where 0: "validTransV (sv1, sv1')" and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2 statO" 
      unfolding move_1_def by auto
      have r1': "reachV sv1'" using r1 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain w1' w2' trv1 sv1'' trv2 sv2' statOO where 
      \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1' trv1 sv1'' sv2 trv2 sv2' statOO" 
      using less(1)[OF v \<Delta> r1' r2] by auto 
      show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv1''"]) 
      apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "sv2'"])
      using \<omega>4 0 sv1 unfolding \<omega>4_def by auto
    next 
      assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO"
      then obtain sv2'
      where 0: "validTransV (sv2,sv2')"  
      and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1 sv2' statO"  
      unfolding move_2_def by auto
      have r2': "reachV sv2'" using r2 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain w1' w2' trv1 sv1' trv2 sv2'' statOO where 
      \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2' trv2 sv2'' statOO" 
      using less(1)[OF v \<Delta> r1 r2'] by auto 
      show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
      apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "sv1'"])
      apply(rule exI[of _ "sv2 # trv2"]) apply(rule exI[of _ "sv2''"]) 
      using \<omega>4 0 sv2 unfolding \<omega>4_def by auto
    next
      assume sv1: "\<not> isSecV sv1" and  sv2: "\<not> isSecV sv2"  and 
      "move_12 \<Delta> v w1 w2 s1 s2 statA sv1 sv2 statO" and 
      sv12: "Van.eqAct sv1 sv2"
      then obtain sv1' sv2' statO'
      where statO': "statO' = sstatO' statO sv1 sv2"
      and 0: "validTransV (sv1,sv1')"  "validTransV (sv2,sv2')"  
      and \<Delta>: "\<Delta> v w1 w2 s1 s2 statA sv1' sv2' statO'"  
      unfolding move_12_def by auto
      have r1': "reachV sv1'" and r2': "reachV sv2'" using r1 r2 0 
      by (metis Van.reach.Step fst_conv snd_conv)+
      obtain w1' w2' trv1 sv1'' trv2 sv2'' statOO where 
      \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1' trv1 sv1'' sv2' trv2 sv2'' statOO" 
      using less(1)[OF v \<Delta> r1' r2'] by auto 
      show ?thesis apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
      apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv1''"]) 
      apply(rule exI[of _ "sv2 # trv2"]) apply(rule exI[of _ "sv2''"]) 
      using \<omega>4 0 sv1 sv2 sv12 unfolding \<omega>4_def statO' by (auto simp: Van.eqAct_def)
    qed
  next
    assume m: "react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" 
    have m: "match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
    have "(\<exists>w1' w2'. w1'<w1 \<and> w2'<w2 \<and> \<not> isSecO s2 \<and> \<Delta> \<infinity>  w1' w2' s1 s2' statA sv1 sv2 statO) \<or> 
          (\<exists>w1'<w1. eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> match2_1 \<Delta>  w1' \<infinity> s1 s2 s2' statA sv1 sv2 statO) \<or> 
          \<not> isSecV sv1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and> match2_12 \<Delta>  \<infinity> \<infinity> s1 s2 s2' statA sv1 sv2 statO" 
    using m v4 nis2 unfolding match2_def by auto

    thus ?thesis 
    apply(elim disjE exE) 
      subgoal for w1' w2' apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
      apply(rule exI[of _ "[]"]) apply(rule exI[of _ "sv1"]) 
      apply(rule exI[of _ "[]"]) apply(rule exI[of _ "sv2"]) 
      apply(rule exI[of _ statO]) unfolding \<omega>4_def 
      by auto
      subgoal for w1' apply(rule exI[of _ w1']) apply(rule exI[of _ \<infinity>]) 
      unfolding match2_1_def apply(elim conjE exE) subgoal for sv2'
      apply(rule exI[of _ "[]"]) apply(rule exI[of _ "sv1"])
      apply(rule exI[of _ "[sv2]"]) apply(rule exI[of _ "sv2'"])  
      apply(rule exI[of _ statO])
      unfolding \<omega>4_def using nis2(3) by (auto simp: eqSec_def) .
      subgoal  apply(rule exI[of _ \<infinity>])  apply(rule exI[of _ \<infinity>]) 
      unfolding match2_12_def apply(elim conjE exE) subgoal for sv1' sv2' 
      apply(rule exI[of _ "[sv1]"]) apply(rule exI[of _ "sv1'"]) 
      apply(rule exI[of _ "[sv2]"]) apply(rule exI[of _ "sv2'"]) 
      apply(rule exI[of _ "sstatO' statO sv1 sv2"])
      unfolding \<omega>4_def using nis2(3) apply (auto simp: eqSec_def
      sstatA'_def sstatO'_def lastt_def Van.eqAct_def) . . .
  qed
qed


(****)
(* Ready now for the final siege... *)
(*   *)

(* 
thm unwindCond_ex_\<chi>3' unwindCond_ex_\<chi>4'
thm \<chi>3'_def \<chi>4'_def
*)


definition "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' \<equiv> 
   ltr1 = lappend (llist_of (tr1 ## s1')) (s1'' $ ltr1') \<and> 
   ltr2 = lappend (llist_of (tr2 ## s2')) (s2'' $ ltr2') \<and> 
   Opt.validFromS s1 ((tr1 ## s1') ## s1'') \<and> Opt.validFromS s2 ((tr2 ## s2') ## s2'') \<and> 
   never isIntO tr1 \<and> never isIntO tr2 \<and> 
   isIntO s1' \<and> isIntO s2' \<and> getActO s1' = getActO s2' \<and> 
   Opt.lvalidFromS s1'' (s1'' $ ltr1') \<and> Opt.lcompletedFrom s1'' (s1'' $ ltr1') \<and> 
   Opt.lvalidFromS s2'' (s2'' $ ltr2') \<and> Opt.lcompletedFrom s2'' (s2'' $ ltr2') \<and>   
   Opt.lA (s1'' $ ltr1') = Opt.lA (s2'' $ ltr2')"

lemma isIntO_\<phi>\<phi>: 
assumes vltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"
and vltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"
and A: "Opt.lA ltr1 = Opt.lA ltr2" and inter3: "\<not> lnever isIntO ltr1" 
shows "\<exists>tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'. \<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
proof-
  have 03: "\<exists>s\<in>lset ltr1. isIntO s" using inter3 unfolding llist.pred_set by auto
  define ttr1 where ttr1: "ttr1 \<equiv> ltakeUntil isIntO ltr1"
  define lltr1' where lltr1': "lltr1' \<equiv> ldropUntil isIntO ltr1"
  have ltr1: "ltr1 = lappend (llist_of ttr1) lltr1'"
  unfolding ttr1 lltr1' lappend_ltakeUntil_ldropUntil[OF 03] .. 
  have 13: "ttr1 \<noteq> [] \<and> never isIntO (butlast ttr1) \<and> isIntO (last ttr1)"
  unfolding ttr1 
  using ltakeUntil_last[OF 03] ltakeUntil_not_Nil[OF 03] ltakeUntil_never_butlast[OF 03] by simp
  then obtain tr1 s1' where ttr1_eq: "ttr1 = tr1 ## s1'"
  using rev_exhaust by blast 
  hence tr1s1': "never isIntO tr1" "isIntO s1'" using 13 by auto
  have "lfinite ltr1 \<Longrightarrow> s1' \<noteq> llast ltr1" 
  by (metis Opt.final_not_isInt Opt.lcompletedFrom_def llast_last_llist_of tr1s1'(2) vltr1(2))
  hence ne: "lltr1' \<noteq> [[]]" 
  using ltr1 unfolding ttr1_eq by auto
  then obtain s1'' ltr1' where lltr1': "lltr1' = s1'' $ ltr1'"
  by (meson llist.exhaust)
  have [simp]: "filter isIntO tr1 = []"  
    by (metis never_Nil_filter tr1s1'(1))
  have clltr1': "Opt.lcompletedFrom s1 lltr1'" 
  by (metis Opt.lcompletedFrom_def lfinite_lappend lfinite_llist_of llast_lappend_LCons 
  llast_last_llist_of lltr1' ltr1 ne vltr1(2))

  have inter4: "\<not> lnever isIntO ltr2" using A inter3  
  by (metis Opt.lA.eq_LNil_iff Opt.lO Opt.lO.eq_LNil_iff lfiltermap_LNil_never 
    lfiltermap_lmap_lfilter vltr1(2) vltr2(2))
  have 04: "\<exists>s\<in>lset ltr2. isIntO s" using inter4 unfolding llist.pred_set by auto
  define ttr2 where ttr2: "ttr2 \<equiv> ltakeUntil isIntO ltr2"
  define lltr2' where lltr2': "lltr2' \<equiv> ldropUntil isIntO ltr2"
  have ltr2: "ltr2 = lappend (llist_of ttr2) lltr2'"
  unfolding ttr2 lltr2' lappend_ltakeUntil_ldropUntil[OF 04] .. 
  have 14: "ttr2 \<noteq> [] \<and> never isIntO (butlast ttr2) \<and> isIntO (last ttr2)"
  unfolding ttr2 
  using ltakeUntil_last[OF 04] ltakeUntil_not_Nil[OF 04] ltakeUntil_never_butlast[OF 04] by simp
  then obtain tr2 s2' where ttr2_eq: "ttr2 = tr2 ## s2'"
  using rev_exhaust by blast 
  hence tr2s2': "never isIntO tr2" "isIntO s2'" using 14 by auto
  have "lfinite ltr2 \<Longrightarrow> s2' \<noteq> llast ltr2" 
  by (metis Opt.final_not_isInt Opt.lcompletedFrom_def llast_last_llist_of tr2s2'(2) vltr2(2))
  hence ne: "lltr2' \<noteq> [[]]" 
  using ltr2 unfolding ttr2_eq by auto
  then obtain s2'' ltr2' where lltr2': "lltr2' = s2'' $ ltr2'"
  by (meson llist.exhaust)
  have [simp]: "filter isIntO tr2 = []"  
    by (metis never_Nil_filter tr2s2'(1))
  have clltr2': "Opt.lcompletedFrom s2 lltr2'" 
  by (metis Opt.lcompletedFrom_def lfinite_lappend lfinite_llist_of llast_lappend_LCons 
  llast_last_llist_of lltr2' ltr2 ne vltr2(2))

  have AA: "Opt.lA lltr1' = Opt.lA lltr2'"
  unfolding Opt.lA[OF clltr1'] Opt.lA[OF clltr2']
  using A[unfolded Opt.lA[OF vltr1(2)] Opt.lA[OF vltr2(2)]] tr1s1' tr2s2'
  unfolding ltr1 ltr2 ttr1_eq ttr2_eq
  unfolding lfilter_lappend_llist_of by simp

  show ?thesis apply(rule exI[of _ tr1]) apply(rule exI[of _ s1'])
  apply(rule exI[of _ s1''])  apply(rule exI[of _ ltr1']) 
  apply(rule exI[of _ tr2]) apply(rule exI[of _ s2'])
  apply(rule exI[of _ s2''])  apply(rule exI[of _ ltr2']) 
  unfolding \<phi>\<phi>_def  apply(intro conjI)
    subgoal unfolding ltr1 ttr1_eq lltr1' ..
    subgoal unfolding ltr2 ttr2_eq lltr2' ..
    subgoal using vltr1(1) unfolding ltr1 ttr1_eq lltr1'  
    by (simp add: Opt.lvalidFromS_lappend_finite lappend_llist_of_LCons)
    subgoal using vltr2(1) unfolding ltr2 ttr2_eq lltr2'  
    by (simp add: Opt.lvalidFromS_lappend_finite lappend_llist_of_LCons)
    subgoal using tr1s1' by simp
    subgoal using tr2s2' by simp
    subgoal using tr1s1' by simp
    subgoal using tr2s2' by simp
    subgoal using A[unfolded Opt.lA[OF vltr1(2)] Opt.lA[OF vltr2(2)]]
    tr1s1' tr2s2'
    unfolding ltr1 ttr1_eq ltr2 ttr2_eq lltr1' lltr2'
    unfolding lfilter_lappend_llist_of by simp
    subgoal using vltr1(1) unfolding ltr1 ttr1_eq lltr1'  
    using Opt.lvalidFromS_lappend_LCons by blast
    subgoal using vltr1(2) unfolding ltr1 ttr1_eq lltr1' 
    by (metis Opt.lcompletedFrom_def lfinite_lappend lfinite_llist_of 
    llast_lappend_LCons llast_last_llist_of llist.distinct(1)) 
    subgoal using vltr2(1) unfolding ltr2 ttr2_eq lltr2'  
    using Opt.lvalidFromS_lappend_LCons by blast
    subgoal using vltr2(2) unfolding ltr2 ttr2_eq lltr2' 
    by (metis Opt.lcompletedFrom_def lfinite_lappend lfinite_llist_of 
    llast_lappend_LCons llast_last_llist_of llist.distinct(1)) 
    subgoal using AA unfolding lltr1' lltr2' . .     
qed

definition "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1' \<equiv> 
   ltr1 = lappend (llist_of (tr1 ## s1')) (s1'' $ ltr1') \<and>  
   Opt.validFromS s1 ((tr1 ## s1') ## s1'') \<and> 
   never isIntO tr1 \<and> \<not> isIntO s1' \<and> \<not> isIntO s1'' \<and> 
   never isSecO tr1 \<and> isSecO s1' \<and> 
   Opt.lvalidFromS s1'' (s1'' $ ltr1') \<and> Opt.lcompletedFrom s1'' (s1'' $ ltr1')"

lemma isSecO_\<chi>\<chi>: 
assumes vltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"
and inter: "lnever isIntO ltr1" and isec: "\<not> lnever isSecO ltr1"  
shows "\<exists>tr1 s1' s1'' ltr1'. \<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'"
proof-
  have 0: "\<exists>s\<in>lset ltr1. isSecO s" using isec unfolding llist.pred_set by auto
  define ttr1 where ttr1: "ttr1 \<equiv> ltakeUntil isSecO ltr1"
  define lltr1' where lltr1': "lltr1' \<equiv> ldropUntil isSecO ltr1"
  have ltr1: "ltr1 = lappend (llist_of ttr1) lltr1'"
  unfolding ttr1 lltr1' lappend_ltakeUntil_ldropUntil[OF 0] .. 
  have 1: "ttr1 \<noteq> [] \<and> never isSecO (butlast ttr1) \<and> isSecO (last ttr1)"
  unfolding ttr1 
  using ltakeUntil_last[OF 0] ltakeUntil_not_Nil[OF 0] ltakeUntil_never_butlast[OF 0] by simp
  then obtain tr1 s1' where ttr1_eq: "ttr1 = tr1 ## s1'"
  using rev_exhaust by blast 
  hence tr1s1': "never isSecO tr1" "isSecO s1'" using 1 by auto
  have 2: "never isIntO tr1 \<and> \<not> isIntO s1' \<and> lnever isIntO lltr1'" 
  using inter unfolding ltr1 ttr1_eq 
  unfolding llist_all_lappend_llist_of list_all_append by simp
  have "lfinite ltr1 \<Longrightarrow> s1' \<noteq> llast ltr1"
  by (metis Opt.final_not_isSec Opt.lcompletedFrom_def llast_last_llist_of tr1s1'(2) vltr1(2))
  hence ne: "lltr1' \<noteq> [[]]" 
  using ltr1 unfolding ttr1_eq by auto
  then obtain s1'' ltr1' where lltr1': "lltr1' = s1'' $ ltr1'"
  by (meson llist.exhaust)
  show ?thesis apply(rule exI[of _ tr1]) apply(rule exI[of _ s1'])
  apply(rule exI[of _ s1''])  apply(rule exI[of _ ltr1']) 
  unfolding \<chi>\<chi>_def apply(intro conjI)
    subgoal unfolding ltr1 ttr1_eq lltr1' ..
    subgoal using vltr1(1) unfolding ltr1 ttr1_eq lltr1'  
    by (simp add: Opt.lvalidFromS_lappend_finite lappend_llist_of_LCons)
    subgoal using 2 by simp
    subgoal using 2 by simp
    subgoal using 2 unfolding lltr1' by simp
    subgoal using tr1s1' by simp
    subgoal using tr1s1' by simp
    subgoal using vltr1(1) unfolding ltr1 ttr1_eq lltr1'  
    using Opt.lvalidFromS_lappend_LCons by blast
    subgoal using vltr1(2) unfolding ltr1 ttr1_eq lltr1'  
    by (metis Opt.lcompletedFrom_def ne lfinite_lappend 
      lfinite_llist_of llast_lappend_LCons llast_last_llist_of lltr1') . 
qed
  

(* *)

type_synonym ('stA,'stO) tuple34 =  
 "enat \<times> enat \<times>
  'stA \<times> 'stA llist \<times>  
  'stA \<times> 'stA llist \<times> 
  status \<times> 
  'stO \<times> 'stO \<times> status"

type_synonym ('stA,'stO) tuple12 =  
 "'stO list \<times> 'stO \<times> 'stO list \<times> 'stO \<times> status \<times> status"


context 
fixes \<Delta> :: "enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'stateO \<Rightarrow> 'stateO \<Rightarrow> status \<Rightarrow> 'stateV \<Rightarrow> 'stateV \<Rightarrow> status \<Rightarrow> bool" 
begin

(*
thm unwindCond_ex_\<chi>3'[no_vars]
thm \<chi>3'_def
term \<chi>3'
thm isSecO_\<chi>\<chi>
*)

fun isn :: "turn \<times> ('stateO,'stateV) tuple34 \<Rightarrow> bool"
where 
"isn (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<longleftrightarrow> ltr1 = [[]] \<and> ltr2 = [[]]"

fun h_t :: 
"turn \<times> ('stateO,'stateV)tuple34 \<Rightarrow> 
 ('stateO,'stateV)tuple12 \<times> 
 turn \<times> ('stateO,'stateV)tuple34"
where 
"h_t (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
 (if trn = L 
  then if lnever isSecO ltr1 
  then let (s1',ltr1') = (lhd (ltl ltr1), ltl ltr1)
  in let (w1',w2',trv1,sv1',trv2,sv2',statOO) = 
     (SOME k. case k of (w1',w2',trv1,sv1',trv2,sv2',statOO) \<Rightarrow> 
         \<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO)
  in ((trv1,sv1',trv2,sv2',statA,statOO),
      (if trv1 = [] then L else R,
       w1',w2',s1',ltr1',s2,ltr2,statA,sv1',sv2',statOO))
  else 
  let (tr1,s1',s1'',ltr1') = 
      (SOME k. case k of (tr1,s1',s1'',ltr1') \<Rightarrow> 
         \<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1')
  in let (w1',w2',trv1,sv1'',trv2,sv2'',statOO) = 
           (SOME k'. case k' of (w1',w2',trv1,sv1'',trv2,sv2'',statOO) \<Rightarrow> 
            \<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO)
  in ((trv1,sv1'',trv2,sv2'',statA,statOO),
      (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))
  \<comment> \<open>   \<close>
  else if lnever isSecO ltr2  
  then let (s2',ltr2') = (lhd (ltl ltr2), ltl ltr2)
  in let (w1',w2',trv1,sv1',trv2,sv2',statOO) = 
     (SOME k. case k of (w1',w2',trv1,sv1',trv2,sv2',statOO) \<Rightarrow> 
         \<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO)
  in ((trv1,sv1',trv2,sv2',statA,statOO),
      (if trv2 = [] then R else L,
       w1',w2',s1,ltr1,s2',ltr2',statA,sv1',sv2',statOO))
  else 
  let (tr2,s2',s2'',ltr2') = 
      (SOME k. case k of (tr2,s2',s2'',ltr2') \<Rightarrow> 
         \<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2')
  in let (w1',w2',trv1,sv1'',trv2,sv2'',statOO) = 
           (SOME k'. case k' of (w1',w2',trv1,sv1'',trv2,sv2'',statOO) \<Rightarrow> 
            \<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO)
  in ((trv1,sv1'',trv2,sv2'',statA,statOO),
      (L,w1',w2',s1, ltr1, s2'',s2'' $ ltr2',statA,sv1'',sv2'',statOO))
)"

declare h_t.simps[simp del]

definition "h \<equiv> fst o h_t" 
definition "t \<equiv> snd o h_t" 

fun econd where "econd (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    (llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0)"

fun e where "e (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[([sv1],sv1,[sv2],sv2,statA,statO)]]"

definition f :: "turn \<times> ('stateO,'stateV)tuple34 \<Rightarrow> ('stateO,'stateV)tuple12 llist"
where "f \<equiv> ccorec_llist isn h econd e t" 

(* *)

lemma f_LNil: 
"ltr1 = [[]] \<Longrightarrow> ltr2 = [[]] \<Longrightarrow> f (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[]]"
unfolding f_def apply(subst llist_ccorec(1)) by auto

lemma f_length_1: 
assumes "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0"
shows "f (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[([sv1],sv1,[sv2],sv2,statA,statO)]]" 
using assms unfolding f_def apply(subst llist_ccorec(2))  
  subgoal unfolding e.simps lnull_def by auto
  subgoal by auto
  subgoal unfolding econd.simps by simp .

lemma f_length_ge1: 
assumes "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
shows "f (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)  = 
   LCons (h (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)) (f (t (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) ))" 
proof-
  show ?thesis using assms unfolding f_def apply(subst llist_ccorec(2))   
  subgoal unfolding e.simps lnull_def by auto
  subgoal by auto
  subgoal unfolding econd.simps by auto .
qed

(* *)

definition lltrv1 :: "turn \<times> ('stateO,'stateV)tuple34 \<Rightarrow> 'stateV llist" where 
"lltrv1 trn_tp = lconcat (lmap (\<lambda>(trv1,sv1'',trv2,sv2'',statAA,statOO). llist_of trv1) (f trn_tp))"

definition then1 :: "turn \<times> ('stateO,'stateV)tuple34 \<Rightarrow> nat" where 
"then1 trn_tp = firstNC (lmap (\<lambda>(trv1,sv1'',trv2,sv2'',statAA,statOO). trv1) (f trn_tp))"

definition lltrv2 :: "turn \<times> ('stateO,'stateV)tuple34 \<Rightarrow> 'stateV llist" where 
"lltrv2 trn_tp = lconcat (lmap (\<lambda>(trv1,sv1'',trv2,sv2'',statAA,statOO). llist_of trv2) (f trn_tp))"

definition then2 :: "turn \<times> ('stateO,'stateV)tuple34 \<Rightarrow> nat" where 
"then2 trn_tp = firstNC (lmap (\<lambda>(trv1,sv1'',trv2,sv2'',statAA,statOO). trv2) (f trn_tp))"

(* *)  
lemma lltrv1_ne_imp: 
assumes "lltrv1 trn_tp \<noteq> [[]]"
shows "\<exists>trv1 sv1'' trv2 sv2'' statAA statOO. (trv1,sv1'',trv2,sv2'',statAA,statOO) \<in> lset (f trn_tp) \<and> 
              trv1 \<noteq> []"
using assms unfolding lltrv1_def unfolding lconcat_eq_LNil_iff by force
 
lemma lltrv2_ne_imp: 
assumes "lltrv2 trn_tp \<noteq> [[]]"
shows "\<exists>trv1 sv1'' trv2 sv2'' statAA statOO. (trv1,sv1'',trv2,sv2'',statAA,statOO) \<in> lset (f trn_tp) \<and> 
              trv2 \<noteq> []"
using assms unfolding lltrv2_def unfolding lconcat_eq_LNil_iff by force


(* *)

lemma lltrv1_LNil[simp]: 
"ltr1 = [[]] \<Longrightarrow> ltr2 = [[]] \<Longrightarrow> lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[]]"
unfolding lltrv1_def f_LNil by simp 
lemma lltrv2_LNil[simp]: 
"ltr1 = [[]] \<Longrightarrow> ltr2 = [[]] \<Longrightarrow> lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[]]"
unfolding lltrv2_def f_LNil by simp 

(* *)

lemma lltrv1_lnever[simp]: 
assumes "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0"  
shows "lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[sv1]]" 
unfolding lltrv1_def using f_length_1[OF assms] by auto

lemma lltrv2_lnever[simp]: 
assumes "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0" 
shows "lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[sv2]]" 
unfolding lltrv2_def using f_length_1[OF assms] by auto

(* *)

(* 
thm unwindCond_ex_\<chi>3'[no_vars]
thm \<chi>3'_def
term \<chi>3'
thm isSecO_\<chi>\<chi>[no_vars]
*)

lemma h_t_lnever_L:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"
and l': "lnever isIntO ltr1" "\<not> isIntO s2" 
and len: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
and l: "trn = L"  "lnever isSecO ltr1" 
shows "\<exists> w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO. 
  ltr1 = s1 $ ltr1' \<and> validTransO (s1,s1') \<and> 
  Opt.lvalidFromS s1' ltr1' \<and> Opt.lcompletedFrom s1' ltr1' \<and> lnever isIntO ltr1' \<and> 
  \<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO \<and> 
  h_t (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
  ((trv1,sv1',trv2,sv2',statA,statOO),
   (if trv1 = [] then L else R, 
    w1',w2', s1', ltr1',s2,ltr2,statA,sv1',sv2',statOO))"
proof-
  have s1: "\<not> isIntO s1" using l' ltr1 
  by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil lhd_LCons 
  llist.exhaust llist.pred_inject(2))

  obtain ltr1' where ltr13: "ltr1 = s1 $ ltr1'"   
  by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel ltr1(1) ltr1(2))   
  hence ltr1': "ltr1' = ltl ltr1" by auto
  have ltr1'ne: "ltr1' \<noteq> [[]]" using len(1) unfolding ltr13 
    by (metis One_nat_def llength_LCons llength_LNil one_eSuc one_enat_def order_less_irrefl)
  define s1' where s1': "s1' = lhd (ltl ltr1)" 
  have v3: "validTransO (s1,s1')" and vv3: "Opt.lvalidFromS s1' ltr1'" "Opt.lcompletedFrom s1' ltr1'"
  using ltr1 ltr1'ne unfolding ltr13 s1' 
  by (metis Opt.lcompletedFrom_LCons Opt.lcompletedFrom_def Opt.lvalidFromS_Cons_iff ltr1' ltr13)+

  have is1': "\<not> isIntO s1'" and "lnever isIntO ltr1'" 
  using l'(1) unfolding ltr13 
  by (metis llist.exhaust_sel llist.pred_inject(2) ltr1' ltr1'ne s1')+

  have iss1: "\<not> isSecO s1"  
    using l(2) ltr13 by auto
  
  obtain w1' w2' trv1 sv1' trv2 sv2' statOO
  where \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 (lhd (ltl ltr1)) s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"   
  using unwindCond_ex_\<omega>3[OF unw \<Delta> r v3 s1 is1' iss1 l'(2)] s1' by auto

  (* *)

  define tp' where 
  "tp' = (SOME k'. case k' of (w1',w2',trv1,sv1',trv2,sv2',statOO) \<Rightarrow> 
          \<omega>3 \<Delta> w1 w2 w1' w2' s1 (lhd (ltl ltr1)) s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO)"
  
  have 1: "case tp' of (w1',w2',trv1,sv1',trv2,sv2',statOO) \<Rightarrow> 
         \<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
  using \<omega>3 unfolding tp'_def s1' apply- apply(rule someI_ex)
  apply(rule exI[of _ "(w1',w2',trv1,sv1',trv2,sv2',statOO)"]) by auto

  obtain w1' w2' trv1 sv1' trv2 sv2' statOO where 
  tp': "tp' = (w1',w2',trv1,sv1',trv2,sv2',statOO)" by(cases tp', auto)

  have \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"  
  using 1 unfolding tp' by auto

  show ?thesis
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
  apply(rule exI[of _ s1']) apply(rule exI[of _ ltr1']) 
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1']) 
  apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2'])
  apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal by fact
    subgoal by fact
    subgoal by fact
    subgoal by fact
    subgoal by fact
    subgoal by fact
    subgoal using len l unfolding h_t.simps apply simp 
    unfolding tp'_def[symmetric] tp' s1' ltr1' by simp .
qed

lemma lltrv1_lltrv2_lnever_L:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"
and l': "lnever isIntO ltr1" "\<not> isIntO s2" 
and len: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
and l: "trn = L"  "lnever isSecO ltr1" 
shows "\<exists> w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO. 
  ltr1 = s1 $ ltr1' \<and> validTransO (s1,s1') \<and> 
  Opt.lvalidFromS s1' ltr1' \<and> Opt.lcompletedFrom s1' ltr1' \<and> lnever isIntO ltr1' \<and> 
  \<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO \<and> 
  lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv1) (lltrv1 (if trv1 = [] then L else R,
                                   w1',w2',s1',ltr1',s2,ltr2,statA,sv1',sv2',statOO)) \<and> 
  lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv2) (lltrv2 (if trv1 = [] then L else R,
                                   w1',w2',s1',ltr1',s2,ltr2,statA,sv1',sv2',statOO))"
proof- 
  show ?thesis
  using h_t_lnever_L[OF assms] apply(elim exE)
  subgoal for w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ s1']) apply(rule exI[of _ ltr1']) 
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1']) 
  apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2'])
  apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal by simp
    subgoal by simp 
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal unfolding lltrv1_def apply(subst f_length_ge1[OF len])
    unfolding h_def t_def by auto
    subgoal unfolding lltrv2_def apply(subst f_length_ge1[OF len])
    unfolding h_def t_def by auto . . 
qed

(* *)

lemma h_t_not_lnever_L:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"
and l': "lnever isIntO ltr1" "\<not> isIntO s2" 
and len: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
and l: "trn = L"  "\<not> lnever isSecO ltr1" 
shows "\<exists> w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO. 
  \<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1' \<and> 
  \<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO \<and> 
  h_t (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
  ((trv1,sv1'',trv2,sv2'',statA,statOO),
   (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))"
proof-
  have s1: "\<not> isIntO s1" using l' ltr1  
  by (metis Opt.lvalidFromS_def l(2) lhd_LCons llist.exhaust llist.pred_inject(1) llist.pred_inject(2)) 

  obtain tr1 s1' s1'' ltr1'
  where \<chi>\<chi>: "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'"
  using isSecO_\<chi>\<chi>[OF ltr1 l'(1) l(2)] by auto  

  define tp where 
  "tp = (SOME k. case k of (tr1,s1',s1'',ltr1') \<Rightarrow> 
           \<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1')"

  have 0: "case tp of (tr1,s1',s1'',ltr1') \<Rightarrow> 
         \<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'"
  using \<chi>\<chi> unfolding tp_def apply- apply(rule someI_ex)
  apply(rule exI[of _ "(tr1,s1',s1'',ltr1')"]) by auto

  obtain tr1 s1' s1'' ltr1' where 
  tp: "tp = (tr1,s1',s1'',ltr1')" by(cases tp, auto)

  have \<chi>\<chi>: "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'"
  using 0 unfolding tp by auto

  obtain w1' w2' trv1 sv1'' trv2 sv2'' statOO
  where \<chi>3': "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"   
  using unwindCond_ex_\<chi>3'[OF unw \<Delta> r, of tr1 s1' s1'']
  using \<chi>\<chi> l' s1 unfolding \<chi>\<chi>_def by auto

  (* *)

  define tp' where 
  "tp' = (SOME k'. case k' of (w1',w2',trv1,sv1'',trv2,sv2'',statOO) \<Rightarrow> 
          \<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO)"
  
  have 1: "case tp' of (w1',w2',trv1,sv1'',trv2,sv2'',statOO) \<Rightarrow> 
         \<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
  using \<chi>3' unfolding tp'_def apply- apply(rule someI_ex)
  apply(rule exI[of _ "(w1',w2',trv1,sv1'',trv2,sv2'',statOO)"]) by auto

  obtain w1' w2' trv1 sv1'' trv2 sv2'' statOO where 
  tp': "tp' = (w1',w2',trv1,sv1'',trv2,sv2'',statOO)" by(cases tp', auto)

  have \<chi>3': "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"  
  using 1 unfolding tp' by auto

  show ?thesis 
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ tr1]) apply(rule exI[of _ s1']) apply(rule exI[of _ s1'']) apply(rule exI[of _ ltr1']) 
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2''])
  apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal using \<chi>\<chi> .
    subgoal using \<chi>3' .
    subgoal using l unfolding h_t.simps 
    unfolding tp_def[symmetric] tp apply simp
    unfolding tp'_def[symmetric] tp' by simp .
qed

lemma lltrv1_lltrv2_not_lnever_L:  
assumes unw: "unwindCond \<Delta>" 
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"
and l': "lnever isIntO ltr1" "\<not> isIntO s2"
and len: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
and l: "trn = L"  "\<not> lnever isSecO ltr1"  
shows "\<exists> w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO. 
  \<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1' \<and> 
  \<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO \<and> 
  lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv1) (lltrv1 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)) \<and> 
  lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv2) (lltrv2 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)) "
proof- 
  show ?thesis
  using h_t_not_lnever_L[OF assms] apply(elim exE)
  subgoal for w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ tr1]) apply(rule exI[of _ s1']) apply(rule exI[of _ s1'']) apply(rule exI[of _ ltr1']) 
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2''])
  apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal by simp
    subgoal by simp 
    subgoal unfolding lltrv1_def apply(subst f_length_ge1[OF len])
    unfolding h_def t_def by simp
    subgoal unfolding lltrv2_def apply(subst f_length_ge1[OF len])
    unfolding h_def t_def by simp . . 
qed

(* *)

lemma h_t_lnever_R:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"
and l': "\<not> isIntO s1" "lnever isIntO ltr2" 
and len: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
and l: "trn = R"  "lnever isSecO ltr2" 
shows "\<exists> w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO. 
  ltr2 = s2 $ ltr2' \<and> validTransO (s2,s2') \<and> 
  Opt.lvalidFromS s2' ltr2' \<and> Opt.lcompletedFrom s2' ltr2' \<and> lnever isIntO ltr2' \<and> 
  \<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO \<and> 
  h_t (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
  ((trv1,sv1',trv2,sv2',statA,statOO),
   (if trv2 = [] then R else L,
    w1',w2',s1,ltr1,s2',ltr2',statA,sv1',sv2',statOO))"
proof-
  have s2: "\<not> isIntO s2" using l' ltr2 
  by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil lhd_LCons 
  llist.exhaust llist.pred_inject(2))

  obtain ltr2' where ltr24: "ltr2 = s2 $ ltr2'"   
  by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel ltr2(1) ltr2(2))   
  hence ltr2': "ltr2' = ltl ltr2" by auto
  have ltr2'ne: "ltr2' \<noteq> [[]]" using len(2) unfolding ltr24 
    by (metis One_nat_def llength_LCons llength_LNil one_eSuc one_enat_def order_less_irrefl)
  define s2' where s2': "s2' = lhd (ltl ltr2)" 
  have v4: "validTransO (s2,s2')" and vv4: "Opt.lvalidFromS s2' ltr2'" "Opt.lcompletedFrom s2' ltr2'"
  using ltr2 ltr2'ne unfolding ltr24 s2' 
  by (metis Opt.lcompletedFrom_LCons Opt.lcompletedFrom_def Opt.lvalidFromS_Cons_iff ltr2' ltr24)+

  have is2': "\<not> isIntO s2'" and "lnever isIntO ltr2'" 
  using l'(2) unfolding ltr24 
  by (metis llist.exhaust_sel llist.pred_inject(2) ltr2' ltr2'ne s2')+

  have iss2: "\<not> isSecO s2"  
    using l(2) ltr24 by auto
  
  obtain w1' w2' trv1 sv1' trv2 sv2' statOO
  where \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 (lhd (ltl ltr2)) statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"   
  using unwindCond_ex_\<omega>4[OF unw \<Delta> r l'(1) v4 s2 is2' iss2 ] s2' by auto

  (* *)

  define tp' where 
  "tp' = (SOME k'. case k' of (w1',w2',trv1,sv1',trv2,sv2',statOO) \<Rightarrow> 
          \<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 (lhd (ltl ltr2)) statA sv1 trv1 sv1' sv2 trv2 sv2' statOO)"
  
  have 1: "case tp' of (w1',w2',trv1,sv1',trv2,sv2',statOO) \<Rightarrow> 
         \<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
  using \<omega>4 unfolding tp'_def s2' apply- apply(rule someI_ex)
  apply(rule exI[of _ "(w1',w2',trv1,sv1',trv2,sv2',statOO)"]) by auto

  obtain w1' w2' trv1 sv1' trv2 sv2' statOO where 
  tp': "tp' = (w1',w2',trv1,sv1',trv2,sv2',statOO)" by(cases tp', auto)

  have \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"  
  using 1 unfolding tp' by auto

  show ?thesis 
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ s2']) apply(rule exI[of _ ltr2']) 
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1']) 
  apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2'])
  apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal by fact
    subgoal by fact
    subgoal by fact
    subgoal by fact
    subgoal by fact
    subgoal by fact
    subgoal using len l unfolding h_t.simps apply simp 
    unfolding tp'_def[symmetric] tp' s2' ltr2' by simp .
qed

lemma lltrv1_lltrv2_lnever_R:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"
and l': "\<not> isIntO s1" "lnever isIntO ltr2" 
and len: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
and l: "trn = R"  "lnever isSecO ltr2" 
shows "\<exists> w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO. 
  ltr2 = s2 $ ltr2' \<and> validTransO (s2,s2') \<and> 
  Opt.lvalidFromS s2' ltr2' \<and> Opt.lcompletedFrom s2' ltr2' \<and> lnever isIntO ltr2' \<and> 
  \<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO \<and> 
  lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv1) (lltrv1 (if trv2 = [] then R else L,
                                   w1',w2',s1,ltr1,s2',ltr2',statA,sv1',sv2',statOO)) \<and> 
  lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv2) (lltrv2 (if trv2 = [] then R else L,
                                   w1',w2',s1,ltr1,s2',ltr2',statA,sv1',sv2',statOO))"
proof- 
  show ?thesis
  using h_t_lnever_R[OF assms] apply(elim exE)
  subgoal for w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ s2']) apply(rule exI[of _ ltr2']) 
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1']) 
  apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2'])
  apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal by simp
    subgoal by simp 
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal unfolding lltrv1_def apply(subst f_length_ge1[OF len])
    unfolding h_def t_def by auto
    subgoal unfolding lltrv2_def apply(subst f_length_ge1[OF len])
    unfolding h_def t_def by auto . . 
qed

(* *)

lemma h_t_not_lnever_R:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"
and l': "\<not> isIntO s1" "lnever isIntO ltr2" 
and len: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
and l: "trn = R"  "\<not> lnever isSecO ltr2"  
shows "\<exists> w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO. 
  \<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2' \<and> 
  \<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO \<and> 
  h_t (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
  ((trv1,sv1'',trv2,sv2'',statA,statOO),
   (L,w1',w2',s1,ltr1,s2'',s2'' $ ltr2',statA,sv1'',sv2'',statOO))"
proof-
  have s2: "\<not> isIntO s2" using l' ltr2   
  by (metis Simple_Transition_System.lvalidFromS_def l(2) lhd_LCons llist.pred_inject(1) 
   llist.pred_inject(2) neq_LNil_conv)

  obtain tr2 s2' s2'' ltr2'
  where \<chi>\<chi>: "\<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'"
  using isSecO_\<chi>\<chi>[OF ltr2 l'(2) l(2)] by auto  

  define tp where 
  "tp = (SOME k. case k of (tr2,s2',s2'',ltr2') \<Rightarrow> 
           \<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2')"

  have 0: "case tp of (tr2,s2',s2'',ltr2') \<Rightarrow> 
         \<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'"
  using \<chi>\<chi> unfolding tp_def apply- apply(rule someI_ex)
  apply(rule exI[of _ "(tr2,s2',s2'',ltr2')"]) by auto

  obtain tr2 s2' s2'' ltr2' where 
  tp: "tp = (tr2,s2',s2'',ltr2')" by(cases tp, auto)

  have \<chi>\<chi>: "\<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'"
  using 0 unfolding tp by auto

  obtain w1' w2' trv1 sv1'' trv2 sv2'' statOO
  where \<chi>4': "\<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"   
  using unwindCond_ex_\<chi>4'[OF unw \<Delta> r, of tr2 s2' s2'']
  using \<chi>\<chi> l' s2 unfolding \<chi>\<chi>_def by auto

  (* *)

  define tp' where 
  "tp' = (SOME k'. case k' of (w1',w2',trv1,sv1'',trv2,sv2'',statOO) \<Rightarrow> 
          \<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO)"
  
  have 1: "case tp' of (w1',w2',trv1,sv1'',trv2,sv2'',statOO) \<Rightarrow> 
         \<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
  using \<chi>4' unfolding tp'_def apply- apply(rule someI_ex)
  apply(rule exI[of _ "(w1',w2',trv1,sv1'',trv2,sv2'',statOO)"]) by auto

  obtain w1' w2' trv1 sv1'' trv2 sv2'' statOO where 
  tp': "tp' = (w1',w2',trv1,sv1'',trv2,sv2'',statOO)" by(cases tp', auto)

  have \<chi>4': "\<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"  
  using 1 unfolding tp' by auto

  show ?thesis 
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ tr2]) apply(rule exI[of _ s2']) apply(rule exI[of _ s2'']) apply(rule exI[of _ ltr2']) 
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2''])
  apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal using \<chi>\<chi> .
    subgoal using \<chi>4' .
    subgoal using l unfolding h_t.simps 
    unfolding tp_def[symmetric] tp apply simp
    unfolding tp'_def[symmetric] tp' by auto .
qed

lemma lltrv1_lltrv2_not_lnever_R:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"
and l': "\<not> isIntO s1" "lnever isIntO ltr2" 
and len: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
and l: "trn = R"  "\<not> lnever isSecO ltr2"  
shows "\<exists> w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO. 
  \<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2' \<and> 
  \<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO \<and> 
  lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv1) (lltrv1 (L,w1',w2',s1,ltr1,s2'',s2'' $ ltr2',statA,sv1'',sv2'',statOO)) \<and> 
  lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv2) (lltrv2 (L,w1',w2',s1,ltr1,s2'',s2'' $ ltr2',statA,sv1'',sv2'',statOO))"
proof- 
  show ?thesis
  using h_t_not_lnever_R[OF assms] apply(elim exE)
  subgoal for w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ tr2]) apply(rule exI[of _ s2']) apply(rule exI[of _ s2'']) apply(rule exI[of _ ltr2']) 
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2''])
  apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal by simp
    subgoal by simp 
    subgoal unfolding lltrv1_def apply(subst f_length_ge1[OF len])
    unfolding h_def t_def by simp
    subgoal unfolding lltrv2_def apply(subst f_length_ge1[OF len])
    unfolding h_def t_def by simp . .
qed

lemma f_not_LNil: "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]] \<Longrightarrow> 
f (w1,w2,trn, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO) \<noteq> [[]]"
apply(cases "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0")
  subgoal apply(subst f_length_1) by auto
  subgoal apply(subst f_length_ge1) by auto .


(* *)

lemma lvalidFromS_lltrv1:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
shows "Van.lvalidFromS sv1 (lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  {fix n sv1 ltrv1
   assume "\<exists>trn w1 w2 s1 ltr1 s2 ltr2 statA sv2 statO. 
       n = w1 \<and>   
       ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2"
   hence "Van.llvalidFromS n sv1 ltrv1" 
   proof(coinduct rule: Van.llvalidFromS.coinduct[of "\<lambda>n sv1 ltrv1. 
     \<exists>trn w1 w2 s1 ltr1 s2 ltr2 statA sv2 statO. 
       n = w1 \<and> 
       ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2"])
     case (llvalidFromS n sv1 ltrv1) 
     then obtain trn w1 w2 s1 ltr1 s2 ltr2 statA sv2 statO  
     where n: "n = w1" and 
     ltrv1: "ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
     by auto
     have isi3: "\<not> isIntO s1" using ltr1
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))  
     have isi4: "\<not> isIntO s2" using ltr2
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))
  
     show ?case proof(cases "ltr1 = [[]] \<and> ltr2 = [[]]")
       case True note ltr14 = True
       hence ltrv1: "ltrv1 = [[]]" unfolding ltrv1 by simp
       show ?thesis unfolding ltrv1 apply(rule Van.llvalidFromS_selectLNil) by auto
     next
       case False hence ltr14: "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" by auto
       show ?thesis proof(cases "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0")
         case True note ltr14 = ltr14 True
         hence ltrv1: "ltrv1 = [[sv1]]" unfolding ltrv1 by simp
         show ?thesis unfolding ltrv1 apply(rule Van.llvalidFromS_selectSingl) by auto
       next
         case False hence current: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
         by auto 
         show ?thesis proof(cases trn)
           case L note trn = L note current = current L
           show ?thesis
           proof(cases "lnever isSecO ltr1") 
             case True note current = current True
             obtain trn' w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr1 = s1 $ ltr1'" "validTransO (s1, s1')" "Opt.lvalidFromS s1' ltr1'"
             "lcompletedFromO s1' ltr1'" "lnever isIntO ltr1'" and 
             \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv1 = [] then L else R)"
             and ltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv1 by blast
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO)"
             have ltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' ..
             
             show ?thesis 
             proof(cases "trv1 = []")
               case True note trv1 = True
               have sv1': "sv1' = sv1" 
               using \<omega>3 unfolding \<omega>3_def by (simp add: trv1)
               show ?thesis 
               apply(rule Van.llvalidFromS_selectDelay)
               apply(rule exI[of _ "w1'"]) apply(rule exI[of _ n]) 
               apply(rule exI[of _ sv1]) apply(rule exI[of _ "ltrv1'"])  
               apply(intro conjI)
               subgoal .. subgoal ..      
               subgoal unfolding ltrv1 trv1 by simp
               subgoal using \<omega>3 unfolding \<omega>3_def trv1 n by simp
               subgoal apply(rule disjI1) 
                 apply(rule exI[of _ trn'])
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1']) apply(rule exI[of _ "ltr1'"])
                 apply(rule exI[of _ s2]) apply(rule exI[of _ ltr2])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv2']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..  
                   subgoal unfolding ltrv1' trn' trv1 sv1' using trn by simp
                   subgoal using \<omega>3 unfolding \<omega>3_def sv1' by simp
                   subgoal using \<omega>3 unfolding \<omega>3_def  
                   by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv) 
                   subgoal by fact  subgoal by fact
                   subgoal using \<omega>3 unfolding \<omega>3_def   
                   by (metis Nil_is_append_conv Van.reach_validFromS_reach last_snoc not_Cons_self2 r(4))
                   subgoal using \<omega>\<omega> by simp subgoal using \<omega>\<omega> by simp subgoal using \<omega>\<omega> by simp                    
                   subgoal by fact subgoal by fact subgoal by fact . .
             next
               case False note trv1 = False
               show ?thesis 
               apply(rule Van.llvalidFromS_selectlappend)
               apply(rule exI[of _ sv1]) apply(rule exI[of _ "trv1"])
               apply(rule exI[of _ sv1']) apply(rule exI[of _ "w1'"])  
               apply(rule exI[of _ "ltrv1'"]) apply(rule exI[of _ n]) 
               apply(intro conjI)
                 subgoal .. subgoal ..  
                 subgoal using ltrv1 .
                 subgoal using \<omega>3 unfolding \<omega>3_def  
                 by (metis Nil_is_append_conv Van.validFromS_def Van.validS_append1 hd_append2)
                 subgoal by fact
                 subgoal using \<omega>3 unfolding \<omega>3_def   
                 by (metis Van.validFromS_def Van.validS_validTrans list.sel(1) not_Cons_self2 snoc_eq_iff_butlast trv1)        
                 subgoal apply(rule disjI1) 
                 apply(rule exI[of _ trn']) 
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ s1']) apply(rule exI[of _ "ltr1'"])
                 apply(rule exI[of _ s2]) apply(rule exI[of _ ltr2])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv2']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..   
                   subgoal using trv1 unfolding ltrv1' trn' by auto
                   subgoal using \<omega>3 unfolding \<omega>3_def by simp
                   subgoal using \<omega>3 unfolding \<omega>3_def  
                   by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv) 
                   subgoal by fact
                   subgoal using \<omega>3 unfolding \<omega>3_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                   subgoal using \<omega>3 unfolding \<omega>3_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> 
                   using llist_all_lappend_llist_of ltr1(3) by blast
                   subgoal using \<omega>\<omega> using ltr2(1) by fastforce
                   subgoal by fact
                   subgoal by fact . . 
             qed
           next
             case False note current = current False 
             obtain w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'" and 
             \<chi>3': "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
             and ltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))" 
             using lltrv1_lltrv2_not_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv1 by blast
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)"
             have ltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' .. 
         
             show ?thesis apply(rule Van.llvalidFromS_selectlappend)
             apply(rule exI[of _ sv1]) apply(rule exI[of _ "trv1"])
             apply(rule exI[of _ sv1'']) apply(rule exI[of _ "w1'"])  
             apply(rule exI[of _ "ltrv1'"]) apply(rule exI[of _ "w1"]) 
             apply(intro conjI)
               subgoal unfolding n .. subgoal ..  
               subgoal using ltrv1 .
               subgoal using \<chi>3' unfolding \<chi>3'_def  
               by (metis Nil_is_append_conv Van.validFromS_def Van.validS_append1 hd_append2)
               subgoal using \<chi>3' unfolding \<chi>3'_def by simp
               subgoal using \<chi>3' unfolding \<chi>3'_def  
               by (metis Van.validFromS Van.validS_validTrans Simple_Transition_System.validFromS_def 
               append_is_Nil_conv not_Cons_self2)
               subgoal apply(rule disjI1) 
               apply(rule exI[of _ R]) 
               apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
               apply(rule exI[of _ s1'']) apply(rule exI[of _ "s1'' $ ltr1'"])
               apply(rule exI[of _ s2]) apply(rule exI[of _ ltr2])
               apply(rule exI[of _ statA]) apply(rule exI[of _ sv2'']) apply(rule exI[of _ statOO])
               apply(intro conjI) 
                 subgoal ..   
                 subgoal unfolding ltrv1' ..
                 subgoal using \<chi>3' unfolding \<chi>3'_def by simp
                 subgoal using \<chi>3' unfolding \<chi>3'_def  
                 by (metis Simple_Transition_System.reach_validFromS_reach \<chi>\<chi> \<chi>\<chi>_def 
                 append_is_Nil_conv last_snoc not_Cons_self2 r(1))
                 subgoal by fact
                 subgoal using \<chi>3' unfolding \<chi>3'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                 subgoal using \<chi>3' unfolding \<chi>3'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto 
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 using llist_all_lappend_llist_of ltr1(3) by blast
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def using ltr2(1) by fastforce
                 subgoal by fact
                 subgoal by fact . . 
           qed
         next
           case R note trn = R note current = current R
           show ?thesis
           proof(cases "lnever isSecO ltr2")
             case True note current = current True
             obtain trn' w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr2 = s2 $ ltr2'" "validTransO (s2, s2')" "Opt.lvalidFromS s2' ltr2'"
             "lcompletedFromO s2' ltr2'" "lnever isIntO ltr2'" and 
             \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv2 = [] then R else L)"
             and ltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]  
             unfolding ltrv1 by blast
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO)"
             have ltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' ..

             show ?thesis 
             proof(cases "trv1 = []")
               case True note trv1 = True
               have sv1': "sv1' = sv1" 
               using \<omega>4 unfolding \<omega>4_def by (simp add: trv1)
               show ?thesis 
               apply(rule Van.llvalidFromS_selectDelay)
               apply(rule exI[of _ "w1'"]) apply(rule exI[of _ n]) 
               apply(rule exI[of _ sv1]) apply(rule exI[of _ "ltrv1'"])  
               apply(intro conjI)
               subgoal .. subgoal ..      
               subgoal unfolding ltrv1 trv1 by simp
               subgoal using \<omega>4 unfolding \<omega>4_def trv1 n by simp
               subgoal apply(rule disjI1) 
                 apply(rule exI[of _ trn'])
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1]) apply(rule exI[of _ "ltr1"])
                 apply(rule exI[of _ s2']) apply(rule exI[of _ ltr2'])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv2']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..  
                   subgoal unfolding ltrv1' trn' trv1 sv1' using trn by simp
                   subgoal using \<omega>4 unfolding \<omega>4_def sv1' by simp
                   subgoal by fact 
                   subgoal using \<omega>4 unfolding \<omega>4_def  
                   by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv) 
                   subgoal by fact
                   subgoal using \<omega>4 unfolding \<omega>4_def   
                   by (metis Nil_is_append_conv Van.reach_validFromS_reach last_snoc not_Cons_self2 r(4))
                   subgoal by fact subgoal by fact subgoal by fact
                   subgoal using \<omega>\<omega> by simp subgoal using \<omega>\<omega> by simp subgoal using \<omega>\<omega> by simp . .
             next
               case False note trv1 = False
               show ?thesis 
               apply(rule Van.llvalidFromS_selectlappend)
               apply(rule exI[of _ sv1]) apply(rule exI[of _ "trv1"])
               apply(rule exI[of _ sv1']) apply(rule exI[of _ "w1'"])  
               apply(rule exI[of _ "ltrv1'"]) apply(rule exI[of _ n]) 
               apply(intro conjI)
                 subgoal .. subgoal ..  
                 subgoal using ltrv1 .
                 subgoal using \<omega>4 unfolding \<omega>4_def  
                 by (metis Nil_is_append_conv Van.validFromS_def Van.validS_append1 hd_append2)
                 subgoal by fact
                 subgoal using \<omega>4 unfolding \<omega>4_def   
                 by (metis Van.validFromS_def Van.validS_validTrans list.sel(1) not_Cons_self2 snoc_eq_iff_butlast trv1)
                 subgoal apply(rule disjI1) 
                 apply(rule exI[of _ trn']) 
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ s1]) apply(rule exI[of _ "ltr1"])
                 apply(rule exI[of _ s2']) apply(rule exI[of _ ltr2'])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv2']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..   
                   subgoal using trv1 unfolding ltrv1' trn' by auto
                   subgoal using \<omega>4 unfolding \<omega>4_def by simp
                   subgoal by fact
                   subgoal using \<omega>4 unfolding \<omega>4_def  
                   by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv)                  
                   subgoal using \<omega>4 unfolding \<omega>4_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                   subgoal using \<omega>4 unfolding \<omega>4_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                   subgoal by fact subgoal by fact subgoal by fact
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> 
                   using llist_all_lappend_llist_of ltr1(3) by blast . . 
             qed
           next  
             case False note current = current False 
             obtain w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'" and 
             \<chi>4': "\<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO "
             and ltrv1: "ltrv1 =
             lappend (llist_of trv1) (lltrv1 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO))" 
             using lltrv1_lltrv2_not_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]    
             unfolding ltrv1 by blast  
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO)"
             have ltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' .. 
                  
             show ?thesis 
             proof(cases "trv1 = []")
               case True note trv1 = True
               hence sv1'': "sv1'' = sv1"  
               by (metis \<chi>4'_def Simple_Transition_System.validFromS_Cons_iff \<chi>4' append.simps(1))
               have "w1' < w1" using trv1 \<chi>4' unfolding \<chi>4'_def by auto
               show ?thesis 
               apply(rule Van.llvalidFromS_selectDelay) 
               apply(rule exI[of _ "w1'"])  apply(rule exI[of _ n])
               apply(rule exI[of _ sv1]) apply(rule exI[of _ "ltrv1"])  
               apply(intro conjI)
                 subgoal ..
                 subgoal .. subgoal .. subgoal unfolding n by fact
                 subgoal apply(rule disjI1) 
                 apply(rule exI[of _ L])
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1]) apply(rule exI[of _ ltr1])
                 apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv2'']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..  
                   subgoal unfolding ltrv1 ltrv1' trv1 sv1'' by simp
                   subgoal using \<chi>4' unfolding \<chi>4'_def sv1'' by simp
                   subgoal by fact
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                   by (metis Opt.reach_validFromS_reach Nil_is_append_conv last_snoc not_Cons_self2 r(2))
                   subgoal by fact
                   subgoal using \<chi>4' r(4) unfolding \<chi>4'_def 
                     by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
                   subgoal by fact subgoal by fact subgoal by fact
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                     using llist_all_lappend_llist_of ltr2(3) by blast . .  
             next
               case False note trv1 = False
               show ?thesis
               apply(rule Van.llvalidFromS_selectlappend)
               apply(rule exI[of _ sv1]) apply(rule exI[of _ "trv1"])
               apply(rule exI[of _ sv1'']) 
               apply(rule exI[of _ "w1'"])  
               apply(rule exI[of _ "ltrv1'"]) 
               apply(rule exI[of _ n])
               apply(intro conjI)
                 subgoal .. subgoal .. 
                 subgoal using ltrv1 .
                 subgoal using \<chi>4' unfolding \<chi>4'_def  
                  by (metis Nil_is_append_conv Van.validFromS_def Van.validS_append1 hd_append2)
                 subgoal using trv1 .
                 subgoal using \<chi>4' unfolding \<chi>4'_def  
                 by (metis Simple_Transition_System.validFromS_def Van.validS_validTrans list.sel(1) 
                   not_Cons_self2 snoc_eq_iff_butlast trv1)
                 subgoal apply(rule disjI1)
                 apply(rule exI[of _ L])  
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1]) apply(rule exI[of _ ltr1])
                 apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv2'']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal .. subgoal unfolding ltrv1' ..
                   subgoal using \<chi>4' unfolding \<chi>4'_def by simp
                   subgoal by fact
                   subgoal using \<chi>4' unfolding \<chi>4'_def  
                   by (metis Simple_Transition_System.reach_validFromS_reach \<chi>\<chi> \<chi>\<chi>_def 
                   append_is_Nil_conv last_snoc not_Cons_self2 r(2))
                   subgoal using \<chi>4' unfolding \<chi>4'_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                   subgoal using \<chi>4' unfolding \<chi>4'_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                   subgoal by fact
                   subgoal by fact
                   subgoal by fact 
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto  
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def   
                     using llist_all_lappend_llist_of ltr2(3) by blast . .
             qed
           qed
         qed
       qed
     qed
   qed
  }
  thus ?thesis apply-apply(rule Van.llvalidFromS_imp_lvalidFromS)
  using assms by blast
qed


lemma lvalidFromS_lltrv2:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
shows "Van.lvalidFromS sv2 (lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  {fix n sv2 ltrv2
   assume "\<exists>trn w1 w2 s1 ltr1 s2 ltr2 statA sv1 statO. 
       n = w2 \<and>   
       ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2"
   hence "Van.llvalidFromS n sv2 ltrv2" 
   proof(coinduct rule: Van.llvalidFromS.coinduct[of "\<lambda>n sv2 ltrv2. 
     \<exists>trn w1 w2 s1 ltr1 s2 ltr2 statA sv1 statO. 
       n = w2 \<and> 
       ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2"])
     case (llvalidFromS n sv2 ltrv2) 
     then obtain trn w1 w2 s1 ltr1 s2 ltr2 statA sv1 statO  
     where n: "n = w2" and 
     ltrv2: "ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
     by auto
     have isi3: "\<not> isIntO s1" using ltr1
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))  
     have isi4: "\<not> isIntO s2" using ltr2
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))
  
     show ?case proof(cases "ltr1 = [[]] \<and> ltr2 = [[]]")
       case True note ltr14 = True
       hence ltrv2: "ltrv2 = [[]]" unfolding ltrv2 by simp
       show ?thesis unfolding ltrv2 apply(rule Van.llvalidFromS_selectLNil) by auto
     next
       case False hence ltr14: "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" by auto
       show ?thesis proof(cases "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0")
         case True note ltr14 = ltr14 True
         hence ltrv2: "ltrv2 = [[sv2]]" unfolding ltrv2 by simp
         show ?thesis unfolding ltrv2 apply(rule Van.llvalidFromS_selectSingl) by auto
       next
         case False hence current: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
         by auto 
         show ?thesis proof(cases trn)
           case L note trn = L note current = current L
           show ?thesis
           proof(cases "lnever isSecO ltr1") 
             case True note current = current True
             obtain trn' w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr1 = s1 $ ltr1'" "validTransO (s1, s1')" "Opt.lvalidFromS s1' ltr1'"
             "lcompletedFromO s1' ltr1'" "lnever isIntO ltr1'" and 
             \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv1 = [] then L else R)"
             and ltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2(trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv2 by blast
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO)"
             have ltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' ..
             
             show ?thesis 
             proof(cases "trv2 = []")
               case True note trv2 = True
               have sv2': "sv2' = sv2" 
               using \<omega>3 unfolding \<omega>3_def by (simp add: trv2)
               show ?thesis 
               apply(rule Van.llvalidFromS_selectDelay)
               apply(rule exI[of _ "w2'"]) apply(rule exI[of _ n]) 
               apply(rule exI[of _ sv2]) apply(rule exI[of _ "ltrv2'"])  
               apply(intro conjI)
               subgoal .. subgoal ..      
               subgoal unfolding ltrv2 trv2 by simp
               subgoal using \<omega>3 unfolding \<omega>3_def trv2 n by simp
               subgoal apply(rule disjI1) 
                 apply(rule exI[of _ trn'])
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1']) apply(rule exI[of _ "ltr1'"])
                 apply(rule exI[of _ s2]) apply(rule exI[of _ ltr2])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv1']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..  
                   subgoal unfolding ltrv2' trn' trv2 sv2' using trn by simp
                   subgoal using \<omega>3 unfolding \<omega>3_def sv2' by simp
                   subgoal using \<omega>3 unfolding \<omega>3_def  
                   by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv) 
                   subgoal by fact  
                   subgoal using \<omega>3 unfolding \<omega>3_def   
                   by (metis Nil_is_append_conv Van.reach_validFromS_reach last_snoc not_Cons_self2 r(3))
                   subgoal by fact
                   subgoal using \<omega>\<omega> by simp subgoal using \<omega>\<omega> by simp subgoal using \<omega>\<omega> by simp                    
                   subgoal by fact subgoal by fact subgoal by fact . .
             next
               case False note trv2 = False
               show ?thesis 
               apply(rule Van.llvalidFromS_selectlappend)
               apply(rule exI[of _ sv2]) apply(rule exI[of _ "trv2"])
               apply(rule exI[of _ sv2']) apply(rule exI[of _ "w2'"])  
               apply(rule exI[of _ "ltrv2'"]) apply(rule exI[of _ n]) 
               apply(intro conjI)
                 subgoal .. subgoal ..  
                 subgoal using ltrv2 .
                 subgoal using \<omega>3 unfolding \<omega>3_def  
                 by (metis Nil_is_append_conv Van.validFromS_def Van.validS_append1 hd_append2)
                 subgoal by fact
                 subgoal using \<omega>3 unfolding \<omega>3_def   
                 by (metis Van.validFromS_def Van.validS_validTrans append_is_Nil_conv list.sel(1) not_Cons_self2 trv2)
                 subgoal apply(rule disjI1) 
                 apply(rule exI[of _ trn']) 
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ s1']) apply(rule exI[of _ "ltr1'"])
                 apply(rule exI[of _ s2]) apply(rule exI[of _ ltr2])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv1']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..   
                   subgoal using trv2 unfolding ltrv2' trn' by auto
                   subgoal using \<omega>3 unfolding \<omega>3_def by simp
                   subgoal using \<omega>3 unfolding \<omega>3_def  
                   by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv) 
                   subgoal by fact
                   subgoal using \<omega>3 unfolding \<omega>3_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                   subgoal using \<omega>3 unfolding \<omega>3_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> 
                   using llist_all_lappend_llist_of ltr1(3) by blast
                   subgoal using \<omega>\<omega> using ltr2(1) by fastforce
                   subgoal by fact
                   subgoal by fact . . 
             qed
           next
             case False note current = current False 
             obtain w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'" and 
             \<chi>3': "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
             and ltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))" 
             using lltrv1_lltrv2_not_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv2 by blast
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)"
             have ltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' .. 
         
             show ?thesis
             proof(cases "trv2 = []")
               case True note trv2 = True
               hence sv2'': "sv2'' = sv2"  
               by (metis \<chi>3'_def Simple_Transition_System.validFromS_Cons_iff \<chi>3' append.simps(1))
               have "w2' < w2" using trv2 \<chi>3' unfolding \<chi>3'_def by auto
               show ?thesis 
               apply(rule Van.llvalidFromS_selectDelay) 
               apply(rule exI[of _ "w2'"])  apply(rule exI[of _ n])
               apply(rule exI[of _ sv2]) apply(rule exI[of _ "ltrv2"])  
               apply(intro conjI)
                 subgoal ..
                 subgoal .. subgoal .. subgoal unfolding n by fact
                 subgoal apply(rule disjI1) 
                 apply(rule exI[of _ R])
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1'']) apply(rule exI[of _ "s1'' $ ltr1'"])
                 apply(rule exI[of _ s2]) apply(rule exI[of _ ltr2])                
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..  
                   subgoal unfolding ltrv2 ltrv2' trv2 sv2'' by simp
                   subgoal using \<chi>3' unfolding \<chi>3'_def sv2'' by simp
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                   by (metis Opt.reach_validFromS_reach Nil_is_append_conv last_snoc not_Cons_self2 r(1))
                   subgoal by fact
                   subgoal using \<chi>3' r(3) unfolding \<chi>3'_def 
                   by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
                   subgoal by fact 
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                     using llist_all_lappend_llist_of ltr1(3) by blast 
                   subgoal by fact subgoal by fact  subgoal by fact . .
             next
               case False note trv2 = False
               show ?thesis
               apply(rule Van.llvalidFromS_selectlappend)
               apply(rule exI[of _ sv2]) apply(rule exI[of _ "trv2"])
               apply(rule exI[of _ sv2'']) apply(rule exI[of _ "w2'"])  
               apply(rule exI[of _ "ltrv2'"]) apply(rule exI[of _ "w2"]) 
               apply(intro conjI)
                 subgoal unfolding n .. subgoal ..  
                 subgoal using ltrv2 .
                 subgoal using \<chi>3' unfolding \<chi>3'_def  
                 by (metis Nil_is_append_conv Van.validFromS_def Van.validS_append1 hd_append2)
                 subgoal by fact
                 subgoal using \<chi>3' unfolding \<chi>3'_def  
                 by (metis Simple_Transition_System.validFromS_def Van.validS_validTrans append_is_Nil_conv list.sel(1) not_Cons_self2 trv2)
                 subgoal apply(rule disjI1) 
                 apply(rule exI[of _ R]) 
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1'']) apply(rule exI[of _ "s1'' $ ltr1'"])
                 apply(rule exI[of _ s2]) apply(rule exI[of _ ltr2])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..   
                   subgoal unfolding ltrv2' ..
                   subgoal using \<chi>3' unfolding \<chi>3'_def by simp
                   subgoal using \<chi>3' unfolding \<chi>3'_def  
                   by (metis Simple_Transition_System.reach_validFromS_reach \<chi>\<chi> \<chi>\<chi>_def 
                   append_is_Nil_conv last_snoc not_Cons_self2 r(1))
                   subgoal by fact
                   subgoal using \<chi>3' unfolding \<chi>3'_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                   subgoal using \<chi>3' unfolding \<chi>3'_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto 
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                   using llist_all_lappend_llist_of ltr1(3) by blast
                   subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def using ltr2(1) by fastforce
                   subgoal by fact
                   subgoal by fact . . 
             qed
           qed
         next
           case R note trn = R note current = current R
           show ?thesis
           proof(cases "lnever isSecO ltr2")
             case True note current = current True
             obtain trn' w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr2 = s2 $ ltr2'" "validTransO (s2, s2')" "Opt.lvalidFromS s2' ltr2'"
             "lcompletedFromO s2' ltr2'" "lnever isIntO ltr2'" and 
             \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv2 = [] then R else L)"
             and ltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]  
             unfolding ltrv2 by blast
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO)"
             have ltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' ..
 
             show ?thesis 
             proof(cases "trv2 = []")
               case True note trv2 = True
               have sv2': "sv2' = sv2" 
               using \<omega>4 unfolding \<omega>4_def by (simp add: trv2)
               show ?thesis 
               apply(rule Van.llvalidFromS_selectDelay)
               apply(rule exI[of _ "w2'"]) apply(rule exI[of _ n]) 
               apply(rule exI[of _ sv2]) apply(rule exI[of _ "ltrv2'"])  
               apply(intro conjI)
               subgoal .. subgoal ..      
               subgoal unfolding ltrv2 trv2 by simp
               subgoal using \<omega>4 unfolding \<omega>4_def trv2 n by simp
               subgoal apply(rule disjI1) 
                 apply(rule exI[of _ trn'])
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1]) apply(rule exI[of _ "ltr1"])
                 apply(rule exI[of _ s2']) apply(rule exI[of _ ltr2'])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv1']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..  
                   subgoal unfolding ltrv2' trn' trv2 sv2' using trn by simp
                   subgoal using \<omega>4 unfolding \<omega>4_def sv2' by simp
                   subgoal by fact 
                   subgoal using \<omega>4 unfolding \<omega>4_def  
                   by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv) 
                   subgoal using \<omega>4 unfolding \<omega>4_def   
                   by (metis Nil_is_append_conv Van.reach_validFromS_reach last_snoc not_Cons_self2 r(3))
                   subgoal by fact subgoal by fact subgoal by fact subgoal by fact
                   subgoal using \<omega>\<omega> by simp subgoal using \<omega>\<omega> by simp subgoal using \<omega>\<omega> by simp . .
             next
               case False note trv2 = False
               show ?thesis 
               apply(rule Van.llvalidFromS_selectlappend)
               apply(rule exI[of _ sv2]) apply(rule exI[of _ "trv2"])
               apply(rule exI[of _ sv2']) apply(rule exI[of _ "w2'"])  
               apply(rule exI[of _ "ltrv2'"]) apply(rule exI[of _ n]) 
               apply(intro conjI)
                 subgoal .. subgoal ..  
                 subgoal using ltrv2 .
                 subgoal using \<omega>4 unfolding \<omega>4_def  
                 by (metis Nil_is_append_conv Van.validFromS_def Van.validS_append1 hd_append2)
                 subgoal by fact
                 subgoal using \<omega>4 unfolding \<omega>4_def    
                 by (metis Van.validFromS_def Van.validS_validTrans append_is_Nil_conv list.sel(1) not_Cons_self2 trv2)
                 subgoal apply(rule disjI1) 
                 apply(rule exI[of _ trn']) 
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) apply(rule exI[of _ s1]) apply(rule exI[of _ "ltr1"])
                 apply(rule exI[of _ s2']) apply(rule exI[of _ ltr2'])
                 apply(rule exI[of _ statA]) apply(rule exI[of _ sv1']) apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..   
                   subgoal using trv2 unfolding ltrv2' trn' by auto
                   subgoal using \<omega>4 unfolding \<omega>4_def by simp
                   subgoal by fact
                   subgoal using \<omega>4 unfolding \<omega>4_def  
                   by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv)                  
                   subgoal using \<omega>4 unfolding \<omega>4_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                   subgoal using \<omega>4 unfolding \<omega>4_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                   subgoal by fact subgoal by fact subgoal by fact
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> 
                   using llist_all_lappend_llist_of ltr1(3) by blast . . 
             qed
           next  
             case False note current = current False 
             obtain w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'" and 
             \<chi>4': "\<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO "
             and ltrv2: "ltrv2 =
             lappend (llist_of trv2) (lltrv2 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO))" 
             using lltrv1_lltrv2_not_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]    
             unfolding ltrv2 by blast  
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO)"
             have ltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' .. 
             have trv2: "trv2 \<noteq> []" using \<chi>4' unfolding \<chi>4'_def by auto
                  
             show ?thesis 
             apply(rule Van.llvalidFromS_selectlappend)
             apply(rule exI[of _ sv2]) apply(rule exI[of _ "trv2"])
             apply(rule exI[of _ sv2'']) 
             apply(rule exI[of _ "w2'"])  
             apply(rule exI[of _ "ltrv2'"]) 
             apply(rule exI[of _ n])
             apply(intro conjI)
               subgoal .. subgoal .. 
               subgoal using ltrv2 .
               subgoal using \<chi>4' unfolding \<chi>4'_def  
               by (metis Nil_is_append_conv Van.validFromS_def Van.validS_append1 hd_append2)
               subgoal using trv2 .
               subgoal using \<chi>4' unfolding \<chi>4'_def  
               by (metis Simple_Transition_System.validFromS_def Van.validS_validTrans append_is_Nil_conv list.sel(1) not_Cons_self2)
               subgoal apply(rule disjI1)
               apply(rule exI[of _ L])  
               apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
               apply(rule exI[of _ s1]) apply(rule exI[of _ ltr1])
               apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"])
               apply(rule exI[of _ statA]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ statOO])
               apply(intro conjI) 
                 subgoal .. subgoal unfolding ltrv2' ..
                 subgoal using \<chi>4' unfolding \<chi>4'_def by simp
                 subgoal by fact
                 subgoal using \<chi>4' unfolding \<chi>4'_def  
                 by (metis Simple_Transition_System.reach_validFromS_reach \<chi>\<chi> \<chi>\<chi>_def 
                   append_is_Nil_conv last_snoc not_Cons_self2 r(2))
                 subgoal using \<chi>4' unfolding \<chi>4'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                 subgoal using \<chi>4' unfolding \<chi>4'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                 subgoal by fact
                 subgoal by fact
                 subgoal by fact 
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto  
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def   
                 using llist_all_lappend_llist_of ltr2(3) by blast . .
           qed
         qed
       qed
     qed
   qed
  }
  thus ?thesis apply-apply(rule Van.llvalidFromS_imp_lvalidFromS)
  using assms by blast
qed

(* *)

lemma lcompletedFrom_lltrv1:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
shows "Van.lcompletedFrom sv1 (lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  {fix ltrv1 assume ltrv1: "ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
   and lfin: "lfinite ltrv1"
   hence "list_of ltrv1 \<noteq> [] \<and> finalV (last (list_of ltrv1))"
   using assms(2-) proof(induct "length (list_of ltrv1)" "w1" 
     arbitrary: trn w2 ltrv1 s1 ltr1 s2 ltr2 statA sv1 sv2 statO 
     rule: less2_induct')
     case (less w1 ltrv1 trn w2 s1 ltr1 s2 ltr2 statA sv1 sv2 statO)
     hence ltrv1: "ltrv1 = lltrv1 (trn, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
     and lfin: "lfinite ltrv1" 
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "lcompletedFromO s1 ltr1" "lnever isIntO ltr1"
     and ltr2: "Opt.lvalidFromS s2 ltr2" "lcompletedFromO s2 ltr2" "lnever isIntO ltr2" 
     by auto
     have isi3: "\<not> isIntO s1" using ltr1
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))  
     have isi4: "\<not> isIntO s2" using ltr2
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))
  
     show ?case proof(cases "ltr1 = [[]] \<and> ltr2 = [[]]")
       case True note ltr14 = True
       hence False using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
       thus ?thesis by auto
     next
       case False hence ltr14: "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" by auto
       show ?thesis proof(cases "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0")
         case True note ltr14 = ltr14 True
         hence ltrv1: "list_of ltrv1 = [sv1]" unfolding ltrv1 by simp  
         have "llength ltr1 = Suc 0 \<or> llength ltr2 = Suc 0"
         using ltr14 
         by (metis Opt.lcompletedFrom_def 
          Suc_ile_eq i0_less lfinite_code(1) llength_eq_0 llist.exhaust 
          ltr1(2) ltr2(2) nle_le not_lnull_conv zero_enat_def) 
         hence "ltr1 = [[s1]] \<or> ltr2 = [[s2]]"  
           using Opt.lcompletedFrom_singl ltr1(1) ltr1(2) ltr2(1) ltr2(2) by blast
         hence "finalO s1 \<or> finalO s2"  
           using Opt.lcompletedFrom_LCons ltr1(2) ltr2(2) by blast 
         hence "finalV sv1"  
           using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by auto
         thus ?thesis unfolding ltrv1 by auto 
       next
         case False hence current: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" by auto
         show ?thesis 
         proof(cases trn)
           case L note current = current L
           show ?thesis
           proof(cases "lnever isSecO ltr1")
             case True note current = current True
             obtain trn' w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr1 = s1 $ ltr1'" "validTransO (s1, s1')" "Opt.lvalidFromS s1' ltr1'"
             "lcompletedFromO s1' ltr1'" "lnever isIntO ltr1'" and 
             \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn' : "trn' = (if trv1 = [] then L else R)"
             and lltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_L[OF unw \<Delta> r ltr1 isi4 current]
             unfolding ltrv1 by blast
             define ltrv1' where ltrv1': "ltrv1' = lltrv1 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO)"
             have lltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding lltrv1 ltrv1' .. 

             have trv1ne: "trv1 \<noteq> [] \<or> w1' < w1" using \<omega>3 unfolding \<omega>3_def by auto
             have lfin': "lfinite ltrv1'"
             using lfin trv1ne unfolding lltrv1 by simp
             have len: "length (list_of ltrv1') < length (list_of ltrv1) \<or> 
                        length (list_of ltrv1') = length (list_of ltrv1) \<and> w1' < w1"
             using trv1ne lfin lfin' by (simp add: list_of_lappend lltrv1)

             have 0: "list_of ltrv1' \<noteq> [] \<and> finalV (last (list_of ltrv1'))"  
             using len proof(elim disjE conjE)
               assume len: "length (list_of ltrv1') < length (list_of ltrv1)"
               show ?thesis 
               apply(rule less(1)[OF _ ltrv1'])
                 subgoal by fact subgoal by fact              
                 subgoal using \<omega>3 unfolding \<omega>3_def by simp
                 subgoal by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv)
                 subgoal by fact
                 subgoal using \<omega>3 unfolding \<omega>3_def 
                 by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)  
                 subgoal using \<omega>3 unfolding \<omega>3_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal by fact subgoal by fact subgoal by fact  subgoal by fact
                 subgoal by fact subgoal by fact .
             next
               assume len: "length (list_of ltrv1') = length (list_of ltrv1)" "w1' < w1"
               show ?thesis   
               apply(rule less(2)[OF _ _ ltrv1'])
                 subgoal by fact subgoal using len by simp subgoal by fact             
                 subgoal using \<omega>3 unfolding \<omega>3_def by simp
                 subgoal by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv)
                 subgoal by fact
                 subgoal using \<omega>3 unfolding \<omega>3_def 
                 by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)  
                 subgoal using \<omega>3 unfolding \<omega>3_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal by fact subgoal by fact subgoal by fact  subgoal by fact
                 subgoal by fact subgoal by fact . 
             qed
             show ?thesis unfolding lltrv1 using 0  
             by (simp add: lfin' list_of_lappend)
           next
             case False note current = current False 
             obtain w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'" and 
             \<chi>3': "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
             and lltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))" 
             using lltrv1_lltrv2_not_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv1 by blast
             define ltrv1' where ltrv1': "ltrv1' = lltrv1 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)"

             have lltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding lltrv1 ltrv1' .. 
             have trv1ne: "trv1 \<noteq> []" using \<chi>3' unfolding \<chi>3'_def by auto
             have lfin': "lfinite ltrv1'"
             using lfin trv1ne unfolding lltrv1 by simp
             have len: "length (list_of ltrv1') < length (list_of ltrv1)"
             using trv1ne lfin lfin' by (simp add: list_of_lappend lltrv1)
   
             have 0: "list_of ltrv1' \<noteq> [] \<and> finalV (last (list_of ltrv1'))"
             apply(rule less(1)[OF _ ltrv1'])
               subgoal by fact subgoal by fact              
               subgoal using \<chi>3' unfolding \<chi>3'_def by simp
               subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 by (metis Simple_Transition_System.reach_validFromS_reach r(1) snoc_eq_iff_butlast)
               subgoal by fact
               subgoal using \<chi>3' unfolding \<chi>3'_def  
               by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc r(3))
               subgoal using \<chi>3' unfolding \<chi>3'_def   
               by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
               subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by simp 
               subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by simp  
               subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 using llist_all_lappend_llist_of ltr1 by blast
               subgoal by fact  subgoal by fact subgoal by fact  . 
             show ?thesis unfolding lltrv1 using 0  
               by (simp add: lfin' list_of_lappend)
           qed
         next
           case R note current = current R
           show ?thesis
           proof(cases "lnever isSecO ltr2")
             case True note current = current True
             obtain trn' w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr2 = s2 $ ltr2'" "validTransO (s2, s2')" "Opt.lvalidFromS s2' ltr2'"
             "lcompletedFromO s2' ltr2'" "lnever isIntO ltr2'" and 
             \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv2 = [] then R else L)"
             and ltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]  
             unfolding ltrv1 by blast
             define ltrv1' where ltrv1': "ltrv1' = lltrv1 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO)"
             have lltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' ..
      
             have trv1ne: "trv1 \<noteq> [] \<or> w1' < w1" using \<omega>4 unfolding \<omega>4_def by auto
             have lfin': "lfinite ltrv1'"
             using lfin trv1ne unfolding lltrv1 by simp
             have len: "length (list_of ltrv1') < length (list_of ltrv1) \<or> 
                        length (list_of ltrv1') = length (list_of ltrv1) \<and> w1' < w1"
             using trv1ne lfin lfin' by (simp add: list_of_lappend lltrv1)

             have 0: "list_of ltrv1' \<noteq> [] \<and> finalV (last (list_of ltrv1'))"  
             using len proof(elim disjE conjE)
               assume len: "length (list_of ltrv1') < length (list_of ltrv1)"
               show ?thesis 
               apply(rule less(1)[OF _ ltrv1'])
                 subgoal by fact subgoal by fact              
                 subgoal using \<omega>4 unfolding \<omega>4_def by simp
                 subgoal by fact
                 subgoal using r(2) \<omega>\<omega> by (metis Opt.reach.Step fst_conv snd_conv)
                 subgoal using \<omega>4 unfolding \<omega>4_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(3))
                 subgoal using \<omega>4 unfolding \<omega>4_def 
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal by fact subgoal by fact subgoal by fact  subgoal by fact
                 subgoal by fact subgoal by fact .
             next
               assume len: "length (list_of ltrv1') = length (list_of ltrv1)" "w1' < w1"
               show ?thesis   
               apply(rule less(2)[OF _ _ ltrv1'])
                 subgoal by fact subgoal using len by simp subgoal by fact             
                 subgoal using \<omega>4 unfolding \<omega>4_def by simp
                 subgoal by fact
                 subgoal by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv)
                 subgoal using \<omega>4 unfolding \<omega>4_def 
                 by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)  
                 subgoal using \<omega>4 unfolding \<omega>4_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal by fact subgoal by fact subgoal by fact  subgoal by fact
                 subgoal by fact subgoal by fact . 
             qed
             show ?thesis unfolding lltrv1 using 0  
             by (simp add: lfin' list_of_lappend)
           next
             case False note current = current False 
             obtain w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'" and 
             \<chi>4': "\<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO "
             and ltrv1: "ltrv1 =
             lappend (llist_of trv1) (lltrv1 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO))" 
             using lltrv1_lltrv2_not_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]    
             unfolding ltrv1 by blast  
             define ltrv1' where ltrv1': "ltrv1' = lltrv1 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO)"
             have lltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' .. 

             have trv1ne: "trv1 \<noteq> [] \<or> w1' < w1" using \<chi>4' unfolding \<chi>4'_def by auto
             have lfin': "lfinite ltrv1'"
             using lfin trv1ne unfolding lltrv1 by simp
             have len: "length (list_of ltrv1') < length (list_of ltrv1) \<or> 
                        length (list_of ltrv1') = length (list_of ltrv1) \<and> w1' < w1"
             using trv1ne lfin lfin' by (simp add: list_of_lappend lltrv1)

             have 0: "list_of ltrv1' \<noteq> [] \<and> finalV (last (list_of ltrv1'))"  
             using len proof(elim disjE conjE)
               assume len: "length (list_of ltrv1') < length (list_of ltrv1)"
               show ?thesis 
               apply(rule less(1)[OF _ ltrv1'])
                 subgoal by fact subgoal by fact              
                 subgoal using \<chi>4' unfolding \<chi>4'_def by simp
                 subgoal by fact
                 subgoal using r(2) \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
                 subgoal using \<chi>4' unfolding \<chi>4'_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(3))
                 subgoal using \<chi>4' unfolding \<chi>4'_def 
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal by fact subgoal by fact subgoal by fact  
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                   using llist_all_lappend_llist_of ltr2(3) by blast .
             next
               assume len: "length (list_of ltrv1') = length (list_of ltrv1)" "w1' < w1"
               show ?thesis   
               apply(rule less(2)[OF _ _ ltrv1'])
                 subgoal by fact subgoal using len by simp subgoal by fact             
                 subgoal using \<chi>4' unfolding \<chi>4'_def by simp
                 subgoal by fact
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                   by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(2))
                 subgoal using \<chi>4' unfolding \<chi>4'_def 
                 by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)  
                 subgoal using \<chi>4' unfolding \<chi>4'_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc r(4))
                 subgoal by fact subgoal by fact subgoal by fact   
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                   using llist_all_lappend_llist_of ltr2(3) by blast .
             qed
             show ?thesis unfolding lltrv1 using 0  
             by (simp add: lfin' list_of_lappend)
           qed
         qed
       qed
     qed
   qed         
  }
  thus ?thesis unfolding Van.lcompletedFrom_def by auto
qed

lemma lcompletedFrom_lltrv2:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
shows "Van.lcompletedFrom sv2 (lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  {fix ltrv2 assume ltrv2: "ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
   and lfin: "lfinite ltrv2"
   hence "list_of ltrv2 \<noteq> [] \<and> finalV (last (list_of ltrv2))"
   using assms(2-) proof(induct "length (list_of ltrv2)" "w2" 
     arbitrary: ltrv2 trn w1 s1 ltr1 s2 ltr2 statA sv1 sv2 statO 
     rule: less2_induct')
     case (less w2 ltrv2 trn w1 s1 ltr1 s2 ltr2 statA sv1 sv2 statO)
     hence ltrv2: "ltrv2 = lltrv2 (trn, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
     and lfin: "lfinite ltrv2" 
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "lcompletedFromO s1 ltr1" "lnever isIntO ltr1"
     and ltr2: "Opt.lvalidFromS s2 ltr2" "lcompletedFromO s2 ltr2" "lnever isIntO ltr2" 
     by auto
     have isi3: "\<not> isIntO s1" using ltr1
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))  
     have isi4: "\<not> isIntO s2" using ltr2
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))
  
     show ?case proof(cases "ltr1 = [[]] \<and> ltr2 = [[]]")
       case True note ltr14 = True
       hence False using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
       thus ?thesis by auto
     next
       case False hence ltr14: "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" by auto
       show ?thesis proof(cases "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0")
         case True note ltr14 = ltr14 True
         hence ltrv2: "list_of ltrv2 = [sv2]" unfolding ltrv2 by simp  
         have "llength ltr1 = Suc 0 \<or> llength ltr2 = Suc 0"
         using ltr14 
         by (metis Opt.lcompletedFrom_def 
          Suc_ile_eq i0_less lfinite_code(1) llength_eq_0 llist.exhaust 
          ltr1(2) ltr2(2) nle_le not_lnull_conv zero_enat_def) 
         hence "ltr1 = [[s1]] \<or> ltr2 = [[s2]]"  
           using Opt.lcompletedFrom_singl ltr1(1) ltr1(2) ltr2(1) ltr2(2) by blast
         hence "finalO s1 \<or> finalO s2"  
           using Opt.lcompletedFrom_LCons ltr1(2) ltr2(2) by blast 
         hence "finalV sv2"  
           using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by auto
         thus ?thesis unfolding ltrv2 by auto 
       next
         case False hence current: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" by auto
         show ?thesis 
         proof(cases trn)
           case L note current = current L
           show ?thesis
           proof(cases "lnever isSecO ltr1")
             case True note current = current True
             obtain trn' w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr1 = s1 $ ltr1'" "validTransO (s1, s1')" "Opt.lvalidFromS s1' ltr1'"
             "lcompletedFromO s1' ltr1'" "lnever isIntO ltr1'" and 
             \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn' : "trn' = (if trv1 = [] then L else R)"
             and lltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_L[OF unw \<Delta> r ltr1 isi4 current]
             unfolding ltrv2 by blast
             define ltrv2' where ltrv2': "ltrv2' = lltrv2 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO)"
             have lltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding lltrv2 ltrv2' .. 

             have trv2ne: "trv2 \<noteq> [] \<or> w2' < w2" using \<omega>3 unfolding \<omega>3_def by auto
             have lfin': "lfinite ltrv2'"
             using lfin trv2ne unfolding lltrv2 by simp
             have len: "length (list_of ltrv2') < length (list_of ltrv2) \<or> 
                        length (list_of ltrv2') = length (list_of ltrv2) \<and> w2' < w2"
             using trv2ne lfin lfin' by (simp add: list_of_lappend lltrv2)

             have 0: "list_of ltrv2' \<noteq> [] \<and> finalV (last (list_of ltrv2'))"  
             using len proof(elim disjE conjE)
               assume len: "length (list_of ltrv2') < length (list_of ltrv2)"
               show ?thesis 
               apply(rule less(1)[OF _ ltrv2'])
                 subgoal by fact subgoal by fact              
                 subgoal using \<omega>3 unfolding \<omega>3_def by simp
                 subgoal by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv)
                 subgoal by fact
                 subgoal using \<omega>3 unfolding \<omega>3_def 
                 by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)  
                 subgoal using \<omega>3 unfolding \<omega>3_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal by fact subgoal by fact subgoal by fact  subgoal by fact
                 subgoal by fact subgoal by fact .
             next
               assume len: "length (list_of ltrv2') = length (list_of ltrv2)" "w2' < w2"
               show ?thesis   
               apply(rule less(2)[OF _ _ ltrv2'])
                 subgoal by fact subgoal using len by simp subgoal by fact             
                 subgoal using \<omega>3 unfolding \<omega>3_def by simp
                 subgoal by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv)
                 subgoal by fact
                 subgoal using \<omega>3 unfolding \<omega>3_def 
                 by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)  
                 subgoal using \<omega>3 unfolding \<omega>3_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal by fact subgoal by fact subgoal by fact  subgoal by fact
                 subgoal by fact subgoal by fact . 
             qed
             show ?thesis unfolding lltrv2 using 0  
             by (simp add: lfin' list_of_lappend)
           next
             case False note current = current False 
             obtain w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'" and 
             \<chi>3': "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
             and lltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))" 
             using lltrv1_lltrv2_not_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv2 by blast
             define ltrv2' where ltrv2': "ltrv2' = lltrv2 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)"
             have lltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding lltrv2 ltrv2' .. 

             have trv2ne: "trv2 \<noteq> [] \<or> w2' < w2" using \<chi>3' unfolding \<chi>3'_def by auto
             have lfin': "lfinite ltrv2'"
             using lfin trv2ne unfolding lltrv2 by simp
             have len: "length (list_of ltrv2') < length (list_of ltrv2) \<or> 
                        length (list_of ltrv2') = length (list_of ltrv2) \<and> w2' < w2"
             using trv2ne lfin lfin' by (simp add: list_of_lappend lltrv2)

             have 0: "list_of ltrv2' \<noteq> [] \<and> finalV (last (list_of ltrv2'))"  
             using len proof(elim disjE conjE)
               assume len: "length (list_of ltrv2') < length (list_of ltrv2)"
               show ?thesis 
               apply(rule less(1)[OF _ ltrv2']) 
                 subgoal by fact subgoal by fact              
                 subgoal using \<chi>3' unfolding \<chi>3'_def by simp
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 by (metis Simple_Transition_System.reach_validFromS_reach r(1) snoc_eq_iff_butlast)
                 subgoal by fact
                 subgoal using \<chi>3' unfolding \<chi>3'_def  
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc r(3))
                 subgoal using \<chi>3' unfolding \<chi>3'_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by simp 
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by simp  
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 using llist_all_lappend_llist_of ltr1 by blast
                 subgoal by fact  subgoal by fact subgoal by fact .  
             next
               assume len: "length (list_of ltrv2') = length (list_of ltrv2)" "w2' < w2"
               show ?thesis   
               apply(rule less(2)[OF _ _ ltrv2'])
                 subgoal by fact subgoal using len by simp subgoal by fact             
                 subgoal using \<chi>3' unfolding \<chi>3'_def by simp
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def 
                   by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(1))
                 subgoal by fact
                 subgoal using \<chi>3' unfolding \<chi>3'_def 
                 by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)  
                 subgoal using \<chi>3' unfolding \<chi>3'_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                   using llist_all_lappend_llist_of ltr1(3) by blast
                 subgoal by fact subgoal by fact subgoal by fact . 
             qed
             show ?thesis unfolding lltrv2 using 0  
             by (simp add: lfin' list_of_lappend)           
           qed
         next
           case R note current = current R
           show ?thesis
           proof(cases "lnever isSecO ltr2")
             case True note current = current True
             obtain trn' w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr2 = s2 $ ltr2'" "validTransO (s2, s2')" "Opt.lvalidFromS s2' ltr2'"
             "lcompletedFromO s2' ltr2'" "lnever isIntO ltr2'" and 
             \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv2 = [] then R else L)"
             and ltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]  
             unfolding ltrv2 by blast
             define ltrv2' where ltrv2': "ltrv2' = lltrv2 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO)"
             have lltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' ..
      
             have trv2ne: "trv2 \<noteq> [] \<or> w2' < w2" using \<omega>4 unfolding \<omega>4_def by auto
             have lfin': "lfinite ltrv2'"
             using lfin trv2ne unfolding lltrv2 by simp
             have len: "length (list_of ltrv2') < length (list_of ltrv2) \<or> 
                        length (list_of ltrv2') = length (list_of ltrv2) \<and> w2' < w2"
             using trv2ne lfin lfin' by (simp add: list_of_lappend lltrv2)

             have 0: "list_of ltrv2' \<noteq> [] \<and> finalV (last (list_of ltrv2'))"  
             using len proof(elim disjE conjE)
               assume len: "length (list_of ltrv2') < length (list_of ltrv2)"
               show ?thesis 
               apply(rule less(1)[OF _ ltrv2'])
                 subgoal by fact subgoal by fact              
                 subgoal using \<omega>4 unfolding \<omega>4_def by simp
                 subgoal by fact
                 subgoal using r(2) \<omega>\<omega> by (metis Opt.reach.Step fst_conv snd_conv)
                 subgoal using \<omega>4 unfolding \<omega>4_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(3))
                 subgoal using \<omega>4 unfolding \<omega>4_def 
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal by fact subgoal by fact subgoal by fact  subgoal by fact
                 subgoal by fact subgoal by fact .
             next
               assume len: "length (list_of ltrv2') = length (list_of ltrv2)" "w2' < w2"
               show ?thesis   
               apply(rule less(2)[OF _ _ ltrv2'])
                 subgoal by fact subgoal using len by simp subgoal by fact             
                 subgoal using \<omega>4 unfolding \<omega>4_def by simp
                 subgoal by fact
                 subgoal by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv)
                 subgoal using \<omega>4 unfolding \<omega>4_def 
                 by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)  
                 subgoal using \<omega>4 unfolding \<omega>4_def   
                 by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(4))
                 subgoal by fact subgoal by fact subgoal by fact  subgoal by fact
                 subgoal by fact subgoal by fact . 
             qed
             show ?thesis unfolding lltrv2 using 0  
             by (simp add: lfin' list_of_lappend)
           next
             case False note current = current False 
             obtain w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'" and 
             \<chi>4': "\<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO "
             and ltrv2: "ltrv2 =
             lappend (llist_of trv2) (lltrv2 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO))" 
             using lltrv1_lltrv2_not_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]    
             unfolding ltrv2 by blast  
             define ltrv2' where ltrv2': "ltrv2' = lltrv2 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO)"
             have lltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' .. 

             have trv2ne: "trv2 \<noteq> []" using \<chi>4' unfolding \<chi>4'_def by auto
             have lfin': "lfinite ltrv2'"
             using lfin trv2ne unfolding lltrv2 by simp
             have len: "length (list_of ltrv2') < length (list_of ltrv2)"
             using trv2ne lfin lfin' by (simp add: list_of_lappend lltrv2)

             have 0: "list_of ltrv2' \<noteq> [] \<and> finalV (last (list_of ltrv2'))"  
             apply(rule less(1)[OF _ ltrv2'])
               subgoal by fact subgoal by fact              
               subgoal using \<chi>4' unfolding \<chi>4'_def by simp
               subgoal by fact
               subgoal using r(2) \<chi>\<chi> unfolding \<chi>\<chi>_def  
               by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
               subgoal using \<chi>4' unfolding \<chi>4'_def   
               by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2 r(3))
               subgoal using \<chi>4' unfolding \<chi>4'_def 
               by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc r(4))
               subgoal by fact subgoal by fact subgoal by fact  
               subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
               subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
               subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
               using llist_all_lappend_llist_of ltr2(3) by blast .              
             show ?thesis unfolding lltrv2 using 0  
             by (simp add: lfin' list_of_lappend)
           qed
         qed
       qed
     qed
   qed         
  }
  thus ?thesis unfolding Van.lcompletedFrom_def by auto
qed

lemma lS_lltrv1_ltr1:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2" 
shows "Van.lS (lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)) = Opt.lS ltr1"
proof-
  have cltrv1: "Van.lcompletedFrom sv1 (lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_lltrv1[OF assms] .
  {fix trn nL nR ltrv1 ltr1
   assume "\<exists>w1 w2 s1 s2 ltr2 statA sv1 sv2 statO. 
       nL = w1 \<and> nR = w2 \<and>  
       ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2"
   hence "TwoFuncPred.sameFM1 isSecV isSecO getSecV getSecO trn nL nR ltrv1 ltr1" 
   proof(coinduct rule: TwoFuncPred.sameFM1.coinduct[of "\<lambda>trn nL nR ltrv1 ltr1. 
       \<exists>w1 w2 s1 s2 ltr2 statA sv1 sv2 statO.  
       nL = w1 \<and> nR = w2 \<and> 
       ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2", 
       where pred = isSecV and pred' = isSecO and func = getSecV and func' = getSecO])
     case (2 trn nL nR ltrv1 ltr1) 
     then obtain w1 w2 sv1 s1 s2 ltr2 statA sv2 statO  
     where nL: "nL = w1" and nR: "nR = w2" 
     and ltrv1: "ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
     by auto
     have isi3: "\<not> isIntO s1" using ltr1
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))  
     have isi4: "\<not> isIntO s2" using ltr2
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))
  
     show ?case proof(cases "ltr1 = [[]] \<and> ltr2 = [[]]")
       case True note ltr14 = True
       hence ltrv1: "ltrv1 = [[]]" unfolding ltrv1 by simp
       show ?thesis using ltr14 unfolding ltrv1 apply-apply(rule TwoFuncPred.sameFM1_selectLNil) by auto
     next
       case False hence ltr14: "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" by auto
       show ?thesis proof(cases "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0")
         case True note ltr14 = ltr14 True
         hence ltrv1: "ltrv1 = [[sv1]]" unfolding ltrv1 by simp 
         have "llength ltr1 = Suc 0 \<or> llength ltr2 = Suc 0" 
         by (metis Opt.lcompletedFrom_def Suc_ile_eq True 
            lfinite_LNil llength_LNil llist_eq_cong ltr1(2) 
           ltr2(2) nle_le order_le_imp_less_or_eq zero_enat_def zero_order(3))
         hence "finalO s1 \<or> finalO s2" 
         using Opt.lcompletedFrom_singl ltr1(1) ltr1(2) ltr2(1) ltr2(2) by blast
         hence fs1: "finalO s1"  
         using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by auto
         hence ltr1: "ltr1 = [[s1]]"  
         by (metis Opt.final_def Opt.lcompletedFrom_def 
              Opt.lvalidFromS_Cons_iff lfinite_code(1) llist.exhaust ltr1(1) ltr1(2))
         have fsv1: "finalV sv1" 
         using \<Delta> fs1 r(1) r(2) r(3) r(4) unw unwindCond_final by blast
         have isv13: "\<not> isSecV sv1 \<and> \<not> isSecO s1"
         using fsv1 fs1 Opt.final_not_isSec Van.final_not_isSec by blast
         show ?thesis unfolding ltrv1 ltr1 apply(rule TwoFuncPred.sameFM1_selectSingl) 
         using isv13 by auto
       next
         case False hence current: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
         by auto 
         show ?thesis proof(cases trn)
           case L note trn = L[simp] note current = current L
           show ?thesis
           proof(cases "lnever isSecO ltr1")
             case True note current = current True
             obtain trn' w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr1 = s1 $ ltr1'" "validTransO (s1, s1')" "Opt.lvalidFromS s1' ltr1'"
             "lcompletedFromO s1' ltr1'" "lnever isIntO ltr1'" and 
             \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv1 = [] then L else R)"
             and lltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv1 by blast
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO)"
             have ltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding lltrv1 ltrv1' ..
             have nis1: "\<not> isSecO s1" using True \<omega>\<omega>(1) by force
             show ?thesis 
             proof(cases "trv1 = []")
               case True note trv1 = True
               hence "w1' < w1" using \<omega>3 unfolding \<omega>3_def by auto
               have [simp]: "trn' = trn" by (simp add: trv1 trn')
               show ?thesis
               apply(rule TwoFuncPred.sameFM1_selectDelayL)
               apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w1"]) 
               apply(rule exI[of _ "trv1"])  apply(rule exI[of _ "[s1]"])  
               apply(rule exI[of _ "w2'"])
               apply(rule exI[of _ "ltrv1'"])  apply(rule exI[of _ "ltr1'"])    
               apply(rule exI[of _ "w2"])                                    
               apply(intro conjI)
                 subgoal by fact
                 subgoal unfolding nL ..  subgoal unfolding nR ..
                 subgoal unfolding ltrv1 trv1 by simp
                 subgoal unfolding \<omega>\<omega>(1) by simp 
                 subgoal by fact subgoal unfolding trv1 using \<omega>3_def nis1 by simp
                 subgoal apply(rule disjI1) 
                   apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                   apply(rule exI[of _ s1']) apply(rule exI[of _ s2]) 
                   apply(rule exI[of _ ltr2]) apply(rule exI[of _ statA])
                   apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2'])
                   apply(rule exI[of _ statOO])
                   apply(intro conjI) 
                     subgoal ..  subgoal .. 
                     subgoal unfolding ltrv1' by simp
                     subgoal using \<omega>3 unfolding \<omega>3_def by simp
                     subgoal using \<omega>3 unfolding \<omega>3_def  
                     by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv) 
                     subgoal by fact
                     subgoal using \<omega>3 unfolding \<omega>3_def   
                     by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                     subgoal using \<omega>3 unfolding \<omega>3_def   
                     by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> 
                     using llist_all_lappend_llist_of ltr1(3) by blast
                     subgoal using \<omega>\<omega> using ltr2(1) by fastforce
                     subgoal by fact
                     subgoal by fact . .
             next
               case False note trv1 = False 
               show ?thesis
               apply(rule TwoFuncPred.sameFM1_selectlappend)
               apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "[s1]"])
               apply(rule exI[of _ trn']) apply(rule exI[of _ "w1'"])
               apply(rule exI[of _ "w2'"])
               apply(rule exI[of _ "ltrv1'"])  apply(rule exI[of _ "ltr1'"]) 
               apply(rule exI[of _ trn])           
               apply(rule exI[of _ "w1"])      
               apply(rule exI[of _ "w2"])        
               apply(intro conjI)
                 subgoal ..
                 subgoal unfolding nL ..  subgoal unfolding nR ..
                 subgoal using ltrv1 .
                 subgoal unfolding \<omega>\<omega>(1) by simp 
                 subgoal by fact
                 subgoal using \<omega>3 unfolding \<omega>3_def by simp
                 subgoal using ltr1(3) \<omega>3 unfolding \<omega>3_def  
                 by (metis Opt.S.map_filter Opt.S.simps(4) Van.S.map_filter Van.S.eq_Nil_iff(2) append_Nil 
                 butlast_snoc filter.simps(2) nis1)
                 subgoal apply(rule disjI1) 
                   apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                   apply(rule exI[of _ s1']) apply(rule exI[of _ s2]) 
                   apply(rule exI[of _ ltr2]) apply(rule exI[of _ statA])
                   apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2'])
                   apply(rule exI[of _ statOO])
                   apply(intro conjI) 
                     subgoal ..  subgoal ..
                     subgoal unfolding ltrv1' ..
                     subgoal using \<omega>3 unfolding \<omega>3_def by simp
                     subgoal using \<omega>3 unfolding \<omega>3_def  
                     by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv) 
                     subgoal by fact
                     subgoal using \<omega>3 unfolding \<omega>3_def   
                     by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                     subgoal using \<omega>3 unfolding \<omega>3_def   
                     by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> 
                     using llist_all_lappend_llist_of ltr1(3) by blast
                     subgoal using \<omega>\<omega> using ltr2(1) by fastforce
                     subgoal by fact
                     subgoal by fact . .
             qed
           next
             case False note current = current False 
             obtain w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'" and 
             \<chi>3': "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
             and lltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))" 
             using lltrv1_lltrv2_not_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv1 by blast
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)"
             have ltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding lltrv1 ltrv1' .. 
           
             show ?thesis apply(rule TwoFuncPred.sameFM1_selectlappend)
             apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "tr1 ## s1'"])
             apply(rule exI[of _ R]) 
             apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w2'"])
             apply(rule exI[of _ "ltrv1'"])  apply(rule exI[of _ "s1'' $ ltr1'"])            
             apply(rule exI[of _ trn]) 
             apply(rule exI[of _ "w1"]) apply(rule exI[of _ "w2"])
             apply(intro conjI)
               subgoal ..  subgoal unfolding nL ..  subgoal unfolding nR ..
               subgoal using ltrv1 . 
               subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by simp 
               subgoal using \<chi>3' unfolding \<chi>3'_def by simp
               subgoal by simp
               subgoal using \<chi>3' unfolding \<chi>3'_def  
               by (simp add: Opt.S.map_filter Van.S.map_filter)               
               subgoal apply(rule disjI1) 
               apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
               apply(rule exI[of _ s1''])
               apply(rule exI[of _ s2]) apply(rule exI[of _ ltr2])
               apply(rule exI[of _ statA]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2'']) 
               apply(rule exI[of _ statOO])
               apply(intro conjI) 
                 subgoal ..  subgoal ..
                 subgoal unfolding ltrv1' ..
                 subgoal using \<chi>3' unfolding \<chi>3'_def by simp
                 subgoal using \<chi>3' unfolding \<chi>3'_def  
                 by (metis Simple_Transition_System.reach_validFromS_reach \<chi>\<chi> \<chi>\<chi>_def 
                 append_is_Nil_conv last_snoc not_Cons_self2 r(1))
                 subgoal by fact
                 subgoal using \<chi>3' unfolding \<chi>3'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                 subgoal using \<chi>3' unfolding \<chi>3'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto 
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 using llist_all_lappend_llist_of ltr1(3) by blast
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def using ltr2(1) by fastforce
                 subgoal by fact
                 subgoal by fact . . 
           qed
         next
           case R note trn = R[simp] note current = current R
           show ?thesis
           proof(cases "lnever isSecO ltr2")
             case True note current = current True
             obtain trn' w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr2 = s2 $ ltr2'" "validTransO (s2, s2')" "Opt.lvalidFromS s2' ltr2'"
             "lcompletedFromO s2' ltr2'" "lnever isIntO ltr2'" and 
             \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv2 = [] then R else L)"
             and ltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]  
             unfolding ltrv1 by blast
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO)"
             have ltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' ..
             have nev1: "never isSecV trv1" using \<omega>4 unfolding \<omega>4_def by auto
             show ?thesis 
             proof(cases "trv2 = []")
               case True note trv2 = True
               have [simp]: "trn' = trn" using R trv2 trn' by auto
               have "w2' < w2" using \<omega>4 trv2 unfolding \<omega>4_def by auto
               show ?thesis 
               apply(rule TwoFuncPred.sameFM1_selectDelayR)
               apply(rule exI[of _ "w2'"]) apply(rule exI[of _ nR])
               apply(rule exI[of _ trv1]) apply(rule exI[of _ "[]"])
               apply(rule exI[of _ "w1'"])
               apply(rule exI[of _ "ltrv1'"])  apply(rule exI[of _ "ltr1"])    
               apply(rule exI[of _ nL])                
               apply(intro conjI)
                 subgoal by simp subgoal .. subgoal ..
                 subgoal by fact  subgoal by simp
                 subgoal unfolding nR by fact
                 subgoal using nev1 by (simp add: never_Nil_filter)
                 subgoal apply(rule disjI1) 
                   apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                   apply(rule exI[of _ s1]) apply(rule exI[of _ s2']) 
                   apply(rule exI[of _ ltr2']) apply(rule exI[of _ statA])
                   apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2'])
                   apply(rule exI[of _ statOO])
                   apply(intro conjI) 
                     subgoal ..  subgoal ..
                     subgoal unfolding ltrv1' by simp
                     subgoal using \<omega>4 unfolding \<omega>4_def by simp
                     subgoal by fact
                     subgoal using \<omega>4 unfolding \<omega>4_def  
                     by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv)                      
                     subgoal using \<omega>4 unfolding \<omega>4_def   
                     by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                     subgoal using \<omega>4 unfolding \<omega>4_def   
                     by (metis Van.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                     subgoal by fact  subgoal by fact  subgoal by fact
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto . .
             next
               case False note trv2 = False
               have [simp]: "trn' = L"  using R trv2 trn' by auto
               show ?thesis 
               apply(rule TwoFuncPred.sameFM1_selectRL)
               apply(rule exI[of _ trv1]) apply(rule exI[of _ "[]"])
               apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w2'"]) 
               apply(rule exI[of _ "ltrv1'"])  apply(rule exI[of _ "ltr1"]) 
               apply(rule exI[of _ "w1"]) apply(rule exI[of _ "w2"])                    
               apply(intro conjI)
                 subgoal by fact
                 subgoal unfolding nL ..  subgoal unfolding nR ..
                 subgoal unfolding ltrv1 ..
                 subgoal unfolding \<omega>\<omega>(1) by simp 
                 subgoal using \<omega>4 unfolding \<omega>4_def by (simp add:  never_Nil_filter)
                 subgoal apply(rule disjI1) 
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1]) apply(rule exI[of _ s2']) 
                 apply(rule exI[of _ ltr2']) apply(rule exI[of _ statA])
                 apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2'])
                 apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..   subgoal ..
                   subgoal unfolding ltrv1' by simp
                     subgoal using \<omega>4 unfolding \<omega>4_def by simp
                     subgoal by fact
                     subgoal using \<omega>4 unfolding \<omega>4_def  
                     by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv)                      
                     subgoal using \<omega>4 unfolding \<omega>4_def   
                     by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                     subgoal using \<omega>4 unfolding \<omega>4_def   
                     by (metis Van.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                     subgoal by fact  subgoal by fact  subgoal by fact
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto . .
             qed                 
           next
             case False note current = current False 
             obtain w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'" and 
             \<chi>4': "\<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO "
             and ltrv1: "ltrv1 =
             lappend (llist_of trv1) (lltrv1 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO))" 
             using lltrv1_lltrv2_not_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]    
             unfolding ltrv1 by blast  
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO)"
             have ltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' .. 
                  
             show ?thesis   
             apply(rule TwoFuncPred.sameFM1_selectRL)
             apply(rule exI[of _ trv1]) apply(rule exI[of _ "[]"])
             apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w2'"]) 
             apply(rule exI[of _ "ltrv1'"])  apply(rule exI[of _ "ltr1"]) 
             apply(rule exI[of _ "w1"]) apply(rule exI[of _ "w2"])                    
             apply(intro conjI)
               subgoal by fact
               subgoal unfolding nL ..  subgoal unfolding nR ..
               subgoal unfolding ltrv1 ..  subgoal by simp
               subgoal using \<chi>4' unfolding \<chi>4'_def by (simp add:  never_Nil_filter)
               subgoal apply(rule disjI1) 
               apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
               apply(rule exI[of _ s1]) apply(rule exI[of _ s2'']) 
               apply(rule exI[of _ "s2'' $ ltr2'"]) apply(rule exI[of _ statA])
               apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2''])
               apply(rule exI[of _ statOO])
               apply(intro conjI) 
                 subgoal ..   subgoal ..
                 subgoal unfolding ltrv1' by simp
                 subgoal using \<chi>4' unfolding \<chi>4'_def by simp
                 subgoal by fact
                 subgoal using r(2) \<chi>\<chi> unfolding \<chi>\<chi>_def 
                 by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)                
                 subgoal using r(3) \<chi>4' unfolding \<chi>4'_def  
                 by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
                 subgoal using r(4) \<chi>4' unfolding \<chi>4'_def  
                 by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
                 subgoal by fact  subgoal by fact subgoal by fact 
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 using llist_all_lappend_llist_of ltr2(3) by blast . .     
          qed
        qed
      qed
    qed
  qed
  }
  thus ?thesis unfolding Van.lS[OF cltrv1] Opt.lS[OF ltr1(2)]
  apply- apply(rule TwoFuncPred.sameFM1_lmap_lfilter)
  using assms by blast
qed
 
lemma lS_lltrv2_ltr2:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2" 
shows "Van.lS (lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)) = Opt.lS ltr2"
proof-
  have cltrv2: "Van.lcompletedFrom sv2 (lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_lltrv2[OF assms] .
  {fix trn nL nR ltrv2 ltr2
   assume "\<exists>w1 w2 s1 s2 ltr1 statA sv1 sv2 statO. 
       nL = w1 \<and> nR = w2 \<and>  
       ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2"
   hence "TwoFuncPred.sameFM2 isSecV isSecO getSecV getSecO trn nL nR ltrv2 ltr2" 
   proof(coinduct rule: TwoFuncPred.sameFM2.coinduct[of "\<lambda>trn nL nR ltrv2 ltr2. 
       \<exists>w1 w2 s1 s2 ltr1 statA sv1 sv2 statO.  
       nL = w1 \<and> nR = w2 \<and> 
       ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2", 
       where pred = isSecV and pred' = isSecO and func = getSecV and func' = getSecO])
     case (2 trn nL nR ltrv2 ltr2) 
     then obtain w1 w2 sv1 s1 s2 ltr1 statA sv2 statO  
     where nL: "nL = w1" and nR: "nR = w2" 
     and ltrv2: "ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
     by auto
     have isi3: "\<not> isIntO s1" using ltr1
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))  
     have isi4: "\<not> isIntO s2" using ltr2
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))
  
     show ?case proof(cases "ltr1 = [[]] \<and> ltr2 = [[]]")
       case True note ltr14 = True
       hence ltrv2: "ltrv2 = [[]]" unfolding ltrv2 by simp
       show ?thesis using ltr14 unfolding ltrv2 apply-apply(rule TwoFuncPred.sameFM2_selectLNil) by auto
     next
       case False hence ltr14: "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" by auto
       show ?thesis proof(cases "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0")
         case True note ltr14 = ltr14 True
         hence ltrv2: "ltrv2 = [[sv2]]" unfolding ltrv2 by simp 
         have "llength ltr1 = Suc 0 \<or> llength ltr2 = Suc 0" 
         by (metis Opt.lcompletedFrom_def Suc_ile_eq True 
            lfinite_LNil llength_LNil llist_eq_cong ltr1(2) 
           ltr2(2) nle_le order_le_imp_less_or_eq zero_enat_def zero_order(3))
         hence "finalO s1 \<or> finalO s2" 
         using Opt.lcompletedFrom_singl ltr1(1) ltr1(2) ltr2(1) ltr2(2) by blast
         hence fs2: "finalO s2"  
         using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by auto
         hence ltr2: "ltr2 = [[s2]]"  
         by (metis Opt.final_def Opt.lcompletedFrom_def 
              Opt.lvalidFromS_Cons_iff lfinite_code(1) llist.exhaust ltr2(1) ltr2(2))
         have fsv2: "finalV sv2" 
         using \<Delta> fs2 r(1) r(2) r(3) r(4) unw unwindCond_final by blast
         have isv24: "\<not> isSecV sv2 \<and> \<not> isSecO s2"
         using fsv2 fs2 Opt.final_not_isSec Van.final_not_isSec by blast
         show ?thesis unfolding ltrv2 ltr2 apply(rule TwoFuncPred.sameFM2_selectSingl) 
         using isv24 by auto
       next
         case False hence current: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
         by auto 
         show ?thesis proof(cases trn)
           case L note trn = L[simp] note current = current L
           show ?thesis
           proof(cases "lnever isSecO ltr1")
             case True note current = current True
             obtain trn' w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr1 = s1 $ ltr1'" "validTransO (s1, s1')" "Opt.lvalidFromS s1' ltr1'"
             "lcompletedFromO s1' ltr1'" "lnever isIntO ltr1'" and 
             \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv1 = [] then L else R)"
             and lltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv2 by blast
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO)"
             have ltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding lltrv2 ltrv2' ..
             have nev2: "never isSecV trv2" using \<omega>3 unfolding \<omega>3_def by auto
             show ?thesis 
             proof(cases "trv1 = []")
               case True note trv1 = True
               have [simp]: "trn' = trn" using L trv1 trn' by auto
               have "w1' < w1" using \<omega>3 trv1 unfolding \<omega>3_def by auto
               show ?thesis 
               apply(rule TwoFuncPred.sameFM2_selectDelayL)
               apply(rule exI[of _ "w1'"]) apply(rule exI[of _ nL])
               apply(rule exI[of _ trv2]) apply(rule exI[of _ "[]"])
               apply(rule exI[of _ "w2'"])
               apply(rule exI[of _ "ltrv2'"])  apply(rule exI[of _ "ltr2"])    
               apply(rule exI[of _ nR])                
               apply(intro conjI)
                 subgoal by simp subgoal .. subgoal ..
                 subgoal by fact  subgoal by simp
                 subgoal unfolding nL by fact
                 subgoal using nev2 by (simp add: never_Nil_filter)
                 subgoal apply(rule disjI1) 
                   apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                   apply(rule exI[of _ s1']) apply(rule exI[of _ s2]) 
                   apply(rule exI[of _ ltr1']) apply(rule exI[of _ statA])
                   apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2'])
                   apply(rule exI[of _ statOO])
                   apply(intro conjI) 
                     subgoal ..  subgoal ..
                     subgoal unfolding ltrv2' by simp
                     subgoal using \<omega>3 unfolding \<omega>3_def by simp
                     subgoal using \<omega>3 unfolding \<omega>3_def  
                     by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv) 
                     subgoal by fact                                        
                     subgoal using \<omega>3 unfolding \<omega>3_def   
                     by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                     subgoal using \<omega>3 unfolding \<omega>3_def   
                     by (metis Van.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto 
                     subgoal by fact  subgoal by fact  subgoal by fact . .                      
             next
               case False note trv1 = False
               have [simp]: "trn' = R"  using L trv1 trn' by auto
               show ?thesis 
               apply(rule TwoFuncPred.sameFM2_selectLR)
               apply(rule exI[of _ trv2]) apply(rule exI[of _ "[]"])
               apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w2'"]) 
               apply(rule exI[of _ "ltrv2'"])  apply(rule exI[of _ "ltr2"]) 
               apply(rule exI[of _ "w1"]) apply(rule exI[of _ "w2"])                    
               apply(intro conjI)
                 subgoal by fact
                 subgoal unfolding nL ..  subgoal unfolding nR ..
                 subgoal unfolding ltrv2 ..
                 subgoal unfolding \<omega>\<omega>(1) by simp 
                 subgoal using \<omega>3 unfolding \<omega>3_def by (simp add:  never_Nil_filter)
                 subgoal apply(rule disjI1) 
                 apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1']) apply(rule exI[of _ s2]) 
                 apply(rule exI[of _ ltr1']) apply(rule exI[of _ statA])
                 apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2'])
                 apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal ..   subgoal ..
                   subgoal unfolding ltrv2' by simp
                     subgoal using \<omega>3 unfolding \<omega>3_def by simp
                     subgoal using \<omega>3 unfolding \<omega>3_def  
                     by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv) 
                     subgoal by fact                                          
                     subgoal using \<omega>3 unfolding \<omega>3_def   
                     by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                     subgoal using \<omega>3 unfolding \<omega>3_def   
                     by (metis Van.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto 
                     subgoal by fact  subgoal by fact  subgoal by fact . .                   
             qed                 
           next
             case False note current = current False 
             obtain w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'" and 
             \<chi>3': "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
             and lltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))" 
             using lltrv1_lltrv2_not_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv2 by blast
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)"
             have ltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding lltrv2 ltrv2' .. 

             show ?thesis   
             apply(rule TwoFuncPred.sameFM2_selectLR)
             apply(rule exI[of _ trv2]) apply(rule exI[of _ "[]"])
             apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w2'"]) 
             apply(rule exI[of _ "ltrv2'"])  apply(rule exI[of _ "ltr2"]) 
             apply(rule exI[of _ "w1"]) apply(rule exI[of _ "w2"])                    
             apply(intro conjI)
               subgoal by fact
               subgoal unfolding nL ..  subgoal unfolding nR ..
               subgoal unfolding ltrv2 ..  subgoal by simp
               subgoal using \<chi>3' unfolding \<chi>3'_def by (simp add: never_Nil_filter)
               subgoal apply(rule disjI1) 
               apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
               apply(rule exI[of _ s1'']) apply(rule exI[of _ s2]) 
               apply(rule exI[of _ "s1'' $ ltr1'"]) apply(rule exI[of _ statA])
               apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2''])
               apply(rule exI[of _ statOO])
               apply(intro conjI) 
                 subgoal ..   subgoal ..
                 subgoal unfolding ltrv2' by simp
                 subgoal using \<chi>3' unfolding \<chi>3'_def by simp
                 subgoal using r(1) \<chi>\<chi> unfolding \<chi>\<chi>_def 
                 by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)                
                 subgoal by fact
                 subgoal using r(3) \<chi>3' unfolding \<chi>3'_def  
                 by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
                 subgoal using r(4) \<chi>3' unfolding \<chi>3'_def  
                 by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)                
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 using llist_all_lappend_llist_of ltr1(3) by blast
                 subgoal by fact  subgoal by fact subgoal by fact  . .     
           qed
         next
           case R note trn = R[simp] note current = current R
           show ?thesis
           proof(cases "lnever isSecO ltr2")
             case True note current = current True
             obtain trn' w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr2 = s2 $ ltr2'" "validTransO (s2, s2')" "Opt.lvalidFromS s2' ltr2'"
             "lcompletedFromO s2' ltr2'" "lnever isIntO ltr2'" and 
             \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv2 = [] then R else L)"
             and ltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]  
             unfolding ltrv2 by blast
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO)"
             have ltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' ..             
             have nis2: "\<not> isSecO s2" using True \<omega>\<omega>(1) by force
             
             show ?thesis 
             proof(cases "trv2 = []")
               case True note trv2 = True
               hence "w2' < w2" using \<omega>4 unfolding \<omega>4_def by auto
               have [simp]: "trn' = trn" by (simp add: trv2 trn')
               show ?thesis
               apply(rule TwoFuncPred.sameFM2_selectDelayR)
               apply(rule exI[of _ "w2'"]) apply(rule exI[of _ "w2"]) 
               apply(rule exI[of _ "trv2"])  apply(rule exI[of _ "[s2]"])  
               apply(rule exI[of _ "w1'"])
               apply(rule exI[of _ "ltrv2'"])  apply(rule exI[of _ "ltr2'"])    
               apply(rule exI[of _ "w1"])                                    
               apply(intro conjI)
                 subgoal by fact
                 subgoal unfolding nL ..  subgoal unfolding nR ..
                 subgoal unfolding ltrv2 trv2 by simp
                 subgoal unfolding \<omega>\<omega>(1) by simp 
                 subgoal by fact subgoal unfolding trv2 using \<omega>4_def nis2 by simp
                 subgoal apply(rule disjI1) 
                   apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                   apply(rule exI[of _ s1]) apply(rule exI[of _ s2']) 
                   apply(rule exI[of _ ltr1]) apply(rule exI[of _ statA])
                   apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2'])
                   apply(rule exI[of _ statOO])
                   apply(intro conjI) 
                     subgoal ..  subgoal .. 
                     subgoal unfolding ltrv2' by simp
                     subgoal using \<omega>4 unfolding \<omega>4_def by simp
                     subgoal by fact
                     subgoal using \<omega>4 unfolding \<omega>4_def  
                     by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv)                     
                     subgoal using \<omega>4 unfolding \<omega>4_def   
                     by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                     subgoal using \<omega>4 unfolding \<omega>4_def   
                     by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                     subgoal by fact subgoal by fact subgoal by fact 
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> 
                     using llist_all_lappend_llist_of ltr1(3) by blast . .
             next
               case False note trv2 = False 
               show ?thesis
               apply(rule TwoFuncPred.sameFM2_selectlappend)
               apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "[s2]"])
               apply(rule exI[of _ trn']) apply(rule exI[of _ "w1'"])
               apply(rule exI[of _ "w2'"])
               apply(rule exI[of _ "ltrv2'"])  apply(rule exI[of _ "ltr2'"]) 
               apply(rule exI[of _ trn])           
               apply(rule exI[of _ "w1"])      
               apply(rule exI[of _ "w2"])        
               apply(intro conjI)
                 subgoal ..
                 subgoal unfolding nL ..  subgoal unfolding nR ..
                 subgoal using ltrv2 .
                 subgoal unfolding \<omega>\<omega>(1) by simp 
                 subgoal by fact
                 subgoal using \<omega>4 unfolding \<omega>4_def by simp
                 subgoal using ltr1(3) \<omega>4 unfolding \<omega>4_def 
                 by (simp add: never_Nil_filter nis2) 
                 subgoal apply(rule disjI1) 
                   apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                   apply(rule exI[of _ s1]) apply(rule exI[of _ s2']) 
                   apply(rule exI[of _ ltr1]) apply(rule exI[of _ statA])
                   apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2'])
                   apply(rule exI[of _ statOO])
                   apply(intro conjI) 
                     subgoal ..  subgoal ..
                     subgoal unfolding ltrv2' ..
                     subgoal using \<omega>4 unfolding \<omega>4_def by simp
                     subgoal by fact
                     subgoal using \<omega>4 unfolding \<omega>4_def  
                     by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv)                     
                     subgoal using \<omega>4 unfolding \<omega>4_def   
                     by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                     subgoal using \<omega>4 unfolding \<omega>4_def   
                     by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                     subgoal by fact subgoal by fact subgoal by fact 
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> by auto
                     subgoal using \<omega>\<omega> 
                     using llist_all_lappend_llist_of ltr1(3) by blast . .
             qed
           next
             case False note current = current False 
             obtain w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'" and 
             \<chi>4': "\<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO "
             and ltrv2: "ltrv2 =
             lappend (llist_of trv2) (lltrv2 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO))" 
             using lltrv1_lltrv2_not_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]    
             unfolding ltrv2 by blast  
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO)"
             have ltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' ..  
             show ?thesis 
             apply(rule TwoFuncPred.sameFM2_selectlappend)
             apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "tr2 ## s2'"])
             apply(rule exI[of _ L]) 
             apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w2'"])
             apply(rule exI[of _ "ltrv2'"])  apply(rule exI[of _ "s2'' $ ltr2'"])            
             apply(rule exI[of _ trn]) 
             apply(rule exI[of _ "w1"]) apply(rule exI[of _ "w2"])
             apply(intro conjI)
               subgoal ..  subgoal unfolding nL ..  subgoal unfolding nR ..
               subgoal using ltrv2 . 
               subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by simp 
               subgoal using \<chi>4' unfolding \<chi>4'_def by simp
               subgoal by simp
               subgoal using \<chi>4' unfolding \<chi>4'_def  
               by (simp add: Opt.S.map_filter Van.S.map_filter)               
               subgoal apply(rule disjI1) 
               apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
               apply(rule exI[of _ s1])
               apply(rule exI[of _ s2'']) apply(rule exI[of _ ltr1])
               apply(rule exI[of _ statA]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2'']) 
               apply(rule exI[of _ statOO])
               apply(intro conjI) 
                 subgoal ..  subgoal ..
                 subgoal unfolding ltrv2' ..
                 subgoal using \<chi>4' unfolding \<chi>4'_def by simp
                 subgoal by fact
                 subgoal using \<chi>4' unfolding \<chi>4'_def  
                 by (metis Simple_Transition_System.reach_validFromS_reach \<chi>\<chi> \<chi>\<chi>_def 
                 append_is_Nil_conv last_snoc not_Cons_self2 r(2))                 
                 subgoal using \<chi>4' unfolding \<chi>4'_def   
                 by (metis Van.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                 subgoal using \<chi>4' unfolding \<chi>4'_def   
                 by (metis Van.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                 subgoal by fact subgoal by fact subgoal by fact 
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto 
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 using llist_all_lappend_llist_of ltr2(3) by blast . . 
          qed
        qed
      qed
    qed
  qed
  }
  thus ?thesis unfolding Van.lS[OF cltrv2] Opt.lS[OF ltr2(2)]
  apply- apply(rule TwoFuncPred.sameFM2_lmap_lfilter)
  using assms by blast
qed

(* *)

lemma lA_lltrv1_lltrv2:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
shows "Van.lA (lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)) = 
       Van.lA (lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  have cltrv1: "Van.lcompletedFrom sv1 (lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_lltrv1[OF assms] .
  have cltrv2: "Van.lcompletedFrom sv2 (lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_lltrv2[OF assms] . 
  {fix nL nR ltrv1 ltrv2
   assume "\<exists>trn w1 w2 s1 ltr1 s2 ltr2 statA sv1 sv2 statO.  
       nL = w1 \<and> nR = w2 \<and> 
       ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2"
   hence "TwoFuncPred.sameFM isIntV isIntV getActV getActV nL nR ltrv1 ltrv2" 
   proof(coinduct rule: TwoFuncPred.sameFM.coinduct[of "\<lambda>nL nR ltrv1 ltrv2. 
       \<exists> trn w1 w2 s1 ltr1 s2 ltr2 statA sv1 sv2 statO.  
       nL = w1 \<and> nR = w2 \<and> 
       ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> lnever isIntO ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> lnever isIntO ltr2"])
     case (2 nL nR ltrv1 ltrv2) 
     then obtain trn w1 w2 s1 ltr1 s2 ltr2 statA sv1 sv2 statO 
     where nL: "nL = w1" and nR: "nR = w2" 
     and ltrv1: "ltrv1 = lltrv1 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and ltrv2: "ltrv2 = lltrv2 (trn,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" "lnever isIntO ltr1"
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" "lnever isIntO ltr2"
     by auto
     have isi3: "\<not> isIntO s1" using ltr1
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))  
     have isi4: "\<not> isIntO s2" using ltr2
     by (metis Opt.lcompletedFrom_def Opt.lvalidFromS_def lfinite_LNil llist.exhaust_sel llist.pred_inject(2))
  
     show ?case proof(cases "ltr1 = [[]] \<and> ltr2 = [[]]")
       case True note ltr14 = True
       hence ltrv1: "ltrv1 = [[]]" unfolding ltrv1 by simp
       show ?thesis using ltr14 unfolding ltrv1 ltrv2 apply-apply(rule TwoFuncPred.sameFM_selectLNil) by auto
     next
       case False hence ltr14: "ltr1 \<noteq> [[]] \<or> ltr2 \<noteq> [[]]" by auto
       show ?thesis proof(cases "llength ltr1 \<le> Suc 0 \<or> llength ltr2 \<le> Suc 0")
         case True note ltr14 = ltr14 True
         hence ltrv1: "ltrv1 = [[sv1]]" and ltrv2: "ltrv2 = [[sv2]]" unfolding ltrv1 ltrv2 by auto
         have "llength ltr1 = Suc 0 \<or> llength ltr2 = Suc 0" 
         by (metis Opt.lcompletedFrom_def Suc_ile_eq True 
            lfinite_LNil llength_LNil llist_eq_cong ltr1(2) 
           ltr2(2) nle_le order_le_imp_less_or_eq zero_enat_def zero_order(3))
         hence "finalO s1 \<or> finalO s2" 
         using Opt.lcompletedFrom_singl ltr1(1) ltr1(2) ltr2(1) ltr2(2) by blast
         hence fs1: "finalO s1 \<and> finalO s2"  
         using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by auto

         have fsv12: "finalV sv1 \<and> finalV sv2" 
         using \<Delta> fs1 r(1) r(2) r(3) r(4) unw unwindCond_final by blast
         have isv12: "\<not> isIntV sv1 \<and> \<not> isIntV sv2"
         using fsv12 Van.final_not_isInt by blast
         show ?thesis unfolding ltrv1 ltrv2 apply(rule TwoFuncPred.sameFM_selectSingl) 
         using isv12 by auto
       next
         case False hence current: "llength ltr1 > Suc 0" "llength ltr2 > Suc 0" 
         by auto 
         show ?thesis proof(cases trn)
           case L note current = current L
           show ?thesis
           proof(cases "lnever isSecO ltr1")
             case True note current = current True
             obtain trn' w1' w2' s1' ltr1' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr1 = s1 $ ltr1'" "validTransO (s1, s1')" "Opt.lvalidFromS s1' ltr1'"
             "lcompletedFromO s1' ltr1'" "lnever isIntO ltr1'" and 
             \<omega>3: "\<omega>3 \<Delta> w1 w2 w1' w2' s1 s1' s2 statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv1 = [] then L else R)" 
             and lltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO))" 
             and lltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv1 ltrv2 by blast
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO)"
             have lltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding lltrv1 ltrv1' ..
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (trn', w1', w2', s1', ltr1', s2, ltr2, statA, sv1', sv2', statOO)"
             have lltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding lltrv2 ltrv2' .. 
         
             show ?thesis 
             apply(rule TwoFuncPred.sameFM_selectlappend)
             apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w1"]) 
             apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "w2'"]) apply(rule exI[of _ "w2"]) 
             apply(rule exI[of _ "ltrv1'"])  apply(rule exI[of _ "ltrv2'"])                    
             apply(intro conjI)
               subgoal unfolding nL ..  subgoal unfolding nR .. 
               subgoal using lltrv1 .
               subgoal using lltrv2 .
               subgoal using \<omega>3 unfolding \<omega>3_def by simp
               subgoal using \<omega>3 unfolding \<omega>3_def by simp
               subgoal using \<omega>3 unfolding \<omega>3_def by (simp add: Van.A.map_filter)                
               subgoal apply(rule disjI1) 
                 apply(rule exI[of _ trn']) apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
                 apply(rule exI[of _ s1']) apply(rule exI[of _ ltr1']) 
                 apply(rule exI[of _ s2]) apply(rule exI[of _ ltr2]) 
                 apply(rule exI[of _ statA])
                 apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2'])
                 apply(rule exI[of _ statOO])
                 apply(intro conjI) 
                   subgoal .. subgoal ..
                   subgoal unfolding ltrv1' ..
                   subgoal unfolding ltrv2' ..
                   subgoal using \<omega>3 unfolding \<omega>3_def by simp
                   subgoal using \<omega>3 unfolding \<omega>3_def  
                   by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(1) snd_conv) 
                   subgoal by fact
                   subgoal using \<omega>3 unfolding \<omega>3_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                   subgoal using \<omega>3 unfolding \<omega>3_def   
                   by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> by auto
                   subgoal using \<omega>\<omega> 
                   using llist_all_lappend_llist_of ltr1(3) by blast
                   subgoal using \<omega>\<omega> using ltr2(1) by fastforce
                   subgoal by fact
                   subgoal by fact . .
           next
             case False note current = current False 
             obtain w1' w2' tr1 s1' s1'' ltr1' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s1 ltr1 tr1 s1' s1'' ltr1'" and 
             \<chi>3': "\<chi>3' \<Delta> w1 w2 w1' w2' s1 tr1 s1' s1'' s2 statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
             and lltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))" 
             and lltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO))"
             using lltrv1_lltrv2_not_lnever_L[OF unw \<Delta> r ltr1 isi4 current] 
             unfolding ltrv1 ltrv2 by blast
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)"
             have lltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding lltrv1 ltrv1' .. 
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (R,w1',w2',s1'',s1'' $ ltr1',s2,ltr2,statA,sv1'',sv2'',statOO)"
             have lltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding lltrv2 ltrv2' .. 
           
             show ?thesis apply(rule TwoFuncPred.sameFM_selectlappend)
             apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w1"]) 
             apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "w2'"]) apply(rule exI[of _ "w2"]) 
             apply(rule exI[of _ "ltrv1'"]) apply(rule exI[of _ "ltrv2'"])
             apply(intro conjI)
               subgoal unfolding nL .. subgoal unfolding nR ..
               subgoal using lltrv1 . 
               subgoal using lltrv2 .
               subgoal using \<chi>3' unfolding \<chi>3'_def by auto
               subgoal using \<chi>3' unfolding \<chi>3'_def by auto
               subgoal using \<chi>3' unfolding \<chi>3'_def by (simp add: Van.A.map_filter)               
               subgoal apply(rule disjI1) 
               apply(rule exI[of _ R])  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
               apply(rule exI[of _ s1'']) apply(rule exI[of _ "s1'' $ ltr1'"]) 
               apply(rule exI[of _ s2]) apply(rule exI[of _ "ltr2"]) 
               apply(rule exI[of _ statA]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2'']) 
               apply(rule exI[of _ statOO])
               apply(intro conjI) 
                 subgoal ..subgoal ..
                 subgoal unfolding ltrv1' ..
                 subgoal unfolding ltrv2' ..
                 subgoal using \<chi>3' unfolding \<chi>3'_def by simp
                 subgoal using \<chi>3' unfolding \<chi>3'_def  
                 by (metis Simple_Transition_System.reach_validFromS_reach \<chi>\<chi> \<chi>\<chi>_def 
                 append_is_Nil_conv last_snoc not_Cons_self2 r(1))
                 subgoal by fact
                 subgoal using \<chi>3' unfolding \<chi>3'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                 subgoal using \<chi>3' unfolding \<chi>3'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto 
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def  
                 using llist_all_lappend_llist_of ltr1(3) by blast
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def using ltr2(1) by fastforce
                 subgoal by fact
                 subgoal by fact . . 
           qed
         next
           case R note current = current R
           show ?thesis
           proof(cases "lnever isSecO ltr2")
             case True note current = current True
             obtain trn' w1' w2' s2' ltr2' trv1 sv1' trv2 sv2' statOO where 
             \<omega>\<omega>: "ltr2 = s2 $ ltr2'" "validTransO (s2, s2')" "Opt.lvalidFromS s2' ltr2'"
             "lcompletedFromO s2' ltr2'" "lnever isIntO ltr2'" and 
             \<omega>4: "\<omega>4 \<Delta> w1 w2 w1' w2' s1 s2 s2' statA sv1 trv1 sv1' sv2 trv2 sv2' statOO"
             and trn': "trn' = (if trv2 = [] then R else L)"
             and ltrv1: "ltrv1 = 
             lappend (llist_of trv1) (lltrv1 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO))" 
             and ltrv2: "ltrv2 = 
             lappend (llist_of trv2) (lltrv2 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO))" 
             using lltrv1_lltrv2_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]  
             unfolding ltrv1 ltrv2 by blast
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO)"
             have lltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' ..
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (trn', w1', w2', s1, ltr1, s2', ltr2', statA, sv1', sv2', statOO)"
             have lltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' ..
             show ?thesis 
             apply(rule TwoFuncPred.sameFM_selectlappend)  
             apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w1"]) 
             apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "w2'"]) apply(rule exI[of _ "w2"])            
             apply(rule exI[of _ "ltrv1'"]) apply(rule exI[of _ "ltrv2'"])
             apply(intro conjI)
               subgoal unfolding nL ..  subgoal unfolding nR ..
               subgoal using lltrv1 .
               subgoal using lltrv2 .
               subgoal using \<omega>4 unfolding \<omega>4_def by simp
               subgoal using \<omega>4 unfolding \<omega>4_def by simp
               subgoal using \<omega>4 unfolding \<omega>4_def by (simp add: Van.A.map_filter)
               subgoal apply(rule disjI1) 
               apply(rule exI[of _ trn'])  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
               apply(rule exI[of _ s1]) apply(rule exI[of _ "ltr1"]) 
               apply(rule exI[of _ s2']) apply(rule exI[of _ "ltr2'"])
               apply(rule exI[of _ statA]) apply(rule exI[of _ sv1']) apply(rule exI[of _ sv2']) 
               apply(rule exI[of _ statOO])
               apply(intro conjI) 
                 subgoal .. subgoal ..
                 subgoal unfolding ltrv1' ..
                 subgoal unfolding ltrv2' ..
                 subgoal using \<omega>4 unfolding \<omega>4_def by simp 
                 subgoal by fact
                 subgoal using \<omega>4 unfolding \<omega>4_def  
                 by (metis Opt.reach.Step \<omega>\<omega>(2) fst_conv r(2) snd_conv) 
                 subgoal using \<omega>4 unfolding \<omega>4_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                 subgoal using \<omega>4 unfolding \<omega>4_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                 subgoal by fact
                 subgoal by fact
                 subgoal by fact
                 subgoal by fact
                 subgoal using \<omega>\<omega> by auto
                 subgoal using \<omega>\<omega> by auto . . 
           next
             case False note current = current False 
             obtain w1' w2' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statOO where 
             \<chi>\<chi>: "\<chi>\<chi> s2 ltr2 tr2 s2' s2'' ltr2'" and 
             \<chi>4': "\<chi>4' \<Delta> w1 w2 w1' w2' s1 s2 tr2 s2' s2'' statA sv1 trv1 sv1'' sv2 trv2 sv2'' statOO "
             and ltrv1: "ltrv1 =
             lappend (llist_of trv1) (lltrv1 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO))" 
             and ltrv2: "ltrv2 =
             lappend (llist_of trv2) (lltrv2 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO))" 
             using lltrv1_lltrv2_not_lnever_R[OF unw \<Delta> r ltr2(1,2) isi3 ltr2(3) current]    
             unfolding ltrv1 ltrv2 by blast 
             define ltrv1' where ltrv1': "ltrv1' \<equiv> lltrv1 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO)"
             have lltrv1: "ltrv1 = lappend (llist_of trv1) ltrv1'"
             unfolding ltrv1 ltrv1' .. 
             define ltrv2' where ltrv2': "ltrv2' \<equiv> lltrv2 (L, w1', w2', s1, ltr1, s2'', s2'' $ ltr2', statA, sv1'', sv2'', statOO)"
             have lltrv2: "ltrv2 = lappend (llist_of trv2) ltrv2'"
             unfolding ltrv2 ltrv2' .. 
                  
             show ?thesis 
             apply(rule TwoFuncPred.sameFM_selectlappend)
             apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w1"]) 
             apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "w2'"]) apply(rule exI[of _ "w2"])
             apply(rule exI[of _ "ltrv1'"]) apply(rule exI[of _ "ltrv2'"]) 
             apply(intro conjI)
               subgoal unfolding nL ..  subgoal unfolding nR ..
               subgoal using lltrv1 .
               subgoal using lltrv2 .
               subgoal using \<chi>4' unfolding \<chi>4'_def by simp
               subgoal using \<chi>4' unfolding \<chi>4'_def by simp
               subgoal using \<chi>4' unfolding \<chi>4'_def by (simp add: Van.A.map_filter)
               subgoal apply(rule disjI1) 
               apply(rule exI[of _ L]) apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
               apply(rule exI[of _ s1]) apply(rule exI[of _ "ltr1"])  
               apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"])
               apply(rule exI[of _ statA]) 
               apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2'']) apply(rule exI[of _ statOO])
               apply(intro conjI) 
                 subgoal .. subgoal ..
                 subgoal unfolding ltrv1' ..
                 subgoal unfolding ltrv2' ..
                 subgoal using \<chi>4' unfolding \<chi>4'_def by simp
                 subgoal by fact
                 subgoal using \<chi>4' unfolding \<chi>4'_def  
                 by (metis Simple_Transition_System.reach_validFromS_reach \<chi>\<chi> \<chi>\<chi>_def 
                   append_is_Nil_conv last_snoc not_Cons_self2 r(2))
                 subgoal using \<chi>4' unfolding \<chi>4'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(3) snoc_eq_iff_butlast)
                 subgoal using \<chi>4' unfolding \<chi>4'_def   
                 by (metis Simple_Transition_System.reach_validFromS_reach r(4) snoc_eq_iff_butlast)
                 subgoal by fact
                 subgoal by fact
                 subgoal by fact 
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def by auto  
                 subgoal using \<chi>\<chi> unfolding \<chi>\<chi>_def   
                 using llist_all_lappend_llist_of ltr2(3) by blast . .
           qed
         qed
       qed
     qed
   qed
  }
  thus ?thesis unfolding Van.lA[OF cltrv1] Van.lA[OF cltrv2]
  apply- apply(rule TwoFuncPred.sameFM_lmap_lfilter)
  using assms by blast
qed



(*************)
(*************)

fun isN :: "('stateO,'stateV) tuple34 \<Rightarrow> bool"
where 
"isN (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<longleftrightarrow> ltr1 = [[]] \<or> ltr2 = [[]]"

fun H_T :: 
"('stateO,'stateV)tuple34 \<Rightarrow> 
 ('stateO,'stateV)tuple12 \<times> 
 ('stateO,'stateV)tuple34"
where 
"H_T (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
 (let (tr1,s1',s1'',ltr1',tr2,s2',s2'',ltr2') = 
      (SOME k. case k of (tr1,s1',s1'',ltr1',tr2,s2',s2'',ltr2') \<Rightarrow> 
         \<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2')
  in let (w1',w2',trv1,sv1'',trv2,sv2'',statAA,statOO) = 
           (SOME k'. case k' of (w1',w2',trv1,sv1'',trv2,sv2'',statAA,statOO) \<Rightarrow> 
            \<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO)
  in ((trv1,sv1'',trv2,sv2'',statAA,statOO),
      (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))
 )"

declare H_T.simps[simp del]

definition "H \<equiv> fst o H_T" 
definition "T \<equiv> snd o H_T" 

fun Econd where "Econd (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = (lnever isIntO ltr1)"

fun E where "E (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = f (L,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"

definition F :: "('stateO,'stateV)tuple34 \<Rightarrow> ('stateO,'stateV)tuple12 llist"
where "F \<equiv> ccorec_llist isN H Econd E T" 

(* *)

lemma F_LNil: 
"ltr1 = [[]] \<or> ltr2 = [[]] \<Longrightarrow> F (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[]]"
unfolding F_def apply(subst llist_ccorec(1)) by auto

lemma F_lnever: 
assumes "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]" "lnever isIntO ltr1" 
shows "F (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = f (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)" 
using assms unfolding F_def apply(subst llist_ccorec(2))  
  subgoal unfolding E.simps lnull_def apply(rule f_not_LNil) by auto
  subgoal using assms  by auto
  subgoal unfolding Econd.simps by auto .

lemma F_not_lnever: 
assumes "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]" "\<not> lnever isIntO ltr1" 
shows "F (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)  = 
   LCons (H (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)) (F (T (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) ))" 
using assms unfolding F_def apply(subst llist_ccorec(2))  
  subgoal unfolding E.simps lnull_def apply(rule f_not_LNil) by auto
  subgoal using assms  by auto
  subgoal unfolding Econd.simps by auto .

(* *)

definition ltrv1 ::" ('stateO,'stateV)tuple34 \<Rightarrow> 'stateV llist" where 
"ltrv1 tp = lconcat (lmap (\<lambda>(trv1,sv1'',trv2,sv2'',statAA,statOO). llist_of trv1) (F tp))"

definition firstHolds1 :: "('stateO,'stateV)tuple34 \<Rightarrow> nat" where 
"firstHolds1 tp = firstNC (lmap (\<lambda>(trv1,sv1'',trv2,sv2'',statAA,statOO). trv1) (F tp))"

definition ltrv2 ::" ('stateO,'stateV)tuple34 \<Rightarrow> 'stateV llist" where 
"ltrv2 tp = lconcat (lmap (\<lambda>(trv1,sv1'',trv2,sv2'',statAA,statOO). llist_of trv2) (F tp))"

definition firstHolds2 :: "('stateO,'stateV)tuple34 \<Rightarrow> nat" where 
"firstHolds2 tp = firstNC (lmap (\<lambda>(trv1,sv1'',trv2,sv2'',statAA,statOO). trv2) (F tp))"

(* *)

lemma ltrv1_ne_imp: 
assumes "ltrv1 tp \<noteq> [[]]"
shows "\<exists>trv1 sv1'' trv2 sv2'' statAA statOO. (trv1,sv1'',trv2,sv2'',statAA,statOO) \<in> lset (F tp) \<and> 
              trv1 \<noteq> []"
using assms unfolding ltrv1_def unfolding lconcat_eq_LNil_iff by force
 
lemma ltrv2_ne_imp: 
assumes "ltrv2 tp \<noteq> [[]]"
shows "\<exists>trv1 sv1'' trv2 sv2'' statAA statOO. (trv1,sv1'',trv2,sv2'',statAA,statOO) \<in> lset (F tp) \<and> 
              trv2 \<noteq> []"
using assms unfolding ltrv2_def unfolding lconcat_eq_LNil_iff by force


(* *)

lemma ltrv1_LNil[simp]: 
"ltr1 = [[]] \<or> ltr2 = [[]] \<Longrightarrow> ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[]]"
unfolding ltrv1_def F_LNil by simp 
lemma ltrv2_LNil[simp]: 
"ltr1 = [[]] \<or> ltr2 = [[]] \<Longrightarrow> ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = [[]]"
unfolding ltrv2_def F_LNil by simp 

(* *)

lemma ltrv1_lnever: 
assumes "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]" "lnever isIntO ltr1" 
shows "ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = lltrv1 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)" 
unfolding ltrv1_def F_lnever[OF assms] lltrv1_def ..

lemma ltrv2_lnever: 
assumes "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]" "lnever isIntO ltr1" 
shows "ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = lltrv2 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)" 
unfolding ltrv2_def F_lnever[OF assms] lltrv2_def ..

(* *)

lemma H_T_not_lnever: 
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"
and l: "\<not> lnever isIntO ltr1" "Opt.lA ltr1 = Opt.lA ltr2"
shows "\<exists> w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO. 
  \<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' \<and> 
  \<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO \<and> 
  H_T (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
  ((trv1,sv1'',trv2,sv2'',statAA,statOO),
   (w1',w2', s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))"
proof-
  obtain tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' 
  where \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
  using isIntO_\<phi>\<phi>[OF ltr1 ltr2 l(2,1)] 
  by auto  

  define tp where 
  "tp = (SOME k. case k of (tr1,s1',s1'',ltr1',tr2,s2',s2'',ltr2') \<Rightarrow> 
         \<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2')"

  have 0: "case tp of (tr1,s1',s1'',ltr1',tr2,s2',s2'',ltr2') \<Rightarrow> 
         \<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
  using \<phi>\<phi> unfolding tp_def apply- apply(rule someI_ex)
  apply(rule exI[of _ "(tr1,s1',s1'',ltr1',tr2,s2',s2'',ltr2')"]) by auto

  obtain tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' where 
  tp: "tp = (tr1,s1',s1'',ltr1',tr2,s2',s2'',ltr2')" by(cases tp, auto)

  have \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
  using 0 unfolding tp by auto

  obtain w1' w2' trv1 sv1'' trv2 sv2'' statAA statOO
  where \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"   
  using unwindCond_ex_\<phi>'[OF unw \<Delta> r stat, of tr1 s1' s1'' tr2 s2' s2'']
  using \<phi>\<phi> unfolding \<phi>\<phi>_def by auto

  (* *)

  define tp' where 
  "tp' = (SOME k'. case k' of (w1',w2',trv1,sv1'',trv2,sv2'',statAA,statOO) \<Rightarrow> 
          \<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO)"
  
  have 1: "case tp' of (w1',w2',trv1,sv1'',trv2,sv2'',statAA,statOO) \<Rightarrow> 
         \<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
  using \<phi>' unfolding tp'_def apply- apply(rule someI_ex)
  apply(rule exI[of _ "(w1',w2',trv1,sv1'',trv2,sv2'',statAA,statOO)"]) by auto

  obtain w1' w2' trv1 sv1'' trv2 sv2'' statAA statOO where 
  tp': "tp' = (w1',w2',trv1,sv1'',trv2,sv2'',statAA,statOO)" by(cases tp', auto)

  have \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
  using 1 unfolding tp' by auto

  show ?thesis 
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ tr1]) apply(rule exI[of _ s1']) apply(rule exI[of _ s1'']) apply(rule exI[of _ ltr1'])
  apply(rule exI[of _ tr2]) apply(rule exI[of _ s2']) apply(rule exI[of _ s2'']) apply(rule exI[of _ ltr2'])
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2''])
  apply(rule exI[of _ statAA]) apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal using \<phi>\<phi> .
    subgoal using \<phi>' .
    subgoal unfolding H_T.simps 
    unfolding tp_def[symmetric] tp apply simp
    unfolding tp'_def[symmetric] tp' by simp .
qed
    
lemma ltrv1_ltrv2_not_lnever: 
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"
and l: "\<not> lnever isIntO ltr1" "Opt.lA ltr1 = Opt.lA ltr2"
shows "\<exists> w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO. 
  \<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' \<and> 
  \<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO \<and> 
  ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv1) (ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)) \<and> 
  ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) = 
    lappend (llist_of trv2) (ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))"
proof-
  have ltr1NE: "ltr1 \<noteq> [[]]" using l(1) by auto
  hence ltr2NE: "ltr2 \<noteq> [[]]" using l(2)  
    using Opt.lcompletedFrom_def ltr2(2) by blast
  show ?thesis
  using H_T_not_lnever[OF assms] apply(elim exE)
  subgoal for w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO
  apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
  apply(rule exI[of _ tr1]) apply(rule exI[of _ s1']) apply(rule exI[of _ s1'']) apply(rule exI[of _ ltr1'])
  apply(rule exI[of _ tr2]) apply(rule exI[of _ s2']) apply(rule exI[of _ s2'']) apply(rule exI[of _ ltr2'])
  apply(rule exI[of _ trv1]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ trv2]) apply(rule exI[of _ sv2''])
  apply(rule exI[of _ statAA]) apply(rule exI[of _ statOO])
  apply(intro conjI)
    subgoal by simp
    subgoal by simp
    subgoal unfolding ltrv1_def apply(subst F_not_lnever[OF ltr1NE ltr2NE l(1)])
    unfolding H_def T_def by simp
    subgoal unfolding ltrv2_def apply(subst F_not_lnever[OF ltr1NE ltr2NE l(1)])
    unfolding H_def T_def by simp . .
qed
  
(* *)

lemma lvalidFromS_ltrv1:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" 
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" 
and ltr14: "Opt.lA ltr1 = Opt.lA ltr2"
shows "Van.lvalidFromS sv1 (ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  {fix n1 sv1 ltrr1
   assume "\<exists>w1 w2 s1 ltr1 s2 ltr2 statA sv2 statO.  
       ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       n1 = w1 \<and>
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and>
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> 
       Opt.lA ltr1 = Opt.lA ltr2"
   hence "Van.llvalidFromS n1 sv1 ltrr1" 
   proof(coinduct rule: Van.llvalidFromS.coinduct[of "\<lambda>n1 sv1 ltrr1. 
    \<exists>w1 w2 s1 ltr1 s2 ltr2 statA sv2 statO.  
       ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       n1 = w1 \<and>
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and>
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> 
       Opt.lA ltr1 = Opt.lA ltr2"])
     case (llvalidFromS n1 sv1 ltrr1) 
     then obtain w1 w2 s1 ltr1 s2 ltr2 statA sv2 statO  
     where ltrr1: "ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and n1: "n1 = w1" 
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and stat: "statA = Diff \<longrightarrow> statO = Diff"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"  
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"  
     and A34: "Opt.lA ltr1 = Opt.lA ltr2"  
     by auto 

     have current: "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]"
     using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
     
     show ?case proof(cases "lnever isIntO ltr1")
       case True note current = current True
       hence "lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))
       note ln34 = True this
       have ltrr1: "ltrr1 = lltrv1 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr1 ltrv1_lnever[OF current] by simp 
       show ?thesis apply(rule Van.llvalidFromS_selectlvalidFromS)
       unfolding ltrr1 apply simp
       apply(rule lvalidFromS_lltrv1)
       using ln34 \<Delta> llvalidFromS ln34(2) ltr1(1) ltr1(2) ltr2(1) ltr2(2) r(1) r(2) r(4) unw by auto
     next
       case False note ln3 = False
       hence ln4: "\<not> lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))

       have "ltr1 \<noteq> [[s1]]" using ln3 ltr1  
       using Opt.final_not_isInt by auto
       hence "llength ltr1 > Suc 0" 
       by (metis Opt.lcompletedFrom_singl Suc_ile_eq current(1) enat_0_iff(1) 
       linorder_not_less llength_LNil llist_eq_cong ltr1(1) ltr1(2) nle_le not_less_zero)
       hence "\<not> finalO s1" 
       by (metis Opt.final_def Opt.lvalidFromS_Cons_iff current(1) eSuc_enat enat_0 
       linorder_neq_iff llength_LCons llength_LNil llist.exhaust_sel ltr1(1))
       hence nf12: "\<not> finalV sv1 \<and> \<not> finalV sv2" 
       using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by force     

       obtain w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO
       where \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
       and \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
       and ltrr1: "ltrr1 = 
          lappend (llist_of trv1) (ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))" 
       using ltrv1_ltrv2_not_lnever[OF unw \<Delta> r stat ltr1 ltr2 ln3 A34] 
       unfolding ltrr1 by blast
       define ltrr1' where ltrr1': "ltrr1' = ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr1: "ltrr1 = lappend (llist_of trv1) ltrr1'" 
       unfolding ltrr1 ltrr1' ..
       have ne: "trv1 \<noteq> [] \<or> (trv1 = [] \<and> w1' < w1)" 
       using \<phi>' unfolding \<phi>'_def ltrr1 by simp

       show ?thesis using ne proof(elim disjE conjE)
         assume trv1: "trv1 \<noteq> []"
         show ?thesis
         apply(rule Van.llvalidFromS_selectlappend)
         apply(rule exI[of _ sv1]) apply(rule exI[of _ trv1])
         apply(rule exI[of _ sv1'']) apply(rule exI[of _ "w1'"]) 
         apply(rule exI[of _ ltrr1']) apply(rule exI[of _ "w1"])           
         apply(intro conjI)
           subgoal unfolding n1 .. subgoal ..
           subgoal unfolding ltrr1 ..
           subgoal using \<phi>' unfolding \<phi>'_def 
           by (metis Van.validS_append1 Van.validFromS_def append_is_Nil_conv hd_append2)
           subgoal by fact
           subgoal using \<phi>' unfolding \<phi>'_def  
           by (metis Simple_Transition_System.validFromS_def Van.validS_validTrans append_is_Nil_conv list.sel(1) not_Cons_self2 trv1)
           subgoal apply(rule disjI1)
           apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
           apply(rule exI[of _ s1'']) apply(rule exI[of _ "s1'' $ ltr1'"])
           apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"])
           apply(rule exI[of _ statAA]) apply(rule exI[of _ sv2'']) apply(rule exI[of _ statOO]) 
           apply(intro conjI)
             subgoal unfolding ltrr1' ..
             subgoal ..
             subgoal using \<phi>' unfolding \<phi>'_def by auto
             subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
               by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
               by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(3) \<phi>' unfolding \<phi>'_def  
               by (metis Van.reach_validFromS_reach append_is_Nil_conv last_snoc trv1)
             subgoal using r(4) \<phi>' unfolding \<phi>'_def  
               by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
             subgoal using \<phi>' unfolding \<phi>'_def by auto
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp . .
       next
         assume trv1[simp]: "trv1 = []" and MM': "w1' < w1" 
         hence sv1''[simp]: "sv1'' = sv1" using \<phi>' unfolding \<phi>'_def by simp
         show ?thesis
         apply(rule Van.llvalidFromS_selectDelay)
         apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w1"]) 
         apply(rule exI[of _ sv1'']) apply(rule exI[of _ ltrr1'])           
         apply(intro conjI)
           subgoal unfolding n1 .. subgoal by simp
           subgoal unfolding ltrr1 by simp subgoal by fact
           subgoal apply(rule disjI1)
           apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
           apply(rule exI[of _ s1'']) apply(rule exI[of _ "s1'' $ ltr1'"])
           apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"])
           apply(rule exI[of _ statAA]) apply(rule exI[of _ sv2'']) apply(rule exI[of _ statOO]) 
           apply(intro conjI)
             subgoal unfolding ltrr1' ..
             subgoal ..
             subgoal using \<phi>' unfolding \<phi>'_def by auto
             subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
               by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
               by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal unfolding sv1'' by fact
             subgoal using r(4) \<phi>' unfolding \<phi>'_def  
               by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
             subgoal using \<phi>' unfolding \<phi>'_def by auto
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp . . 
       qed
     qed
   qed
  }
  thus ?thesis apply-apply(rule Van.llvalidFromS_imp_lvalidFromS)
  using assms by blast
qed

lemma lvalidFromS_ltrv2:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" 
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" 
and ltr14: "Opt.lA ltr1 = Opt.lA ltr2"
shows "Van.lvalidFromS sv2 (ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  {fix n2 sv2 ltrr2
   assume "\<exists>w1 w2 s1 ltr1 s2 ltr2 statA sv1 statO.  
       ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       n2 = w2 \<and>
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and>
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> 
       Opt.lA ltr1 = Opt.lA ltr2"
   hence "Van.llvalidFromS n2 sv2 ltrr2" 
   proof(coinduct rule: Van.llvalidFromS.coinduct[of "\<lambda>n2 sv2 ltrr2. 
    \<exists>w1 w2 s1 ltr1 s2 ltr2 statA sv1 statO.  
       ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       n2 = w2 \<and>
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and>
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> 
       Opt.lA ltr1 = Opt.lA ltr2"])
     case (llvalidFromS n2 sv2 ltrr2) 
     then obtain w1 w2 s1 ltr1 s2 ltr2 statA sv1 statO  
     where ltrr2: "ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and n2: "n2 = w2" 
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and stat: "statA = Diff \<longrightarrow> statO = Diff"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"  
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"  
     and A34: "Opt.lA ltr1 = Opt.lA ltr2"  
     by auto 

     have current: "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]"
     using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
     
     show ?case proof(cases "lnever isIntO ltr1")
       case True note current = current True
       hence "lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))
       note ln34 = True this
       have ltrr2: "ltrr2 = lltrv2 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr2 ltrv2_lnever[OF current] by simp 
       show ?thesis apply(rule Van.llvalidFromS_selectlvalidFromS)
       unfolding ltrr2 apply simp
       apply(rule lvalidFromS_lltrv2)
       using ln34 \<Delta> llvalidFromS ln34(2) ltr1(1) ltr1(2) ltr2(1) ltr2(2) r(1) r(2) r(3) unw by auto
     next
       case False note ln3 = False
       hence ln4: "\<not> lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))

       have "ltr2 \<noteq> [[s2]]" using ln4 ltr2 
       using Opt.final_not_isInt by auto
       hence "llength ltr2 > Suc 0"  
       by (metis Opt.lcompletedFrom_singl Suc_ile_eq current(2) enat_0_iff(2) 
        linorder_not_less llength_LNil llist_eq_cong ltr2(1) ltr2(2) nle_le not_iless0) 
       hence "\<not> finalO s2" 
       by (metis Opt.final_def Opt.lvalidFromS_Cons_iff current(2) eSuc_enat enat_0 
       linorder_neq_iff llength_LCons llength_LNil llist.exhaust_sel ltr2(1))
       hence nf12: "\<not> finalV sv1 \<and> \<not> finalV sv2" 
       using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by force     

       obtain w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO
       where \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
       and \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
       and ltrr2: "ltrr2 = 
          lappend (llist_of trv2) (ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))" 
       using ltrv1_ltrv2_not_lnever[OF unw \<Delta> r stat ltr1 ltr2 ln3 A34] 
       unfolding ltrr2 by blast
       define ltrr2' where ltrr2': "ltrr2' = ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr2: "ltrr2 = lappend (llist_of trv2) ltrr2'" 
       unfolding ltrr2 ltrr2' ..
       have ne: "trv2 \<noteq> [] \<or> (trv2 = [] \<and> w2' < w2)" 
       using \<phi>' unfolding \<phi>'_def ltrr2 by simp

       show ?thesis using ne proof(elim disjE conjE)
         assume trv2: "trv2 \<noteq> []"
         show ?thesis
         apply(rule Van.llvalidFromS_selectlappend)
         apply(rule exI[of _ sv2]) apply(rule exI[of _ trv2])
         apply(rule exI[of _ sv2'']) apply(rule exI[of _ "w2'"]) 
         apply(rule exI[of _ ltrr2']) apply(rule exI[of _ "w2"])           
         apply(intro conjI)
           subgoal unfolding n2 .. subgoal ..
           subgoal unfolding ltrr2 ..
           subgoal using \<phi>' unfolding \<phi>'_def 
           by (metis Van.validS_append1 Van.validFromS_def append_is_Nil_conv hd_append2)
           subgoal by fact
           subgoal using \<phi>' unfolding \<phi>'_def  
           by (metis Simple_Transition_System.validFromS_def Van.validS_validTrans append_is_Nil_conv list.distinct(1) list.sel(1) trv2)
           subgoal apply(rule disjI1)
           apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
           apply(rule exI[of _ s1'']) apply(rule exI[of _ "s1'' $ ltr1'"])
           apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"])
           apply(rule exI[of _ statAA]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ statOO]) 
           apply(intro conjI)
             subgoal unfolding ltrr2' ..
             subgoal ..
             subgoal using \<phi>' unfolding \<phi>'_def by auto
             subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
               by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
               by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(3) \<phi>' unfolding \<phi>'_def 
               by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
             subgoal using r(4) \<phi>' unfolding \<phi>'_def  
               by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
             subgoal using \<phi>' unfolding \<phi>'_def by auto
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp . .
       next
         assume trv2[simp]: "trv2 = []" and MM': "w2' < w2" 
         hence sv2''[simp]: "sv2'' = sv2" using \<phi>' unfolding \<phi>'_def by simp
         show ?thesis
         apply(rule Van.llvalidFromS_selectDelay)
         apply(rule exI[of _ "w2'"]) apply(rule exI[of _ "w2"]) 
         apply(rule exI[of _ sv2'']) apply(rule exI[of _ ltrr2'])           
         apply(intro conjI)
           subgoal unfolding n2 .. subgoal by simp
           subgoal unfolding ltrr2 by simp subgoal by fact
           subgoal apply(rule disjI1)
           apply(rule exI[of _ w1']) apply(rule exI[of _ w2']) 
           apply(rule exI[of _ s1'']) apply(rule exI[of _ "s1'' $ ltr1'"])
           apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"])
           apply(rule exI[of _ statAA]) apply(rule exI[of _ sv1'']) apply(rule exI[of _ statOO]) 
           apply(intro conjI)
             subgoal unfolding ltrr2' ..
             subgoal ..
             subgoal using \<phi>' unfolding \<phi>'_def by auto
             subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
               by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
               by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(3) \<phi>' unfolding \<phi>'_def  
               by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
             subgoal unfolding sv2'' by fact           
             subgoal using \<phi>' unfolding \<phi>'_def by auto
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp . . 
       qed
     qed
   qed
  }
  thus ?thesis apply-apply(rule Van.llvalidFromS_imp_lvalidFromS)
  using assms by blast
qed

(* *)

lemma lcompletedFrom_ltrv1:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" 
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" 
and A34: "Opt.lA ltr1 = Opt.lA ltr2"
shows "Van.lcompletedFrom sv1 (ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  {fix ltrr1 assume ltrr1: "ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
   and lfin: "lfinite ltrr1"
   hence "list_of ltrr1 \<noteq> [] \<and> finalV (last (list_of ltrr1))"
   using assms(2-) proof(induct "length (list_of ltrr1)" "w1" 
     arbitrary: w2 ltrr1 s1 ltr1 s2 ltr2 statA sv1 sv2 statO 
     rule: less2_induct')
     case (less w1 ltrr1 w2 s1 ltr1 s2 ltr2 statA sv1 sv2 statO)
     hence ltrr1: "ltrr1 = ltrv1 (w1,w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
     and lfin: "lfinite ltrr1" 
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and stat: "statA = Diff \<longrightarrow> statO = Diff"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "lcompletedFromO s1 ltr1" 
     and ltr2: "Opt.lvalidFromS s2 ltr2" "lcompletedFromO s2 ltr2" 
     and A34: "Opt.lA ltr1 = Opt.lA ltr2"
     by auto

     have current: "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]"
     using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
     
     show ?case proof(cases "lnever isIntO ltr1")
       case True note ln3 = True note current = current True
       hence ln4: "lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))
       note ln34 = True this
       have ltrr1: "ltrr1 = lltrv1 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr1 ltrv1_lnever[OF current] by simp 
       show ?thesis 
       using lcompletedFrom_lltrv1[OF unw \<Delta> r ltr1 ln3 ltr2 ln4, of L]
       using lfin[unfolded ltrr1] 
       unfolding Van.lcompletedFrom_def ltrr1[symmetric]         
       using llist_of_list_of by fastforce
     next
       case False note ln3 = False
       hence ln4: "\<not> lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))

       have "ltr1 \<noteq> [[s1]]" using ln3 ltr1  
       using Opt.final_not_isInt by auto
       hence "llength ltr1 > Suc 0" 
       by (metis Opt.lcompletedFrom_singl Suc_ile_eq current(1) enat_0_iff(1) 
       linorder_not_less llength_LNil llist_eq_cong ltr1(1) ltr1(2) nle_le not_less_zero)
       hence "\<not> finalO s1" 
       by (metis Opt.final_def Opt.lvalidFromS_Cons_iff current(1) eSuc_enat enat_0 
       linorder_neq_iff llength_LCons llength_LNil llist.exhaust_sel ltr1(1))
       hence nf12: "\<not> finalV sv1 \<and> \<not> finalV sv2" 
       using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by force     

       obtain w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO
       where \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
       and \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
       and ltrr1: "ltrr1 = 
          lappend (llist_of trv1) (ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))" 
       using ltrv1_ltrv2_not_lnever[OF unw \<Delta> r stat ltr1 ltr2 ln3 A34] 
       unfolding ltrr1 by blast
       define ltrr1' where ltrr1': "ltrr1' = ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr1: "ltrr1 = lappend (llist_of trv1) ltrr1'" 
       unfolding ltrr1 ltrr1' ..
       have ne: "trv1 \<noteq> [] \<or> (trv1 = [] \<and> w1' < w1)" 
       using \<phi>' unfolding \<phi>'_def ltrr1 by simp

       have lfin': "lfinite ltrr1'"
       using lfin ne unfolding ltrr1 by simp
       have len: "length (list_of ltrr1') < length (list_of ltrr1) \<or> 
                  length (list_of ltrr1') = length (list_of ltrr1) \<and> w1' < w1"
       using ne lfin lfin' by (simp add: list_of_lappend ltrr1)

       have 0: "list_of ltrr1' \<noteq> [] \<and> finalV (last (list_of ltrr1'))"  
       using len proof(elim disjE conjE)
         assume len: "length (list_of ltrr1') < length (list_of ltrr1)"
         show ?thesis 
         apply(rule less(1)[OF _ ltrr1'])
           subgoal by fact subgoal by fact              
           subgoal using \<phi>' unfolding \<phi>'_def by simp
           subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
           by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
           subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
           by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
           subgoal using r(3) \<phi>' unfolding \<phi>'_def 
           by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
           subgoal using r(4) \<phi>' unfolding \<phi>'_def  
           by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
           subgoal using \<phi>' unfolding \<phi>'_def by auto
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp . 
       next
         assume len: "length (list_of ltrr1') = length (list_of ltrr1)" "w1' < w1"
         show ?thesis   
         apply(rule less(2)[OF _ _ ltrr1'])
           subgoal by fact subgoal unfolding len ..
           subgoal by fact              
           subgoal using \<phi>' unfolding \<phi>'_def by simp
           subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
           by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
           subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
           by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
           subgoal using r(3) \<phi>' unfolding \<phi>'_def 
           by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
           subgoal using r(4) \<phi>' unfolding \<phi>'_def  
           by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
           subgoal using \<phi>' unfolding \<phi>'_def by auto
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp .
       qed
       show ?thesis unfolding ltrr1 using 0  
       by (simp add: lfin' list_of_lappend) 
     qed
   qed
  }
  thus ?thesis unfolding Van.lcompletedFrom_def by auto
qed

lemma lcompletedFrom_ltrv2:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" 
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" 
and A34: "Opt.lA ltr1 = Opt.lA ltr2"
shows "Van.lcompletedFrom sv2 (ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  {fix ltrr2 assume ltrr2: "ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
   and lfin: "lfinite ltrr2"
   hence "list_of ltrr2 \<noteq> [] \<and> finalV (last (list_of ltrr2))"
   using assms(2-) proof(induct "length (list_of ltrr2)" "w2" 
     arbitrary: w1 ltrr2 s1 ltr1 s2 ltr2 statA sv1 sv2 statO 
     rule: less2_induct')
     case (less w2 ltrr2 w1 s1 ltr1 s2 ltr2 statA sv1 sv2 statO)
     hence ltrr2: "ltrr2 = ltrv2 (w1,w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
     and lfin: "lfinite ltrr2" 
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and stat: "statA = Diff \<longrightarrow> statO = Diff"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "lcompletedFromO s1 ltr1" 
     and ltr2: "Opt.lvalidFromS s2 ltr2" "lcompletedFromO s2 ltr2" 
     and A34: "Opt.lA ltr1 = Opt.lA ltr2"
     by auto

     have current: "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]"
     using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
     
     show ?case proof(cases "lnever isIntO ltr1")
       case True note ln3 = True note current = current True
       hence ln4: "lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))
       note ln34 = True this
       have ltrr2: "ltrr2 = lltrv2 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr2 ltrv2_lnever[OF current] by simp 
       show ?thesis 
       using lcompletedFrom_lltrv2[OF unw \<Delta> r ltr1 ln3 ltr2 ln4, of L]
       using lfin[unfolded ltrr2] 
       unfolding Van.lcompletedFrom_def ltrr2[symmetric]         
       using llist_of_list_of by fastforce
     next
       case False note ln3 = False
       hence ln4: "\<not> lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))

       have "ltr2 \<noteq> [[s2]]" using ln4 ltr2  
       using Opt.final_not_isInt by auto
       hence "llength ltr2 > Suc 0" 
       by (metis Opt.lcompletedFrom_singl Suc_ile_eq current(2) enat_0_iff(2) 
       linorder_not_less llength_LNil llist_eq_cong ltr2(1) ltr2(2) nle_le not_less_zero)
       hence "\<not> finalO s2" 
       by (metis Opt.final_def Opt.lvalidFromS_Cons_iff current(2) eSuc_enat enat_0 
       linorder_neq_iff llength_LCons llength_LNil llist.exhaust_sel ltr2(1))
       hence nf12: "\<not> finalV sv1 \<and> \<not> finalV sv2" 
       using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by force     

       obtain w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO
       where \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
       and \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
       and ltrr2: "ltrr2 = 
          lappend (llist_of trv2) (ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))" 
       using ltrv1_ltrv2_not_lnever[OF unw \<Delta> r stat ltr1 ltr2 ln3 A34] 
       unfolding ltrr2 by blast
       define ltrr2' where ltrr2': "ltrr2' = ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr2: "ltrr2 = lappend (llist_of trv2) ltrr2'" 
       unfolding ltrr2 ltrr2' ..
       have ne: "trv2 \<noteq> [] \<or> (trv2 = [] \<and> w2' < w2)" 
       using \<phi>' unfolding \<phi>'_def ltrr2 by simp

       have lfin': "lfinite ltrr2'"
       using lfin ne unfolding ltrr2 by simp
       have len: "length (list_of ltrr2') < length (list_of ltrr2) \<or> 
                  length (list_of ltrr2') = length (list_of ltrr2) \<and> w2' < w2"
       using ne lfin lfin' by (simp add: list_of_lappend ltrr2)

       have 0: "list_of ltrr2' \<noteq> [] \<and> finalV (last (list_of ltrr2'))"  
       using len proof(elim disjE conjE)
         assume len: "length (list_of ltrr2') < length (list_of ltrr2)"
         show ?thesis 
         apply(rule less(1)[OF _ ltrr2'])
           subgoal by fact subgoal by fact              
           subgoal using \<phi>' unfolding \<phi>'_def by simp
           subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
           by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
           subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
           by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
           subgoal using r(3) \<phi>' unfolding \<phi>'_def 
           by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
           subgoal using r(4) \<phi>' unfolding \<phi>'_def  
           by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
           subgoal using \<phi>' unfolding \<phi>'_def by auto
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp . 
       next
         assume len: "length (list_of ltrr2') = length (list_of ltrr2)" "w2' < w2"
         show ?thesis   
         apply(rule less(2)[OF _ _ ltrr2'])
           subgoal by fact subgoal unfolding len ..
           subgoal by fact              
           subgoal using \<phi>' unfolding \<phi>'_def by simp
           subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
           by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
           subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
           by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
           subgoal using r(3) \<phi>' unfolding \<phi>'_def 
           by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
           subgoal using r(4) \<phi>' unfolding \<phi>'_def  
           by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast) 
           subgoal using \<phi>' unfolding \<phi>'_def by auto
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
           subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp .
       qed
       show ?thesis unfolding ltrr2 using 0  
       by (simp add: lfin' list_of_lappend) 
     qed
   qed
  }
  thus ?thesis unfolding Van.lcompletedFrom_def by auto
qed

(* *)

lemma lS_ltrv1_ltr1:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" 
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" 
and A34: "Opt.lA ltr1 = Opt.lA ltr2"
shows "Van.lS (ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)) = Opt.lS ltr1"
proof-
  have cltrv1: "Van.lcompletedFrom sv1 (ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_ltrv1[OF assms] .  
  {fix nL nR ltrr1 ltr1
   assume "\<exists>w1 w2 s1 s2 ltr2 statA sv1 sv2 statO.  
       nL = w1 \<and> nR = w1 \<and> 
       ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and>  
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1  \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and>
       Opt.lA ltr1 = Opt.lA ltr2"
   hence "TwoFuncPred.sameFM isSecV isSecO getSecV getSecO nL nR ltrr1 ltr1" 
   proof(coinduct rule: TwoFuncPred.sameFM.coinduct[of "\<lambda>nL nR ltrr1 ltr1. 
       \<exists> w1 w2 s1 s2 ltr2 statA sv1 sv2 statO.  
       nL = w1 \<and> nR = w1 \<and> 
       ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and>   
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> 
       Opt.lA ltr1 = Opt.lA ltr2"])
     case (2 nL nR ltrr1 ltr1) 
     then obtain w1 w2 s1 s2 ltr2 statA sv1 sv2 statO 
     where nL: "nL = w1" and nR: "nR = w1" 
     and ltrr1: "ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)" 
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and stat: "statA = Diff \<longrightarrow> statO = Diff"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"  
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"  
     and A34: "Opt.lA ltr1 = Opt.lA ltr2" 
     by auto
     
     have current: "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]"
     using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
     
     show ?case proof(cases "lnever isIntO ltr1")
       case True note ln3 = True note current = current True
       hence ln4: "lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))
       note ln34 = True this
       have ltrr1: "ltrr1 = lltrv1 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr1 ltrv1_lnever[OF current] by simp  

       have clltrv1: "Van.lcompletedFrom sv1 (lltrv1 (L,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
       using lcompletedFrom_lltrv1[OF unw \<Delta> r ltr1 ln3 ltr2 ln4] . 

       show ?thesis apply(rule TwoFuncPred.sameFM_selectlmap_lfilter)
       unfolding ltrr1 apply simp
       using lS_lltrv1_ltr1[OF unw \<Delta> r ltr1 ln3 ltr2 ln4, of L]
       unfolding Van.lS[OF clltrv1] Opt.lS[OF ltr1(2)] .
     next
       case False note ln3 = False
       hence ln4: "\<not> lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))

       have "ltr1 \<noteq> [[s1]]" using ln3 ltr1  
       using Opt.final_not_isInt by auto
       hence "llength ltr1 > Suc 0" 
       by (metis Opt.lcompletedFrom_singl Suc_ile_eq current(1) enat_0_iff(1) 
       linorder_not_less llength_LNil llist_eq_cong ltr1(1) ltr1(2) nle_le not_less_zero)
       hence "\<not> finalO s1" 
       by (metis Opt.final_def Opt.lvalidFromS_Cons_iff current(1) eSuc_enat enat_0 
       linorder_neq_iff llength_LCons llength_LNil llist.exhaust_sel ltr1(1))
       hence nf12: "\<not> finalV sv1 \<and> \<not> finalV sv2" 
       using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by force     

       obtain w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO
       where \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
       and \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
       and ltrr1: "ltrr1 = 
          lappend (llist_of trv1) (ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))"  
       using ltrv1_ltrv2_not_lnever[OF unw \<Delta> r stat ltr1 ltr2 ln3 A34] 
       unfolding ltrr1 by blast
       define ltrr1' where ltrr1': "ltrr1' = ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr1: "ltrr1 = lappend (llist_of trv1) ltrr1'" 
       unfolding ltrr1 ltrr1' ..
       have ne1: "trv1 \<noteq> [] \<or> w1' < w1" 
       using \<phi>' unfolding \<phi>'_def ltrr1 by simp 

       show ?thesis 
       apply(rule TwoFuncPred.sameFM_selectlappend)
       apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w1"]) 
       apply(rule exI[of _ "tr1 ## s1'"]) apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w1"]) 
       apply(rule exI[of _ "ltrr1'"])  apply(rule exI[of _ "s1'' $ ltr1'"])                    
       apply(intro conjI)
         subgoal unfolding nL ..  subgoal unfolding nR .. 
         subgoal using ltrr1 .
         subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
         subgoal by fact
         subgoal by simp 
         subgoal using \<phi>' unfolding \<phi>'_def unfolding Van.S.map_filter Opt.S.map_filter by simp
         subgoal apply(rule disjI1) 
           apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
           apply(rule exI[of _ s1'']) 
           apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"]) 
           apply(rule exI[of _ statAA])
           apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2''])
           apply(rule exI[of _ statOO])
           apply(intro conjI) 
             subgoal .. subgoal ..
             subgoal unfolding ltrr1' .. 
             subgoal using \<phi>' unfolding \<phi>'_def by simp
             subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
             by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
             by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(3) \<phi>' unfolding \<phi>'_def  
             by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
             subgoal using r(4) \<phi>' unfolding \<phi>'_def  
             by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
             subgoal using \<phi>' unfolding \<phi>'_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp . .        
     qed
   qed
  }
  thus ?thesis  apply-  
  unfolding Van.lS[OF cltrv1] Opt.lS[OF ltr1(2)] apply(rule TwoFuncPred.sameFM_lmap_lfilter)
  using assms by blast
qed

lemma lS_ltrv2_ltr2:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" 
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" 
and A34: "Opt.lA ltr1 = Opt.lA ltr2"
shows "Van.lS (ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)) = Opt.lS ltr2"
proof-
  have cltrv2: "Van.lcompletedFrom sv2 (ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_ltrv2[OF assms] .  
  {fix nL nR ltrr2 ltr2
   assume "\<exists>w1 w2 s1 s2 ltr1 statA sv1 sv2 statO.  
       nL = w2 \<and> nR = w2 \<and> 
       ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and>  
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1  \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and>
       Opt.lA ltr1 = Opt.lA ltr2"
   hence "TwoFuncPred.sameFM isSecV isSecO getSecV getSecO nL nR ltrr2 ltr2" 
   proof(coinduct rule: TwoFuncPred.sameFM.coinduct[of "\<lambda>nL nR ltrr2 ltr2. 
       \<exists> w1 w2 s1 s2 ltr1 statA sv1 sv2 statO.  
       nL = w2 \<and> nR = w2 \<and> 
       ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and>   
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> 
       Opt.lA ltr1 = Opt.lA ltr2"])
     case (2 nL nR ltrr2 ltr2) 
     then obtain w1 w2 s1 s2 ltr1 statA sv1 sv2 statO 
     where nL: "nL = w2" and nR: "nR = w2" 
     and ltrr2: "ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)" 
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and stat: "statA = Diff \<longrightarrow> statO = Diff"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"  
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"  
     and A34: "Opt.lA ltr1 = Opt.lA ltr2" 
     by auto
     
     have current: "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]"
     using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
     
     show ?case proof(cases "lnever isIntO ltr1")
       case True note ln3 = True note current = current True
       hence ln4: "lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))
       note ln34 = True this
       have ltrr2: "ltrr2 = lltrv2 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr2 ltrv2_lnever[OF current] by simp  

       have clltrv2: "Van.lcompletedFrom sv2 (lltrv2 (L,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
       using lcompletedFrom_lltrv2[OF unw \<Delta> r ltr1 ln3 ltr2 ln4] . 

       show ?thesis apply(rule TwoFuncPred.sameFM_selectlmap_lfilter)
       unfolding ltrr2 apply simp
       using lS_lltrv2_ltr2[OF unw \<Delta> r ltr1 ln3 ltr2 ln4, of L]
       unfolding Van.lS[OF clltrv2] Opt.lS[OF ltr2(2)] .
     next
       case False note ln3 = False
       hence ln4: "\<not> lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))

       have "ltr2 \<noteq> [[s2]]" using ln4 ltr2  
       using Opt.final_not_isInt by auto
       hence "llength ltr2 > Suc 0" 
       by (metis Opt.lcompletedFrom_singl Suc_ile_eq current(2) enat_0_iff(2) 
       linorder_not_less llength_LNil llist_eq_cong ltr2(1) ltr2(2) nle_le not_less_zero)
       hence "\<not> finalO s2" 
       by (metis Opt.final_def Opt.lvalidFromS_Cons_iff current(2) eSuc_enat enat_0 
       linorder_neq_iff llength_LCons llength_LNil llist.exhaust_sel ltr2(1))
       hence nf12: "\<not> finalV sv1 \<and> \<not> finalV sv2" 
       using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by force     

       obtain w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO
       where \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
       and \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
       and ltrr2: "ltrr2 = 
          lappend (llist_of trv2) (ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))"  
       using ltrv1_ltrv2_not_lnever[OF unw \<Delta> r stat ltr1 ltr2 ln3 A34] 
       unfolding ltrr2 by blast
       define ltrr2' where ltrr2': "ltrr2' = ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr1: "ltrr2 = lappend (llist_of trv2) ltrr2'" 
       unfolding ltrr2 ltrr2' ..
       have ne2: "trv2 \<noteq> [] \<or> w2' < w2" 
       using \<phi>' unfolding \<phi>'_def ltrr2 by simp 

       show ?thesis 
       apply(rule TwoFuncPred.sameFM_selectlappend)
       apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "w2'"]) apply(rule exI[of _ "w2"]) 
       apply(rule exI[of _ "tr2 ## s2'"]) apply(rule exI[of _ "w2'"]) apply(rule exI[of _ "w2"]) 
       apply(rule exI[of _ "ltrr2'"])  apply(rule exI[of _ "s2'' $ ltr2'"])                    
       apply(intro conjI)
         subgoal unfolding nL ..  subgoal unfolding nR .. 
         subgoal using ltrr1 .
         subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
         subgoal by fact
         subgoal by simp 
         subgoal using \<phi>' unfolding \<phi>'_def unfolding Van.S.map_filter Opt.S.map_filter by simp
         subgoal apply(rule disjI1) 
           apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
           apply(rule exI[of _ s1'']) 
           apply(rule exI[of _ s2'']) apply(rule exI[of _ "s1'' $ ltr1'"]) 
           apply(rule exI[of _ statAA])
           apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2''])
           apply(rule exI[of _ statOO])
           apply(intro conjI) 
             subgoal .. subgoal ..
             subgoal unfolding ltrr2' .. 
             subgoal using \<phi>' unfolding \<phi>'_def by simp
             subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
             by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
             by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(3) \<phi>' unfolding \<phi>'_def  
             by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
             subgoal using r(4) \<phi>' unfolding \<phi>'_def  
             by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
             subgoal using \<phi>' unfolding \<phi>'_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp . .        
     qed
   qed
  }
  thus ?thesis  apply-  
  unfolding Van.lS[OF cltrv2] Opt.lS[OF ltr2(2)] apply(rule TwoFuncPred.sameFM_lmap_lfilter)
  using assms by blast
qed

(* *)

lemma lA_ltrv1_ltrv2:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" 
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" 
and A34: "Opt.lA ltr1 = Opt.lA ltr2"
shows "Van.lA (ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)) = 
       Van.lA (ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
proof-
  have cltrv1: "Van.lcompletedFrom sv1 (ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_ltrv1[OF assms] .
  have cltrv2: "Van.lcompletedFrom sv2 (ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_ltrv2[OF assms] . 
  {fix nL nR ltrr1 ltrr2
   assume "\<exists>w1 w2 s1 ltr1 s2 ltr2 statA sv1 sv2 statO.  
       nL = w1 \<and> nR = w2 \<and> 
       ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1  \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and>
       Opt.lA ltr1 = Opt.lA ltr2"
   hence "TwoFuncPred.sameFM isIntV isIntV getActV getActV nL nR ltrr1 ltrr2" 
   proof(coinduct rule: TwoFuncPred.sameFM.coinduct[of "\<lambda>nL nR ltrr1 ltrr2. 
       \<exists> w1 w2 s1 ltr1 s2 ltr2 statA sv1 sv2 statO.  
       nL = w1 \<and> nR = w2 \<and> 
       ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> 
       Opt.lA ltr1 = Opt.lA ltr2"])
     case (2 nL nR ltrr1 ltrr2) 
     then obtain w1 w2 s1 ltr1 s2 ltr2 statA sv1 sv2 statO 
     where nL: "nL = w1" and nR: "nR = w2" 
     and ltrr1: "ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and ltrr2: "ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and stat: "statA = Diff \<longrightarrow> statO = Diff"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"  
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"  
     and A34: "Opt.lA ltr1 = Opt.lA ltr2" 
     by auto
     
     have current: "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]"
     using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
     
     show ?case proof(cases "lnever isIntO ltr1")
       case True note ln3 = True note current = current True
       hence ln4: "lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))
       note ln34 = True this
       have ltrr1: "ltrr1 = lltrv1 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr1 ltrv1_lnever[OF current] by simp 
       have ltrr2: "ltrr2 = lltrv2 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr2 ltrv2_lnever[OF current] by simp 

       have clltrv1: "Van.lcompletedFrom sv1 (lltrv1 (L,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
       using lcompletedFrom_lltrv1[OF unw \<Delta> r ltr1 ln3 ltr2 ln4] .
       have clltrv2: "Van.lcompletedFrom sv2 (lltrv2 (L,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
       using lcompletedFrom_lltrv2[OF unw \<Delta> r ltr1 ln3 ltr2 ln4] . 

       show ?thesis apply(rule TwoFuncPred.sameFM_selectlmap_lfilter)
       unfolding ltrr1 ltrr2 apply simp
       using lA_lltrv1_lltrv2[OF unw \<Delta> r ltr1 ln3 ltr2 ln4, of L]
       unfolding Van.lA[OF clltrv1] Van.lA[OF clltrv2] .
     next
       case False note ln3 = False
       hence ln4: "\<not> lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))

       have "ltr1 \<noteq> [[s1]]" using ln3 ltr1  
       using Opt.final_not_isInt by auto
       hence "llength ltr1 > Suc 0" 
       by (metis Opt.lcompletedFrom_singl Suc_ile_eq current(1) enat_0_iff(1) 
       linorder_not_less llength_LNil llist_eq_cong ltr1(1) ltr1(2) nle_le not_less_zero)
       hence "\<not> finalO s1" 
       by (metis Opt.final_def Opt.lvalidFromS_Cons_iff current(1) eSuc_enat enat_0 
       linorder_neq_iff llength_LCons llength_LNil llist.exhaust_sel ltr1(1))
       hence nf12: "\<not> finalV sv1 \<and> \<not> finalV sv2" 
       using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by force     

       obtain w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO
       where \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
       and \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
       and ltrr1: "ltrr1 = 
          lappend (llist_of trv1) (ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))" 
       and ltrr2: "ltrr2 = 
          lappend (llist_of trv2) (ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))" 
       using ltrv1_ltrv2_not_lnever[OF unw \<Delta> r stat ltr1 ltr2 ln3 A34] 
       unfolding ltrr1 ltrr2 by blast
       define ltrr1' where ltrr1': "ltrr1' = ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr1: "ltrr1 = lappend (llist_of trv1) ltrr1'" 
       unfolding ltrr1 ltrr1' ..
       have ne1: "trv1 \<noteq> [] \<or> w1' < w1" 
       using \<phi>' unfolding \<phi>'_def ltrr1 by simp
       define ltrr2' where ltrr2': "ltrr2' = ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr2: "ltrr2 = lappend (llist_of trv2) ltrr2'" 
       unfolding ltrr2 ltrr2' ..
       have ne2: "trv2 \<noteq> [] \<or> w2' < w2" 
       using \<phi>' unfolding \<phi>'_def ltrr1 by simp

       show ?thesis 
       apply(rule TwoFuncPred.sameFM_selectlappend)
       apply(rule exI[of _ "trv1"]) apply(rule exI[of _ "w1'"]) apply(rule exI[of _ "w1"]) 
       apply(rule exI[of _ "trv2"]) apply(rule exI[of _ "w2'"]) apply(rule exI[of _ "w2"]) 
       apply(rule exI[of _ "ltrr1'"])  apply(rule exI[of _ "ltrr2'"])                    
       apply(intro conjI)
         subgoal unfolding nL ..  subgoal unfolding nR .. 
         subgoal using ltrr1 .
         subgoal using ltrr2 .
         subgoal by fact  subgoal by fact
         subgoal using \<phi>' unfolding \<phi>'_def unfolding Van.A.map_filter by simp
         subgoal apply(rule disjI1) 
           apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
           apply(rule exI[of _ s1'']) apply(rule exI[of _ "s1'' $ ltr1'"]) 
           apply(rule exI[of _ s2'']) apply(rule exI[of _ "s2'' $ ltr2'"]) 
           apply(rule exI[of _ statAA])
           apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2''])
           apply(rule exI[of _ statOO])
           apply(intro conjI) 
             subgoal .. subgoal ..
             subgoal unfolding ltrr1' ..
             subgoal unfolding ltrr2' .. 
             subgoal using \<phi>' unfolding \<phi>'_def by simp
             subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
             by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
             by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(3) \<phi>' unfolding \<phi>'_def  
             by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
             subgoal using r(4) \<phi>' unfolding \<phi>'_def  
             by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
             subgoal using \<phi>' unfolding \<phi>'_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp . .        
     qed
   qed
  }
  thus ?thesis  apply-  
  unfolding Van.lA[OF cltrv1] Van.lA[OF cltrv2] apply(rule TwoFuncPred.sameFM_lmap_lfilter)
  using assms by blast
qed

(* *)

lemma lO_ltrv1_ltrv2:  
assumes unw: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
and stat: "statA = Diff \<longrightarrow> statO = Diff"
and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1" 
and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2" 
and A34: "Opt.lA ltr1 = Opt.lA ltr2" 
and O12: "Van.lO (ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)) = 
          Van.lO (ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
and stO: "statO = Eq"
shows "Opt.lO ltr1 = Opt.lO ltr2"
proof-
  have cltrv1: "Van.lcompletedFrom sv1 (ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_ltrv1[OF assms(1-12)] .
  have cltrv2: "Van.lcompletedFrom sv2 (ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
  using lcompletedFrom_ltrv2[OF assms(1-12)] . 
  {fix nL nR ltr1 ltr2 
   assume "\<exists>ltrr1 ltrr2 w1 w2 s1 s2 statA sv1 sv2 statO.  
       ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1  \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and>
       Opt.lA ltr1 = Opt.lA ltr2 \<and> 
       Van.lO ltrr1 = Van.lO ltrr2 \<and> 
       statO = Eq"
   hence "TwoFuncPred.sameFM isIntO isIntO getObsO getObsO nL nR ltr1 ltr2" 
   proof(coinduct rule: TwoFuncPred.sameFM.coinduct[of "\<lambda>nL nR ltr1 ltr2. 
       \<exists> ltrr1 ltrr2 w1 w2 s1 s2 statA sv1 sv2 statO.   
       ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO) \<and> 
       \<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO \<and> 
       reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
       (statA = Diff \<longrightarrow> statO = Diff) \<and> 
       Opt.lvalidFromS s1 ltr1 \<and> Opt.lcompletedFrom s1 ltr1 \<and> 
       Opt.lvalidFromS s2 ltr2 \<and> Opt.lcompletedFrom s2 ltr2 \<and> 
       Opt.lA ltr1 = Opt.lA ltr2 \<and> 
       Van.lO ltrr1 = Van.lO ltrr2 \<and> 
       statO = Eq"])
     case (2 nL nR ltr1 ltr2)  
     then obtain ltrr1 ltrr2 w1 w2 s1 s2 statA sv1 sv2 statO where 
         ltrr11: "ltrr1 = ltrv1 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and ltrr22: "ltrr2 = ltrv2 (w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO)"
     and \<Delta>: "\<Delta> \<infinity> w1 w2 s1 s2 statA sv1 sv2 statO"
     and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
     and stat: "statA = Diff \<longrightarrow> statO = Diff"
     and ltr1: "Opt.lvalidFromS s1 ltr1" "Opt.lcompletedFrom s1 ltr1"  
     and ltr2: "Opt.lvalidFromS s2 ltr2" "Opt.lcompletedFrom s2 ltr2"  
     and A34: "Opt.lA ltr1 = Opt.lA ltr2" 
     and O12: "Van.lO ltrr1 = Van.lO ltrr2" 
     and stO: "statO = Eq"
     by auto

     have stA: "statA = Eq" using stat stO  
     using status.exhaust by blast
     
     have current: "ltr1 \<noteq> [[]]" "ltr2 \<noteq> [[]]"
     using ltr1(2) ltr2(2) unfolding Opt.lcompletedFrom_def by auto
     
     show ?case proof(cases "lnever isIntO ltr1")
       case True note ln3 = True note current = current True
       hence ln4: "lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))
       note ln34 = True this
       have ltrr1: "ltrr1 = lltrv1 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr11 ltrv1_lnever[OF current] by simp 
       have ltrr2: "ltrr2 = lltrv2 (L, w1, w2, s1, ltr1, s2, ltr2, statA, sv1, sv2, statO)"
       unfolding ltrr22 ltrv2_lnever[OF current] by simp 
 
       have clltrv1: "Van.lcompletedFrom sv1 (lltrv1 (L,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
       using lcompletedFrom_lltrv1[OF unw \<Delta> r ltr1 ln3 ltr2 ln4] .
       have clltrv2: "Van.lcompletedFrom sv2 (lltrv2 (L,w1,w2,s1,ltr1,s2,ltr2,statA,sv1,sv2,statO))"
       using lcompletedFrom_lltrv2[OF unw \<Delta> r ltr1 ln3 ltr2 ln4] . 

       show ?thesis apply(rule TwoFuncPred.sameFM_selectlmap_lfilter) 
       unfolding Opt.lO[OF ltr1(2)] Opt.lO[OF ltr2(2)]  
       by (metis ln3 ln4 lnever_LNil_lfilter')

     next
       case False note ln3 = False
       hence ln4: "\<not> lnever isIntO ltr2" 
       by (metis Opt.lA lfiltermap_LNil_never lfiltermap_lmap_lfilter ltr1(2) A34 ltr2(2))

       have "ltr1 \<noteq> [[s1]]" using ln3 ltr1  
       using Opt.final_not_isInt by auto
       hence "llength ltr1 > Suc 0" 
       by (metis Opt.lcompletedFrom_singl Suc_ile_eq current(1) enat_0_iff(1) 
       linorder_not_less llength_LNil llist_eq_cong ltr1(1) ltr1(2) nle_le not_less_zero)
       hence "\<not> finalO s1" 
       by (metis Opt.final_def Opt.lvalidFromS_Cons_iff current(1) eSuc_enat enat_0 
       linorder_neq_iff llength_LCons llength_LNil llist.exhaust_sel ltr1(1))
       hence nf12: "\<not> finalV sv1 \<and> \<not> finalV sv2" 
       using \<Delta> r(1) r(2) r(3) r(4) unw unwindCond_def by force     

       obtain w1' w2' tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2' trv1 sv1'' trv2 sv2'' statAA statOO
       where \<phi>\<phi>: "\<phi>\<phi> s1 ltr1 s2 ltr2 tr1 s1' s1'' ltr1' tr2 s2' s2'' ltr2'"
       and \<phi>': "\<phi>' \<Delta> w1 w2 w1' w2' statA s1 tr1 s1' s1'' s2 tr2 s2' s2'' statAA statO sv1 trv1 sv1'' sv2 trv2 sv2'' statOO"
       and ltrr1: "ltrr1 = 
          lappend (llist_of trv1) (ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))" 
       and ltrr2: "ltrr2 = 
          lappend (llist_of trv2) (ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO))" 
       using ltrv1_ltrv2_not_lnever[OF unw \<Delta> r stat ltr1 ltr2 ln3 A34] 
       unfolding ltrr11 ltrr22 by blast
       define ltrr1' where ltrr1': "ltrr1' = ltrv1 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr1: "ltrr1 = lappend (llist_of trv1) ltrr1'" 
       unfolding ltrr1 ltrr1' ..
       have ne1: "trv1 \<noteq> [] \<or> w1' < w1" 
       using \<phi>' unfolding \<phi>'_def ltrr1 by simp
       define ltrr2' where ltrr2': "ltrr2' = ltrv2 (w1',w2',s1'',s1'' $ ltr1',s2'',s2'' $ ltr2',statAA,sv1'',sv2'',statOO)"
       have ltrr2: "ltrr2 = lappend (llist_of trv2) ltrr2'" 
       unfolding ltrr2 ltrr2' ..
       have ne2: "trv2 \<noteq> [] \<or> w2' < w2" 
       using \<phi>' unfolding \<phi>'_def ltrr1 by simp

       have ltr1_eq: "ltr1 = lappend (llist_of (tr1 ## s1')) (s1'' $ ltr1')" 
        and ltr2_eq: "ltr2 = lappend (llist_of (tr2 ## s2')) (s2'' $ ltr2')" using \<phi>\<phi> unfolding \<phi>\<phi>_def by auto

       have sst: "statOO = Diff \<longleftrightarrow> Van.O (trv1 ## sv1'') \<noteq> Van.O (trv2 ## sv2'')"
       "statA = Eq \<Longrightarrow> statAA = Diff \<longleftrightarrow> Opt.O ((tr1 ## s1') ## s1'') \<noteq> Opt.O ((tr2 ## s2') ## s2'')"
       "statO = Diff \<Longrightarrow> statOO = Diff" 
       "statAA = Diff \<Longrightarrow> statOO = Diff"
        using \<phi>' stO unfolding \<phi>'_def by auto

       have Atrv12': "Van.A (trv1 ## sv1'') = Van.A (trv2 ## sv2'')"
       using \<phi>' unfolding \<phi>'_def by auto

       have \<Delta>': "\<Delta> \<infinity> w1' w2' s1'' s2'' statAA sv1'' sv2'' statOO" 
       using \<phi>' unfolding \<phi>'_def by auto
       
       have vltrv1: "Van.lvalidFromS sv1 ltrr1" 
       unfolding ltrr11 using lvalidFromS_ltrv1  
       using A34 \<Delta> ltr1(1) ltr1(2) ltr2(1) ltr2(2) r(1) r(2) r(3) r(4) stat unw by blast
       have cltrv1: "Van.lcompletedFrom sv1 ltrr1" 
       unfolding ltrr11 using lcompletedFrom_ltrv1  
       using A34 \<Delta> ltr1(1) ltr1(2) ltr2(1) ltr2(2) r(1) r(2) r(3) r(4) stat unw by blast

       have vltrv2: "Van.lvalidFromS sv2 ltrr2" 
       unfolding ltrr22 using lvalidFromS_ltrv2  
       using A34 \<Delta> ltr1(1) ltr1(2) ltr2(1) ltr2(2) r(1) r(2) r(3) r(4) stat unw by blast
       have cltrv2: "Van.lcompletedFrom sv2 ltrr2" 
       unfolding ltrr22 using lcompletedFrom_ltrv2  
       using A34 \<Delta> ltr1(1) ltr1(2) ltr2(1) ltr2(2) r(1) r(2) r(3) r(4) stat unw by blast 

       have Oltrr1: "Van.lO ltrr1 = lmap getObsV (lfilter isIntV ltrr1)"
       using Van.lO[OF cltrv1] .
       have Oltrr2: "Van.lO ltrr2 = lmap getObsV (lfilter isIntV ltrr2)"
       using Van.lO[OF cltrv2] .
       
       have cltrv1': "Van.lcompletedFrom (lastt sv1 trv1) ltrr1'" 
       using cltrv1 unfolding ltrr1 Van.lcompletedFrom_def Van.final_def apply simp
       using \<phi>' unfolding \<phi>'_def  
       by (metis Van.validS_validTrans Van.validFromS_def lappend_LNil2 last_appendR lfinite_llist_of list_of_lappend 
       list_of_llist_of llist_of.simps(1) snoc_eq_iff_butlast)

       have cltrv2': "Van.lcompletedFrom (lastt sv2 trv2) ltrr2'" 
       using cltrv2 unfolding ltrr2 Van.lcompletedFrom_def Van.final_def apply simp
       using \<phi>' unfolding \<phi>'_def  
       by (metis Van.validS_validTrans Van.validFromS_def lappend_LNil2 last_appendR lfinite_llist_of list_of_lappend 
       list_of_llist_of llist_of.simps(1) snoc_eq_iff_butlast)

       have Oltrr1': "Van.lO ltrr1' = lmap getObsV (lfilter isIntV ltrr1')"
       using Van.lO[OF cltrv1'] .
       have Oltrr2': "Van.lO ltrr2' = lmap getObsV (lfilter isIntV ltrr2')"
       using Van.lO[OF cltrv2'] .

       have "Van.O (trv1 ## sv1'') = Van.O (trv2 ## sv2'') \<and> 
         Van.lO ltrr1' = Van.lO ltrr2'"
       using Atrv12' O12 Oltrr1' Oltrr2' unfolding Oltrr1 Oltrr2 unfolding ltrr1 ltrr2
       unfolding Van.A.map_filter Van.O.map_filter Van.lO.lmap_lfilter apply simp 
       unfolding lmap_lappend_distrib apply simp apply(subst (asm) lappend_llist_of_inj)  
       using map_eq_imp_length_eq by auto
       hence O12'': "Van.O (trv1 ## sv1'') = Van.O (trv2 ## sv2'')"
       and O12': "Van.lO ltrr1' = Van.lO ltrr2'" by auto

       have stOO: "statOO = Eq" using O12'' sst by(cases statOO, auto)

       have O34': "Opt.O ((tr1 ## s1') ## s1'') = Opt.O ((tr2 ## s2') ## s2'')"
       using stOO sst(2) sst(4) stA by blast

       hence s14': "getObsO s1' = getObsO s2'"
       using \<phi>\<phi> unfolding \<phi>\<phi>_def Opt.O.map_filter by (simp add: never_Nil_filter)
       
       show ?thesis
       apply(rule TwoFuncPred.sameFM_selectlappend)
       apply(rule exI[of _ "tr1 ## s1'"]) apply(rule exI[of _ undefined]) apply(rule exI[of _ nL]) 
       apply(rule exI[of _ "tr2 ## s2'"]) apply(rule exI[of _ undefined]) apply(rule exI[of _ nR]) 
       apply(rule exI[of _ "s1'' $ ltr1'"])  apply(rule exI[of _ "s2'' $ ltr2'"])                    
       apply(intro conjI)
         subgoal ..  subgoal .. 
         subgoal by fact subgoal by fact
         subgoal by simp  subgoal by simp
         subgoal using \<phi>\<phi> unfolding \<phi>\<phi>_def unfolding Opt.O.map_filter 
         by (simp add: s14' never_Nil_filter)  
         subgoal apply(rule disjI1) 
           apply(rule exI[of _ ltrr1']) apply(rule exI[of _ ltrr2'])
           apply(rule exI[of _ w1']) apply(rule exI[of _ w2'])
           apply(rule exI[of _ s1'']) apply(rule exI[of _ s2'']) 
           apply(rule exI[of _ statAA])
           apply(rule exI[of _ sv1'']) apply(rule exI[of _ sv2''])
           apply(rule exI[of _ statOO])
           apply(intro conjI) 
             subgoal unfolding ltrr1' ..
             subgoal unfolding ltrr2' ..  
             subgoal using \<phi>' unfolding \<phi>'_def by simp
             subgoal using r(1) \<phi>\<phi> unfolding \<phi>\<phi>_def 
             by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def 
             by (metis Opt.reach_validFromS_reach append_is_Nil_conv last_snoc not_Cons_self2)
             subgoal using r(3) \<phi>' unfolding \<phi>'_def  
             by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
             subgoal using r(4) \<phi>' unfolding \<phi>'_def  
             by (metis Van.reach_validFromS_reach snoc_eq_iff_butlast)
             subgoal using \<phi>' unfolding \<phi>'_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp
             subgoal using r(2) \<phi>\<phi> unfolding \<phi>\<phi>_def by simp 
             subgoal by fact
             subgoal by fact . .
     qed
   qed
  }
  thus ?thesis  
  unfolding Opt.lO[OF ltr1(2)] Opt.lO[OF ltr2(2)] apply(rule TwoFuncPred.sameFM_lmap_lfilter[where wL = undefined and wR = undefined])
  using assms by blast
qed

end (* context *)


(* Relative security from unwinding (for possibly) infinite traces: ) *)

theorem unwind_lrsecure: 
assumes init: "initCond \<Delta>" and unwind: "unwindCond \<Delta>"
shows lrsecure
unfolding lrsecure_def2 proof clarify
  fix s1 tr1 s2 tr2
  assume 3: "istateO s1" "Opt.lvalidFromS s1 tr1" "lcompletedFromO s1 tr1"
  and 4: "istateO s2" "Opt.lvalidFromS s2 tr2" "lcompletedFromO s2 tr2" 
  and A34: "Opt.lA tr1 = Opt.lA tr2" and O34: "Opt.lO tr1 \<noteq> Opt.lO tr2" 
  obtain sv1 sv2 where 
  isv12: "istateV sv1" "istateV sv2" and c12: "corrState sv1 s1" "corrState sv2 s2"
  and \<Delta>: "\<Delta> \<infinity> \<infinity> \<infinity> s1 s2 Eq sv1 sv2 Eq" 
  using init 3 4  unfolding initCond_def by blast
  have r: "reachV sv1" "reachV sv2" "reachO s1" "reachO s2"
  by (auto simp: Van.Istate isv12 Opt.Istate 3 4)
  note all = 3 4 A34 isv12 \<Delta> unwind r
  show "\<exists>sv1 trv1 sv2 trv2.
    istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 \<and>
    Van.lvalidFromS sv1 trv1 \<and> lcompletedFromV sv1 trv1 \<and> Van.lvalidFromS sv2 trv2 \<and>
    lcompletedFromV sv2 trv2 \<and> Van.lS trv1 = Opt.lS tr1 \<and> Van.lS trv2 = Opt.lS tr2 \<and> 
    Van.lA trv1 = Van.lA trv2 \<and> Van.lO trv1 \<noteq> Van.lO trv2"
  apply(rule exI[of _ sv1])  
  apply(rule exI[of _ "ltrv1 \<Delta> (\<infinity>, \<infinity>, s1, tr1, s2, tr2, Eq, sv1, sv2, Eq)"])
  apply(rule exI[of _ sv2])  
  apply(rule exI[of _ "ltrv2 \<Delta> (\<infinity>, \<infinity>, s1, tr1, s2, tr2, Eq, sv1, sv2, Eq)"])
  apply(intro conjI)
    subgoal by fact subgoal by fact subgoal by fact subgoal by fact
    subgoal apply(rule lvalidFromS_ltrv1) using all by auto
    subgoal apply(rule lcompletedFrom_ltrv1) using all by auto 
    subgoal apply(rule lvalidFromS_ltrv2) using all by auto
    subgoal apply(rule lcompletedFrom_ltrv2) using all by auto
    subgoal apply(rule lS_ltrv1_ltr1) using all by auto 
    subgoal apply(rule lS_ltrv2_ltr2) using all by auto 
    subgoal apply(rule lA_ltrv1_ltrv2) using all by auto 
    subgoal using O34 apply- apply(erule contrapos_nn)
    apply(rule lO_ltrv1_ltrv2) using all by auto .
qed


subsection \<open> Compositional unwinding \<close>

text \<open> We allow networks of unwinding relations that unwind into each other, 
which offer a compositional alternative to monolithic unwinding. \<close>


definition unwindIntoCond :: 
"(enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'stateO \<Rightarrow> 'stateO \<Rightarrow> status \<Rightarrow> 'stateV \<Rightarrow> 'stateV \<Rightarrow> status \<Rightarrow> bool) \<Rightarrow>  
 (enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> 'stateO \<Rightarrow> 'stateO \<Rightarrow> status \<Rightarrow> 'stateV \<Rightarrow> 'stateV \<Rightarrow> status \<Rightarrow> bool)
 \<Rightarrow> bool" 
where 
"unwindIntoCond \<Delta> \<Delta>' \<equiv> \<forall>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<longrightarrow> 
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2) 
 \<and> 
 (statA = Eq \<longrightarrow> (isIntO s1 \<longleftrightarrow> isIntO s2))
 \<and>
 ((\<exists>v<w. proact \<Delta>' v w1 w2 s1 s2 statA sv1 sv2 statO)   
  \<or> 
  react \<Delta>' w1 w2 s1 s2 statA sv1 sv2 statO)"

theorem distrib_unwind_lrsecure:
assumes m: "0 < m" and nxt: "\<And>i. i < (m::nat) \<Longrightarrow> nxt i \<subseteq> {0..<m}" 
and init: "initCond (\<Delta>s 0)" 
and step: "\<And>i. i < m \<Longrightarrow> 
  unwindIntoCond (\<Delta>s i) (\<lambda>w w1 w2 s1 s2 statA sv1 sv2 statO. 
     \<exists>j \<in> nxt i. \<Delta>s j w w1 w2 s1 s2 statA sv1 sv2 statO)"
shows lrsecure
proof-
  define \<Delta> where D: "\<Delta> \<equiv> \<lambda>w w1 w2 s1 s2 statA sv1 sv2 statO. \<exists>i < m. \<Delta>s i w w1 w2 s1 s2 statA sv1 sv2 statO"
  have i: "initCond \<Delta>" using init m unfolding initCond_def D by meson
  have c: "unwindCond \<Delta>" unfolding unwindCond_def apply(intro allI impI allI)
  apply(subst (asm) D) apply (elim exE conjE)
    subgoal for w w1 w2 s1 s2 statA sv1 sv2 statO i 
      apply(frule step) unfolding unwindIntoCond_def
      apply(erule allE[of _ w]) apply(erule allE[of _ w1]) apply(erule allE[of _ w2])
      apply(erule allE[of _ s1]) apply(erule allE[of _ s2]) apply(erule allE[of _ statA])
      apply(erule allE[of _ sv1]) apply(erule allE[of _ sv2]) apply(erule allE[of _ statO])
      apply simp apply(elim conjE) 
      apply(erule disjE)
        subgoal apply(rule disjI1)
        subgoal apply(elim exE conjE) subgoal for v
        apply(rule exI[of _ v], simp) 
        apply(rule proact_mono[of "\<lambda>w w1 w2 s1 s2 statA sv1 sv2 statO. \<exists>j\<in>nxt i. \<Delta>s j w w1 w2 s1 s2 statA sv1 sv2 statO"])
          subgoal unfolding le_fun_def D by simp (meson atLeastLessThan_iff nxt subsetD)
          subgoal . . . .
        subgoal apply(rule disjI2)
        apply(rule match_mono[of "\<lambda>w w1 w2 s1 s2 statA sv1 sv2 statO. \<exists>j\<in>nxt i. \<Delta>s j w w1 w2 s1 s2 statA sv1 sv2 statO"])
          subgoal unfolding le_fun_def D by simp (meson atLeastLessThan_iff nxt subsetD)
          subgoal . . . .
  show ?thesis using unwind_lrsecure[OF i c] .
qed

(* A sufficient criterion for unwindIntoCond, removing the proact part: *)
lemma unwindIntoCond_simpleI:
assumes  
 "\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2)"
and 
"\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 statA = Eq 
 \<Longrightarrow>
 isIntO s1 \<longleftrightarrow> isIntO s2"
"\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 react \<Delta>' w1 w2 s1 s2 statA sv1 sv2 statO"
shows "unwindIntoCond \<Delta> \<Delta>'"
using assms unfolding unwindIntoCond_def by auto

lemma unwindIntoCond_simpleI2:
assumes 
 "\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2)"
and 
"\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 statA = Eq 
 \<Longrightarrow>
 isIntO s1 \<longleftrightarrow> isIntO s2"
and 
"\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (\<exists>v<w. proact \<Delta>' v w1 w2 s1 s2 statA sv1 sv2 statO)"
shows "unwindIntoCond \<Delta> \<Delta>'"
using assms unfolding unwindIntoCond_def by auto

lemma unwindIntoCond_simpleIB:
assumes  
 "\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2)"
and 
"\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 statA = Eq 
 \<Longrightarrow>
 isIntO s1 \<longleftrightarrow> isIntO s2"
and 
"\<And>w w1 w2 s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (\<exists>v<w. proact \<Delta>' v w1 w2 s1 s2 statA sv1 sv2 statO) \<or> react \<Delta>' w1 w2 s1 s2 statA sv1 sv2 statO"
shows "unwindIntoCond \<Delta> \<Delta>'"
  using assms unfolding unwindIntoCond_def by auto

(* *)

definition oor where 
"oor \<Delta> \<Delta>\<^sub>2 \<equiv> \<lambda>w w1 w2 s1 s2 statA sv1 sv2 statO. 
  \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO"

lemma oorI1: 
"\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor \<Delta> \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor_def by simp

lemma oorI2: 
"\<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor \<Delta> \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor_def by simp

definition oor3 where 
"oor3 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<equiv> \<lambda>w w1 w2 s1 s2 statA sv1 sv2 statO. 
  \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>3 w w1 w2 s1 s2 statA sv1 sv2 statO"

lemma oor3I1: 
"\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor3 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor3_def by simp

lemma oor3I2: 
"\<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor3 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor3_def by simp

lemma oor3I3: 
"\<Delta>\<^sub>3 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor3 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor3_def by simp

definition oor4 where 
"oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<equiv> \<lambda>w w1 w2 s1 s2 statA sv1 sv2 statO. 
  \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>3 w w1 w2 s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>4 w w1 w2 s1 s2 statA sv1 sv2 statO"

lemma oor4I1: 
"\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor4_def by simp

lemma oor4I2: 
"\<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor4_def by simp

lemma oor4I3: 
"\<Delta>\<^sub>3 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor4_def by simp

lemma oor4I4: 
"\<Delta>\<^sub>4 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 w w1 w2 s1 s2 statA sv1 sv2 statO"
  unfolding oor4_def by simp

definition oor5 where 
"oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 \<equiv> \<lambda>w w1 w2 s1 s2 statA sv1 sv2 statO. 
  \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>3 w w1 w2 s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>4 w w1 w2 s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>5 w w1 w2 s1 s2 statA sv1 sv2 statO"

lemma oor5I1: 
"\<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor5_def by simp

lemma oor5I2: 
"\<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor5_def by simp

lemma oor5I3: 
"\<Delta>\<^sub>3 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor5_def by simp

lemma oor5I4: 
"\<Delta>\<^sub>4 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor5_def by simp

lemma oor5I5: 
"\<Delta>\<^sub>5 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding oor5_def by simp


(* *)


lemma isIntO_match1: "isIntO s1 \<Longrightarrow> match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding match1_def by auto

lemma isIntO_match2: "isIntO s2 \<Longrightarrow> match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO"
unfolding match2_def by auto

lemma isIntO_match: 
  assumes \<open>isIntO s1\<close> and \<open>isIntO s2\<close>
      and \<open>match12 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO\<close>
    shows \<open>react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO\<close>
  unfolding react_def apply (intro conjI)
  subgoal
    using assms(1) by (rule isIntO_match1)
  subgoal
    using assms(2) by (rule isIntO_match2)
  subgoal
    using assms(3) by assumption
  .

(* *)

lemma match1_1_oorI1: 
"match1_1 \<Delta> w1 w2 s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> 
 match1_1 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s1' s2 statA sv1 sv2 statO"
apply(rule match1_1_mono) unfolding le_fun_def oor_def by auto

lemma match1_1_oorI2: 
"match1_1 \<Delta>\<^sub>2 w1 w2 s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> 
 match1_1 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s1' s2 statA sv1 sv2 statO"
apply(rule match1_1_mono) unfolding le_fun_def oor_def by auto

lemma match1_oorI1: 
"match1 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match1 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule match1_mono) unfolding le_fun_def oor_def by auto

lemma match1_oorI2: 
"match1 \<Delta>\<^sub>2 w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match1 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule match1_mono) unfolding le_fun_def oor_def by auto

(* *)

lemma match2_1_oorI1: 
"match2_1 \<Delta> w1 w2 s1 s2 s2' statA sv1 sv2 statO \<Longrightarrow> 
 match2_1 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 s2' statA sv1 sv2 statO"
apply(rule match2_1_mono) unfolding le_fun_def oor_def by auto

lemma match2_1_oorI2: 
"match2_1 \<Delta>\<^sub>2 w1 w2 s1 s2 s2' statA sv1 sv2 statO \<Longrightarrow> 
 match2_1 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 s2' statA sv1 sv2 statO"
apply(rule match2_1_mono) unfolding le_fun_def oor_def by auto

lemma match2_oorI1: 
"match2 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match2 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule match2_mono) unfolding le_fun_def oor_def by auto

lemma match2_oorI2: 
"match2 \<Delta>\<^sub>2 w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match2 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule match2_mono) unfolding le_fun_def oor_def by auto

(* *)

lemma match12_oorI1: 
"match12 \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match12 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule match12_mono) unfolding le_fun_def oor_def by auto

lemma match12_oorI2: 
"match12 \<Delta>\<^sub>2 w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match12 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule match12_mono) unfolding le_fun_def oor_def by auto

lemma match12_1_oorI1: 
"match12_1 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_1 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1' s2' statA' sv1 sv2 statO"
apply(rule match12_1_mono) unfolding le_fun_def oor_def by auto

lemma match12_1_oorI2: 
"match12_1 \<Delta>\<^sub>2 w1 w2 s1' s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_1 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1' s2' statA' sv1 sv2 statO"
apply(rule match12_1_mono) unfolding le_fun_def oor_def by auto

lemma match12_2_oorI1: 
"match12_2 \<Delta> w1 w2 s2 s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_2 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s2 s2' statA' sv1 sv2 statO"
apply(rule match12_2_mono) unfolding le_fun_def oor_def by auto

lemma match12_2_oorI2: 
"match12_2 \<Delta>\<^sub>2 w1 w2 s2 s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_2 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s2 s2' statA' sv1 sv2 statO"
apply(rule match12_2_mono) unfolding le_fun_def oor_def by auto

lemma match12_12_oorI1: 
"match12_12 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_12 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1' s2' statA' sv1 sv2 statO"
apply(rule match12_12_mono) unfolding le_fun_def oor_def by auto

lemma match12_12_oorI2: 
"match12_12 \<Delta>\<^sub>2 w1 w2 s1' s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_12 (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1' s2' statA' sv1 sv2 statO"
apply(rule match12_12_mono) unfolding le_fun_def oor_def by auto

(* *)

lemma match_oorI1: 
"react \<Delta> w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 react (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule match_mono) unfolding le_fun_def oor_def by auto

lemma match_oorI2: 
"react \<Delta>\<^sub>2 w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 react (oor \<Delta> \<Delta>\<^sub>2) w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule match_mono) unfolding le_fun_def oor_def by auto

(* *)

lemma proact_oorI1: 
"proact \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 proact (oor \<Delta> \<Delta>\<^sub>2) w w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule proact_mono) unfolding le_fun_def oor_def by auto

lemma proact_oorI2: 
"proact \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 proact (oor \<Delta> \<Delta>\<^sub>2) w w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule proact_mono) unfolding le_fun_def oor_def by auto

lemma move_1_oorI1: 
"move_1 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_1 (oor \<Delta> \<Delta>\<^sub>2) w w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule move_1_mono) unfolding le_fun_def oor_def by auto

lemma move_1_oorI2: 
"move_1 \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_1 (oor \<Delta> \<Delta>\<^sub>2) w w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule move_1_mono) unfolding le_fun_def oor_def by auto

lemma move_2_oorI1: 
"move_2 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_2 (oor \<Delta> \<Delta>\<^sub>2) w w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule move_2_mono) unfolding le_fun_def oor_def by auto

lemma move_2_oorI2: 
"move_2 \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_2 (oor \<Delta> \<Delta>\<^sub>2) w w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule move_2_mono) unfolding le_fun_def oor_def by auto

lemma move_12_oorI1: 
"move_12 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_12 (oor \<Delta> \<Delta>\<^sub>2) w w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule move_12_mono) unfolding le_fun_def oor_def by auto

lemma move_12_oorI2: 
"move_12 \<Delta>\<^sub>2 w w1 w2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_12 (oor \<Delta> \<Delta>\<^sub>2) w w1 w2 s1 s2 statA sv1 sv2 statO"
apply(rule move_12_mono) unfolding le_fun_def oor_def by auto

end (* context Relative_Security *)


context Relative_Security_Determ  
begin 

lemma match1_1_defD: "match1_1 \<Delta> w1 w2 s1 s1' s2 statA sv1 sv2 statO \<longleftrightarrow>         
    \<not> finalV sv1 \<and> \<Delta> \<infinity> w1 w2 s1' s2 statA (nextO sv1) sv2 statO"
unfolding match1_1_def validTrans_iff_next by simp

lemma match1_12_defD: "match1_12 \<Delta> w1 w2 s1 s1' s2 statA sv1 sv2 statO \<longleftrightarrow>  
  \<not> finalV sv1 \<and> \<not> finalV sv2 \<and>     
  \<Delta> \<infinity> w1 w2 s1' s2 statA (nextO sv1) (nextO sv2) (sstatO' statO sv1 sv2)"
unfolding match1_12_def validTrans_iff_next by simp

lemmas match1_defsD = match1_def match1_1_defD match1_12_defD

(*  *)

lemma match2_1_defD: "match2_1 \<Delta> w1 w2 s1 s2 s2' statA sv1 sv2 statO \<longleftrightarrow> 
  \<not> finalV sv2 \<and> \<Delta> \<infinity> w1 w2 s1 s2' statA sv1 (nextO sv2) statO"
unfolding match2_1_def validTrans_iff_next by simp

lemma match2_12_defD: "match2_12 \<Delta> w1 w2 s1 s2 s2' statA sv1 sv2 statO \<longleftrightarrow> 
  \<not> finalV sv1 \<and> \<not> finalV sv2 \<and> \<Delta> \<infinity> w1 w2 s1 s2' statA (nextO sv1) (nextO sv2) (sstatO' statO sv1 sv2)"
unfolding match2_12_def validTrans_iff_next by simp

lemmas match2_defsD = match2_def match2_1_defD match2_12_defD

(* *)

lemma match12_1_defD: "match12_1 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<longleftrightarrow>  
 \<not> finalV sv1 \<and> \<Delta> \<infinity> w1 w2 s1' s2' statA' (nextO sv1) sv2 statO"
unfolding match12_1_def validTrans_iff_next by simp

lemma match12_2_defD: "match12_2 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<longleftrightarrow>  
  \<not> finalV sv2 \<and> \<Delta> \<infinity> w1 w2 s1' s2' statA' sv1 (nextO sv2) statO"
unfolding match12_2_def validTrans_iff_next by simp

lemma match12_12_defD: "match12_12 \<Delta> w1 w2 s1' s2' statA' sv1 sv2 statO \<longleftrightarrow>  
    (let statO' = sstatO' statO sv1 sv2 in 
    \<not> finalV sv1 \<and> \<not> finalV sv2 \<and>   
    (statA' = Diff \<longrightarrow> statO' = Diff) \<and>       
    \<Delta> \<infinity> w1 w2 s1' s2' statA' (nextO sv1) (nextO sv2) statO')"
unfolding match12_12_def validTrans_iff_next by simp

lemmas match12_defsD = match12_def match12_1_defD match12_2_defD match12_12_defD

lemmas match_deep_defsD = match1_defsD match2_defsD match12_defsD

(* *)

lemma move_1_defD: "move_1 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<longleftrightarrow> 
   \<not> finalV sv1 \<and> \<Delta> w w1 w2 s1 s2 statA (nextO sv1) sv2 statO"
unfolding move_1_def validTrans_iff_next by simp

lemma move_2_defD: "move_2 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<longleftrightarrow>  
   \<not> finalV sv2 \<and> \<Delta> w w1 w2 s1 s2 statA sv1 (nextO sv2) statO"
unfolding move_2_def validTrans_iff_next by simp

lemma move_12_defD: "move_12 \<Delta> w w1 w2 s1 s2 statA sv1 sv2 statO \<longleftrightarrow>  
   (let statO' = sstatO' statO sv1 sv2 in 
   \<not> finalV sv1 \<and> \<not> finalV sv2 \<and>     
   \<Delta> w w1 w2 s1 s2 statA (nextO sv1) (nextO sv2) statO')" 
unfolding move_12_def validTrans_iff_next by simp

lemmas proact_defsD = proact_def move_1_defD move_2_defD move_12_defD

end (* context Relative_Security_Determ *)



end 