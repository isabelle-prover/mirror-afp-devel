section \<open>Unwinding Proof Method for Finitary Relative Security\<close>

text \<open> This theory formalizes the notion of unwinding for finitary relative security, 
and proves its soundness.  \<close>

theory Unwinding_fin
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

definition initCond :: 
"(enat \<Rightarrow> 'stateO \<Rightarrow> 'stateO \<Rightarrow> status \<Rightarrow> 'stateV \<Rightarrow> 'stateV \<Rightarrow> status \<Rightarrow> bool) \<Rightarrow> bool" where 
"initCond \<Delta> \<equiv> \<forall>s1 s2. 
   istateO s1 \<and> istateO s2
   \<longrightarrow> 
   (\<exists>sv1 sv2. istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 
            \<and> \<Delta> \<infinity> s1 s2 Eq sv1 sv2 Eq)"


(* *)

definition "match1_1 \<Delta> s1 s1' s2 statA sv1 sv2 statO \<equiv> 
  \<exists>sv1'. validTransV (sv1,sv1') \<and>        
    \<Delta> \<infinity> s1' s2 statA sv1' sv2 statO"

definition "match1_12 \<Delta> s1 s1' s2 statA sv1 sv2 statO \<equiv> 
  \<exists>sv1' sv2'. 
    let statO' = sstatO' statO sv1 sv2 in 
    validTransV (sv1,sv1') \<and> 
    validTransV (sv2,sv2') \<and>      
    \<Delta> \<infinity> s1' s2 statA sv1' sv2' statO'"

definition "match1 \<Delta> s1 s2 statA sv1 sv2 statO \<equiv> 
  \<not> isIntO s1 \<longrightarrow> 
   (\<forall>s1'. validTransO (s1,s1') 
      \<longrightarrow> 
      (\<not> isSecO s1 \<and> \<Delta> \<infinity> s1' s2 statA sv1 sv2 statO) \<or> 
      (eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> match1_1 \<Delta> s1 s1' s2 statA sv1 sv2 statO) \<or> 
      (eqSec sv1 s1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> match1_12 \<Delta> s1 s1' s2 statA sv1 sv2 statO))"

lemmas match1_defs = match1_def match1_1_def match1_12_def

lemma match1_1_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match1_1 \<Delta> s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> match1_1 \<Delta>' s1 s1' s2 statA sv1 sv2 statO"
unfolding le_fun_def match1_1_def by auto

lemma match1_12_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match1_12 \<Delta> s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> match1_12 \<Delta>' s1 s1' s2 statA sv1 sv2 statO"
unfolding le_fun_def match1_12_def by fastforce

lemma match1_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "match1 \<Delta> s1 s2 statA sv1 sv2 statO \<Longrightarrow> match1 \<Delta>' s1 s2 statA sv1 sv2 statO"
unfolding match1_def apply clarify subgoal for s1' apply(erule allE[of _ s1'])
using match1_1_mono[OF assms, of s1 s1' s2 statA sv1 sv2 statO] 
      match1_12_mono[OF assms, of s1 s1' s2 statA sv1 sv2 statO] 
      assms[unfolded le_fun_def, rule_format, of _ s1' s2 statA sv1 sv2 statO]
by auto .

(*  *)

definition "match2_1 \<Delta> s1 s2 s2' statA sv1 sv2 statO \<equiv> 
  \<exists>sv2'. validTransV (sv2,sv2') \<and>   
        \<Delta> \<infinity> s1 s2' statA sv1 sv2' statO"

definition "match2_12 \<Delta> s1 s2 s2' statA sv1 sv2 statO \<equiv> 
  \<exists>sv1' sv2'.   
    let statO' = sstatO' statO sv1 sv2 in 
    validTransV (sv1,sv1') \<and> 
    validTransV (sv2,sv2') \<and>         
    \<Delta> \<infinity> s1 s2' statA sv1' sv2' statO'"

definition "match2 \<Delta> s1 s2 statA sv1 sv2 statO \<equiv> 
  \<not> isIntO s2 \<longrightarrow>
  (\<forall>s2'. validTransO (s2,s2') 
     \<longrightarrow> 
     (\<not> isSecO s2 \<and> \<Delta> \<infinity> s1 s2' statA sv1 sv2 statO) \<or> 
     (eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> match2_1 \<Delta> s1 s2 s2' statA sv1 sv2 statO) \<or>
     (\<not> isSecV sv1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and> match2_12 \<Delta> s1 s2 s2' statA sv1 sv2 statO))"

lemmas match2_defs = match2_def match2_1_def match2_12_def

lemma match2_1_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match2_1 \<Delta> s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> match2_1 \<Delta>' s1 s1' s2 statA sv1 sv2 statO"
unfolding le_fun_def match2_1_def by auto

lemma match2_12_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match2_12 \<Delta> s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> match2_12 \<Delta>' s1 s1' s2 statA sv1 sv2 statO"
unfolding le_fun_def match2_12_def by fastforce

lemma match2_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "match2 \<Delta> s1 s2 statA sv1 sv2 statO \<Longrightarrow> match2 \<Delta>' s1 s2 statA sv1 sv2 statO"
unfolding match2_def apply clarify subgoal for s2' apply(erule allE[of _ s2'])
using match2_1_mono[OF assms, of s1 s2 s2' statA sv1 sv2 statO] 
      match2_12_mono[OF assms, of s1 s2 s2' statA sv1 sv2 statO] 
      assms[unfolded le_fun_def, rule_format, of _ s1 s2' statA sv1 sv2 statO]
by auto .

(* *)

definition "match12_1 \<Delta> s1' s2' statA' sv1 sv2 statO \<equiv> 
  \<exists>sv1'. validTransV (sv1,sv1') \<and>   
        \<Delta> \<infinity> s1' s2' statA' sv1' sv2 statO"

definition "match12_2 \<Delta> s1' s2' statA' sv1 sv2 statO \<equiv> 
  \<exists>sv2'. validTransV (sv2,sv2') \<and>  
        \<Delta> \<infinity> s1' s2' statA' sv1 sv2' statO"

definition "match12_12 \<Delta> s1' s2' statA' sv1 sv2 statO \<equiv> 
  \<exists>sv1' sv2'.  
    let statO' = sstatO' statO sv1 sv2 in 
    validTransV (sv1,sv1') \<and>   
    validTransV (sv2,sv2') \<and>  
    (statA' = Diff \<longrightarrow> statO' = Diff) \<and>       
    \<Delta> \<infinity> s1' s2' statA' sv1' sv2' statO'"

definition "match12 \<Delta> s1 s2 statA sv1 sv2 statO \<equiv> 
\<forall>s1' s2'. 
   let statA' = sstatA' statA s1 s2 in
   validTransO (s1,s1') \<and> 
   validTransO (s2,s2') \<and> 
   Opt.eqAct s1 s2 \<and> 
   isIntO s1 \<and> isIntO s2
   \<longrightarrow> 
   (\<not> isSecO s1 \<and> \<not> isSecO s2 \<and> (statA = statA' \<or> statO = Diff) \<and> \<Delta> \<infinity> s1' s2' statA' sv1 sv2 statO)
   \<or> 
   (\<not> isSecO s2 \<and> eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> 
    (statA = statA' \<or> statO = Diff) \<and> 
    match12_1 \<Delta> s1' s2' statA' sv1 sv2 statO)  
   \<or> 
   (\<not> isSecO s1 \<and> eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> 
    (statA = statA' \<or> statO = Diff) \<and> 
    match12_2 \<Delta> s1' s2' statA' sv1 sv2 statO)  
   \<or> 
   (eqSec sv1 s1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and>   
    match12_12 \<Delta> s1' s2' statA' sv1 sv2 statO)"

lemmas match12_defs = match12_def match12_1_def match12_2_def match12_12_def

(* A sufficient critetion for match12, removing the asymmetric conditions 
and the isInt assumptions: *)
lemma match12_simpleI: 
assumes "\<And>s1' s2' statA'. 
   statA' = sstatA' statA s1 s2 \<Longrightarrow> 
   validTransO (s1,s1') \<Longrightarrow> 
   validTransO (s2,s2') \<Longrightarrow>
   Opt.eqAct s1 s2 \<Longrightarrow> 
   (\<not> isSecO s1 \<and> \<not> isSecO s2 \<and> (statA = statA' \<or> statO = Diff) \<and> \<Delta> \<infinity> s1' s2' statA' sv1 sv2 statO)
   \<or> 
   (eqSec sv1 s1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and>   
    match12_12 \<Delta> s1' s2' statA' sv1 sv2 statO)"
shows "match12 \<Delta> s1 s2 statA sv1 sv2 statO"
using assms unfolding match12_def Let_def by blast

lemma match12_1_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match12_1 \<Delta> s1' s2' statA' sv1 sv2 statO \<Longrightarrow> match12_1 \<Delta>' s1' s2' statA' sv1 sv2 statO"
unfolding le_fun_def match12_1_def by auto

lemma match12_2_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match12_2 \<Delta> s1 s2' statA' sv1 sv2 statO \<Longrightarrow> match12_2 \<Delta>' s1 s2' statA' sv1 sv2 statO"
unfolding le_fun_def match12_2_def by auto

lemma match12_12_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> match12_12 \<Delta> s1' s2' statA' sv1 sv2 statO \<Longrightarrow> match12_12 \<Delta>' s1' s2' statA' sv1 sv2 statO"
unfolding le_fun_def match12_12_def by fastforce

lemma match12_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "match12 \<Delta> s1 s2 statA sv1 sv2 statO \<Longrightarrow> match12 \<Delta>' s1 s2 statA sv1 sv2 statO"
unfolding match12_def apply clarify subgoal for s1' s2' apply(erule allE[of _ s1']) apply(erule allE[of _ s2'])
using match12_1_mono[OF assms, of s1' s2' _ sv1 sv2 statO] 
      match12_2_mono[OF assms, of s1' s2' _ sv1 sv2 statO] 
      match12_12_mono[OF assms, of s1' s2' _ sv1 sv2 statO]
      assms[unfolded le_fun_def, rule_format, of _ s1' s2' 
       "sstatA' statA s1 s2" sv1 sv2 statO] 
by simp metis .

(* *)

definition "react \<Delta> s1 s2 statA sv1 sv2 statO \<equiv> 
 match1 \<Delta> s1 s2 statA sv1 sv2 statO 
 \<and>
 match2 \<Delta> s1 s2 statA sv1 sv2 statO 
 \<and> 
 match12 \<Delta> s1 s2 statA sv1 sv2 statO"

lemmas react_defs = match1_def match2_def match12_def
lemmas match_deep_defs = match1_defs match2_defs match12_defs

lemma match_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "react \<Delta> s1 s2 statA sv1 sv2 statO \<Longrightarrow> react \<Delta>' s1 s2 statA sv1 sv2 statO"
unfolding react_def using match1_mono[OF assms] match2_mono[OF assms] match12_mono[OF assms] by auto    

(* *)

definition "move_1 \<Delta> w s1 s2 statA sv1 sv2 statO \<equiv> 
 \<exists>sv1'. validTransV (sv1,sv1') \<and>  
   \<Delta> w s1 s2 statA sv1' sv2 statO"

definition "move_2 \<Delta> w s1 s2 statA sv1 sv2 statO \<equiv> 
 \<exists>sv2'. validTransV (sv2,sv2') \<and>    
   \<Delta> w s1 s2 statA sv1 sv2' statO"

definition "move_12 \<Delta> w s1 s2 statA sv1 sv2 statO \<equiv> 
 \<exists>sv1' sv2'.  
   let statO' = sstatO' statO sv1 sv2 in 
   validTransV (sv1,sv1') \<and> validTransV (sv2,sv2') \<and>     
   \<Delta> w s1 s2 statA sv1' sv2' statO'" 

definition "proact \<Delta> w s1 s2 statA sv1 sv2 statO \<equiv> 
 (\<not> isSecV sv1 \<and> \<not> isIntV sv1 \<and> move_1 \<Delta> w s1 s2 statA sv1 sv2 statO) 
 \<or> 
 (\<not> isSecV sv2 \<and> \<not> isIntV sv2 \<and> move_2 \<Delta> w s1 s2 statA sv1 sv2 statO) 
 \<or> 
 (\<not> isSecV sv1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> move_12 \<Delta> w s1 s2 statA sv1 sv2 statO)"

lemmas proact_defs = proact_def move_1_def move_2_def move_12_def

lemma move_1_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> move_1 \<Delta> meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> move_1 \<Delta>' meas s1 s2 statA sv1 sv2 statO"
unfolding le_fun_def move_1_def by auto

lemma move_2_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> move_2 \<Delta> meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> move_2 \<Delta>' meas s1 s2 statA sv1 sv2 statO"
unfolding le_fun_def move_2_def by auto

lemma move_12_mono: 
"\<Delta> \<le> \<Delta>' \<Longrightarrow> move_12 \<Delta> meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> move_12 \<Delta>' meas s1 s2 statA sv1 sv2 statO"
unfolding le_fun_def move_12_def by fastforce

lemma proact_mono: 
assumes "\<Delta> \<le> \<Delta>'" 
shows "proact \<Delta> meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> proact \<Delta>' meas s1 s2 statA sv1 sv2 statO"
unfolding proact_def using move_1_mono[OF assms] move_2_mono[OF assms] move_12_mono[OF assms] by auto


subsection \<open> The definition of unwinding \<close>

definition unwindCond :: 
"(enat \<Rightarrow> 'stateO \<Rightarrow> 'stateO \<Rightarrow> status \<Rightarrow> 'stateV \<Rightarrow> 'stateV \<Rightarrow> status \<Rightarrow> bool) \<Rightarrow> bool" 
where 
"unwindCond \<Delta> \<equiv> \<forall>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
 \<Delta> w s1 s2 statA sv1 sv2 statO 
 \<longrightarrow> 
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2) 
 \<and> 
 (statA = Eq \<longrightarrow> (isIntO s1 \<longleftrightarrow> isIntO s2))
 \<and>
 ((\<exists>v < w. proact \<Delta> v s1 s2 statA sv1 sv2 statO) 
  \<or> 
  react \<Delta> s1 s2 statA sv1 sv2 statO
 )"


(* *)

(* A sufficient criterion for unwindCond, removing the proact part: *)
lemma unwindCond_simpleI:
assumes  
 "\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2)"
and 
"\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO \<Longrightarrow> statA = Eq 
 \<Longrightarrow>
 isIntO s1 \<longleftrightarrow> isIntO s2"
and 
"\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 react \<Delta> s1 s2 statA sv1 sv2 statO"
shows "unwindCond \<Delta>"
using assms unfolding unwindCond_def by auto


subsection \<open> The soundness of unwinding \<close>

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
   Opt.A tr1 = Opt.A tr2 \<and> (isIntO s1 \<and> isIntO s2 \<longrightarrow> getActO s1 = getActO s2)
   \<Longrightarrow> 
   \<exists>sv1 trv1 sv2 trv2. 
     istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 \<and> 
     \<psi> s1 tr1 s2 tr2 Eq sv1 trv1 sv2 trv2" 
shows rsecure
  unfolding rsecure_def3 apply clarify
  subgoal for s1 tr1 s2 tr2
    using assms[of s1 tr1 s2 tr2] 
    using \<psi>_completedFrom \<psi>_def completedFromO_lastt by (metis (full_types))
  .

proposition unwindCond_ex_\<psi>:
assumes unwind: "unwindCond \<Delta>"
and \<Delta>: "\<Delta> w s1 s2 statA sv1 sv2 statO" and stat: "(statA = Diff \<longrightarrow> statO = Diff)" 
and v: "Opt.validFromS s1 tr1" "Opt.completedFrom s1 tr1" "Opt.validFromS s2 tr2" "Opt.completedFrom s2 tr2"
and tr14: "Opt.A tr1 = Opt.A tr2" 
and r: "reachO s1" "reachO s2" "reachV sv1" "reachV sv2"
shows "\<exists>trv1 trv2. \<psi> s1 tr1 s2 tr2 statO sv1 trv1 sv2 trv2"
using assms(2-)  
proof(induction "length tr1 + length tr2" w
   arbitrary: s1 s2 statA sv1 sv2 statO tr1 tr2 rule: less2_induct')
  case (less w tr1 tr2 s1 s2 statA sv1 sv2 statO)
  note ok = `statA = Diff \<longrightarrow> statO = Diff` 
  note \<Delta> = `\<Delta> w s1 s2 statA sv1 sv2 statO`
  note A34 = `Opt.A tr1 = Opt.A tr2`
  note r34 = less.prems(8,9) note r12 = less.prems(10,11)
  note r = r34 r12 
  note r3 = r34(1) note r4 = r34(2) note r1 = r12(1) note r2 = r12(2)

  have i34: "statA = Eq \<longrightarrow> isIntO s1 = isIntO s2"
  and f34: "finalO s1 = finalO s2 \<and> finalV sv1 = finalO s1 \<and> finalV sv2 = finalO s2"
    using \<Delta> unwind[unfolded unwindCond_def] r by auto

  have proact_match: "(\<exists>v<w. proact \<Delta> v s1 s2 statA sv1 sv2 statO) \<or> react \<Delta> s1 s2 statA sv1 sv2 statO"
    using \<Delta> unwind[unfolded unwindCond_def] r by auto
  show ?case using proact_match proof safe
    fix v assume v: "v < w"
    assume "proact \<Delta> v s1 s2 statA sv1 sv2 statO"
    thus ?thesis unfolding proact_def proof safe
      assume sv1: "\<not> isSecV sv1" "\<not> isIntV sv1" and "move_1 \<Delta> v s1 s2 statA sv1 sv2 statO"
      then obtain sv1'
      where 0: "validTransV (sv1,sv1')" 
      and \<Delta>: "\<Delta> v s1 s2 statA sv1' sv2 statO"  
      unfolding move_1_def by auto
      have r1': "reachV sv1'" using r1 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2 tr2 statO sv1' trv1 sv2 trv2"  
      using less(2)[OF v, of tr1 tr2 s1 s2 statA sv1' sv2 statO, simplified, OF \<Delta> ok _ _ _ _ _ r34 r1' r2] 
      using A34 less.prems(3-6) by blast
      show ?thesis apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ trv2])
      using \<psi> ok 0 sv1 unfolding \<psi>_def Van.completedFrom_def by auto
    next 
      assume sv2: "\<not> isSecV sv2" "\<not> isIntV sv2" and "move_2 \<Delta> v s1 s2 statA sv1 sv2 statO"
      then obtain sv2'
      where 0: "validTransV (sv2,sv2')"  
      and \<Delta>: "\<Delta> v s1 s2 statA sv1 sv2' statO"  
      unfolding move_2_def by auto
      have r2': "reachV sv2'" using r2 0 by (metis Van.reach.Step fst_conv snd_conv)
      obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2 tr2 statO sv1 trv1 sv2' trv2"  
      using less(2)[OF v, of tr1 tr2 s1 s2 statA sv1 sv2' statO, simplified, OF \<Delta> ok _ _ _ _ _ r34 r1 r2']  
      using A34 less.prems(3-6) by blast
      show ?thesis apply(rule exI[of _ trv1]) apply(rule exI[of _ "sv2 # trv2"])
      using \<psi> ok 0 sv2 unfolding \<psi>_def Van.completedFrom_def by auto 
    next
      assume sv12: "\<not> isSecV sv1" "\<not> isSecV sv2" "Van.eqAct sv1 sv2" 
      and "move_12 \<Delta> v s1 s2 statA sv1 sv2 statO"
      then obtain sv1' sv2' statO'
      where 0: "statO' = sstatO' statO sv1 sv2" 
      "validTransV (sv1,sv1') " "\<not> isSecV sv1"
      "validTransV (sv2,sv2')" "\<not> isSecV sv2"  
      "Van.eqAct sv1 sv2"  
      and \<Delta>: "\<Delta> v s1 s2 statA sv1' sv2' statO'"  
      unfolding move_12_def by auto
      have r12': "reachV sv1'" "reachV sv2'" using r1 r2 0 by (metis Van.reach.Step fst_conv snd_conv)+
      have ok': "statA = Diff \<longrightarrow> statO' = Diff" using ok 0 unfolding sstatO'_def by (cases statO, auto) 
      obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2 tr2 statO' sv1' trv1 sv2' trv2" 
      using less(2)[OF v, of tr1 tr2 s1 s2 statA sv1' sv2' statO', simplified, OF \<Delta> ok' _ _ _ _ _ r34 r12']   
      using A34 less.prems(3-6) by blast
      show ?thesis apply(rule exI[of _ "sv1 # trv1"]) apply(rule exI[of _ "sv2 # trv2"])
      using \<psi> ok' 0 sv12 unfolding \<psi>_def sstatO'_def Van.completedFrom_def
      using Van.A.Cons_unfold Van.eqAct_def completedFromO_lastt less.prems(4) 
      less.prems(6) by auto 
    qed
  next
    assume m: "react \<Delta> s1 s2 statA sv1 sv2 statO"
    show ?thesis
    proof(cases "length tr1 \<le> Suc 0") 
      case True note tr1 = True
      hence "tr1 = [] \<or> tr1 = [s1]"  
      by (metis Opt.validFromS_Cons_iff le_0_eq le_SucE length_0_conv length_Suc_conv less.prems(3))
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
      by (metis (no_types, opaque_lifting) Opt.completed_Cons Opt.completed_Nil 
      Simple_Transition_System.validFromS_Cons_iff Suc_n_not_le_n bot_nat_0.extremum le_Suc_eq length_Cons less.prems(5) less.prems(6) list.exhaust order_antisym_conv)
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
        have m: "match1 \<Delta> s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto
        have "(\<not> isSecO s1 \<and> \<Delta> \<infinity> s1' s2 statA sv1 sv2 statO) \<or> 
              (eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and> match1_1 \<Delta> s1 s1' s2 statA sv1 sv2 statO) \<or> 
              (eqSec sv1 s1 \<and> \<not> isSecV sv2 \<and> Van.eqAct sv1 sv2 \<and> match1_12 \<Delta> s1 s1' s2 statA sv1 sv2 statO)" 
        using m isAO3 trn3 ok unfolding match1_def by auto  
        thus ?thesis 
        proof safe 
          assume "\<not> isSecO s1" and \<Delta>: "\<Delta> \<infinity> s1' s2 statA sv1 sv2 statO"
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
          assume trn13: "eqSec sv1 s1" and
          Atrn1: "\<not> isIntV sv1" and "match1_1 \<Delta> s1 s1' s2 statA sv1 sv2 statO"
          then obtain sv1' where  
          trn1: "validTransV (sv1,sv1') " and              
          \<Delta>: "\<Delta> \<infinity> s1' s2 statA sv1' sv2 statO"
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
          Atrn12: "Van.eqAct sv1 sv2" and "match1_12 \<Delta> s1 s1' s2 statA sv1 sv2 statO"
          then obtain sv1' sv2' statO' where
          statO': "statO' = sstatO' statO sv1 sv2" and  
          trn1: "validTransV (sv1,sv1') " and 
          trn2: "validTransV (sv2,sv2')" and 
          \<Delta>: "\<Delta> \<infinity> s1' s2 statA sv1' sv2' statO'"
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
        have m: "match2 \<Delta> s1 s2 statA sv1 sv2 statO" using m unfolding react_def by auto 
        have "(\<not> isSecO s2 \<and> \<Delta> \<infinity> s1 s2' statA sv1 sv2 statO) \<or> 
              (eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> match2_1 \<Delta> s1 s2 s2' statA sv1 sv2 statO) \<or> 
              (\<not> isSecV sv1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and> match2_12 \<Delta> s1 s2 s2' statA sv1 sv2 statO)" 
        using m isAO4 trn4 ok tr2'NE  unfolding match2_def by auto 
        thus ?thesis 
        proof safe 
          assume "\<not> isSecO s2" and \<Delta>: "\<Delta> \<infinity> s1 s2' statA sv1 sv2 statO"
          hence S4: "Opt.S tr2' = Opt.S tr2" unfolding tr2 by auto            
          obtain trv1 trv2 where \<psi>: "\<psi> s1 tr1 s2' tr2' statO sv1 trv1 sv2 trv2"
          using less(1)[of tr1 tr2', OF _ \<Delta> _ _ _ _ _ _ r3 r4', simplified]
          using less.prems tr2' ok A34' tr1'NE tr2'NE unfolding tr1 tr2 Opt.completedFrom_def by (cases "isIntO s2", auto)  
          show ?thesis apply(rule exI[of _ trv1]) apply(rule exI[of _ trv2])
          using \<psi> O44' S4 unfolding \<psi>_def 
          using completedFromO_lastt less.prems(6)  
          unfolding Opt.completedFrom_def using tr2 tr2'NE by auto
        next
          assume trn24: "eqSec sv2 s2" and
          Atrn2: "\<not> isIntV sv2" and "match2_1 \<Delta> s1 s2 s2' statA sv1 sv2 statO"
          then obtain sv2' where trn2: "validTransV (sv2,sv2')" and              
          \<Delta>: "\<Delta> \<infinity> s1 s2' statA sv1 sv2' statO"
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
          Atrn12: "Van.eqAct sv1 sv2" and  "match2_12 \<Delta> s1 s2 s2' statA sv1 sv2 statO"
          then obtain sv1' sv2' statO' where
          statO': "statO' = sstatO' statO sv1 sv2" and 
          trn1: "validTransV (sv1,sv1')" and               
          trn2: "validTransV (sv2,sv2')" and               
          \<Delta>: "\<Delta> \<infinity> s1 s2' statA sv1' sv2' statO'"
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
        have m: "match12 \<Delta> s1 s2 statA sv1 sv2 statO" using m unfolding statA' react_def by auto
        have trn34: "getObsO s1 = getObsO s2 \<or> statA' = Diff"
        using isAO34 unfolding statA' sstatA'_def by (cases statA,auto)  
        have "(\<not> isSecO s1 \<and> \<not> isSecO s2 \<and> (statA = statA' \<or> statO = Diff) \<and> \<Delta> \<infinity> s1' s2' statA' sv1 sv2 statO) 
              \<or> 
              (\<not> isSecO s2 \<and> eqSec sv1 s1 \<and> \<not> isIntV sv1 \<and>
               (statA = statA' \<or> statO = Diff) \<and> 
               match12_1 \<Delta> s1' s2' statA' sv1 sv2 statO)  
              \<or> 
              (\<not> isSecO s1 \<and> eqSec sv2 s2 \<and> \<not> isIntV sv2 \<and> 
               (statA = statA' \<or> statO = Diff) \<and> 
               match12_2 \<Delta> s1' s2' statA' sv1 sv2 statO)  
              \<or> 
              (eqSec sv1 s1 \<and> eqSec sv2 s2 \<and> Van.eqAct sv1 sv2 \<and> 
               match12_12 \<Delta> s1' s2' statA' sv1 sv2 statO)"
        (is "?K1 \<or> ?K2 \<or> ?K3 \<or> ?K4")
        using m[unfolded match12_def, rule_format, of s1' s2'] 
        isAO34 A34' trn3 trn4 tr1'NE tr2'NE 
        unfolding s13 s24 trn34 statA' Opt.eqAct_def sstatA'_def by auto
        thus ?thesis proof (elim disjE)
          assume K1: "?K1" hence \<Delta>: "\<Delta> \<infinity> s1' s2' statA' sv1 sv2 statO" by simp
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
          then obtain sv1' where  
          trn1: "validTransV (sv1,sv1') " and 
          trn13: "eqSec sv1 s1" and
          Atrn1: "\<not> isIntV sv1" and  ok': "(statA' = statA \<or> statO = Diff)" and 
          \<Delta>: "\<Delta> \<infinity> s1' s2' statA' sv1' sv2 statO"
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
          by simp (smt (verit, ccfv_SIG) Opt.S.simps(2) Simple_Transition_System.lastt_Cons 
          Van.A.Cons_unfold Van.O.Cons_unfold \<psi>_def list.simps(3) status.simps(1))
        next
          assume K3: "?K3" 
          then obtain sv2' where  
          trn2: "validTransV (sv2,sv2')" and 
          trn24: "eqSec sv2 s2" and
          Atrn2: "\<not> isIntV sv2" and  ok': "(statA' = statA \<or> statO = Diff)" and 
          \<Delta>: "\<Delta> \<infinity> s1' s2' statA' sv1 sv2' statO"
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
          by simp (metis last.simps lastt_def list.simps(3) status.distinct(2))
        next
          assume K4: "?K4"
          then obtain sv1' sv2' statO' where 0: 
            "statO' = sstatO' statO sv1 sv2"
            "validTransV (sv1,sv1') "
            "eqSec sv1 s1"
            "validTransV (sv2,sv2')"
            "eqSec sv2 s2"
            "Van.eqAct sv1 sv2"
            and ok': "statA' = Diff \<longrightarrow> statO' = Diff" and \<Delta>: "\<Delta> \<infinity> s1' s2' statA' sv1' sv2' statO'"
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
          by (smt (z3) Simple_Transition_System.lastt_Cons Van.A.Cons_unfold Van.O.Cons_unfold 
           completedFromO_lastt f3 f34 lastt_Nil less.prems(4) less.prems(6) list.inject s13 
           s24 status.simps(1) tr1 tr1' tr2 tr2' trn3 trn4 newStat.simps(1) newStat.simps(3))   
       qed
      qed
    qed
  qed
qed

theorem unwind_rsecure: 
  assumes init: "initCond \<Delta>"
    and unwind: "unwindCond \<Delta>"
  shows rsecure
  apply (rule rsecure_strong)
  apply (elim conjE)
  subgoal for s1 tr1 s2 tr2
    using init unfolding initCond_def 
    apply (erule_tac allE[of _ s1])    
    apply (elim allE[of _ s2] conjE)
    apply (elim impE[of \<open>istateO s1 \<and> istateO s2\<close>] exE conjE)
    subgoal by clarify
    subgoal for sv1 sv2
      using unwind apply (drule_tac unwindCond_ex_\<psi>, blast+)
      subgoal by (rule Transition_System.reach.Istate)
      subgoal by (rule Transition_System.reach.Istate)
      subgoal by (rule Transition_System.reach.Istate)
      subgoal by (rule Transition_System.reach.Istate)
      apply (elim exE)
      subgoal for trv1 trv2 
        apply (rule exI[of _ sv1], rule exI[of _ trv1], rule exI[of _ sv2], rule exI[of _ trv2])
        by clarify
      .
    .
  .


subsection \<open> Compositional unwinding \<close>

text \<open> We allow networks of unwinding relations that unwind into each other, 
which offer a compositional alternative to monolithic unwinding. \<close>

definition unwindIntoCond :: 
"(enat \<Rightarrow> 'stateO \<Rightarrow> 'stateO \<Rightarrow> status \<Rightarrow> 'stateV \<Rightarrow> 'stateV \<Rightarrow> status \<Rightarrow> bool) \<Rightarrow>  
 (enat \<Rightarrow> 'stateO \<Rightarrow> 'stateO \<Rightarrow> status \<Rightarrow> 'stateV \<Rightarrow> 'stateV \<Rightarrow> status \<Rightarrow> bool)
 \<Rightarrow> bool" 
where 
"unwindIntoCond \<Delta> \<Delta>' \<equiv> \<forall>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<and> reachO s2 \<and> reachV sv1 \<and> reachV sv2 \<and> 
 \<Delta> w s1 s2 statA sv1 sv2 statO \<longrightarrow> 
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2) 
 \<and> 
 (statA = Eq \<longrightarrow> (isIntO s1 \<longleftrightarrow> isIntO s2))
 \<and>
 ((\<exists>v<w. proact \<Delta>' v s1 s2 statA sv1 sv2 statO)   
  \<or> 
  react \<Delta>' s1 s2 statA sv1 sv2 statO)"

(* A sufficient criterion for unwindIntoCond, removing the proact part: *)
lemma unwindIntoCond_simpleI:
assumes  
 "\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2)"
and 
"\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 statA = Eq 
 \<Longrightarrow>
 isIntO s1 \<longleftrightarrow> isIntO s2"
"\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 react \<Delta>' s1 s2 statA sv1 sv2 statO"
shows "unwindIntoCond \<Delta> \<Delta>'"
using assms unfolding unwindIntoCond_def by auto

lemma unwindIntoCond_simpleI2:
assumes 
 "\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2)"
and 
"\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 statA = Eq 
 \<Longrightarrow>
 isIntO s1 \<longleftrightarrow> isIntO s2"
and 
"\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (\<exists>v<w. proact \<Delta>' v s1 s2 statA sv1 sv2 statO)"
shows "unwindIntoCond \<Delta> \<Delta>'"
using assms unfolding unwindIntoCond_def by auto

lemma unwindIntoCond_simpleIB:
assumes  
 "\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (finalO s1 \<longleftrightarrow> finalO s2) \<and> (finalV sv1 \<longleftrightarrow> finalO s1) \<and> (finalV sv2 \<longleftrightarrow> finalO s2)"
and 
"\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 statA = Eq 
 \<Longrightarrow>
 isIntO s1 \<longleftrightarrow> isIntO s2"
and 
"\<And>w s1 s2 statA sv1 sv2 statO. 
 reachO s1 \<Longrightarrow> reachO s2 \<Longrightarrow> reachV sv1 \<Longrightarrow> reachV sv2 \<Longrightarrow> 
 \<Delta> w s1 s2 statA sv1 sv2 statO 
 \<Longrightarrow>
 (\<exists>v<w. proact \<Delta>' v s1 s2 statA sv1 sv2 statO) \<or> react \<Delta>' s1 s2 statA sv1 sv2 statO"
shows "unwindIntoCond \<Delta> \<Delta>'"
  using assms unfolding unwindIntoCond_def by auto

theorem distrib_unwind_rsecure:
assumes m: "0 < m" and nxt: "\<And>i. i < (m::nat) \<Longrightarrow> nxt i \<subseteq> {0..<m}" 
and init: "initCond (\<Delta>s 0)" 
and step: "\<And>i. i < m \<Longrightarrow> 
  unwindIntoCond (\<Delta>s i) (\<lambda>w s1 s2 statA sv1 sv2 statO. 
     \<exists>j \<in> nxt i. \<Delta>s j w s1 s2 statA sv1 sv2 statO)"
shows rsecure
proof-
  define \<Delta> where D: "\<Delta> \<equiv> \<lambda>w s1 s2 statA sv1 sv2 statO. \<exists>i < m. \<Delta>s i w s1 s2 statA sv1 sv2 statO"
  have i: "initCond \<Delta>" 
    using init m unfolding initCond_def D by meson
  have c: "unwindCond \<Delta>" unfolding unwindCond_def apply(intro allI impI allI)
  apply(subst (asm) D) apply (elim exE conjE)
    subgoal for w s1 s2 statA sv1 sv2 statO i 
      apply(frule step) unfolding unwindIntoCond_def
      apply(erule allE[of _ w])
      apply(erule allE[of _ s1]) apply(erule allE[of _ s2]) apply(erule allE[of _ statA])
      apply(erule allE[of _ sv1]) apply(erule allE[of _ sv2]) apply(erule allE[of _ statO])
      apply simp apply(elim conjE) 
      apply(erule disjE)
        subgoal apply(rule disjI1)
        subgoal apply(elim exE conjE) subgoal for v
        apply(rule exI[of _ v], simp) 
        apply(rule proact_mono[of "\<lambda>w s1 s2 statA sv1 sv2 statO. \<exists>j\<in>nxt i. \<Delta>s j w s1 s2 statA sv1 sv2 statO"])
          subgoal unfolding le_fun_def D by simp (meson atLeastLessThan_iff nxt subsetD)
          subgoal . . . .
        subgoal apply(rule disjI2)
        apply(rule match_mono[of "\<lambda>w s1 s2 statA sv1 sv2 statO. \<exists>j\<in>nxt i. \<Delta>s j w s1 s2 statA sv1 sv2 statO"])
          subgoal unfolding le_fun_def D by simp (meson atLeastLessThan_iff nxt subsetD)
          subgoal . . . .
  show ?thesis using unwind_rsecure[OF i c] .
qed

corollary linear_unwind_rsecure:
assumes init: "initCond (\<Delta>s 0)"
and step: "(\<And>i. i < m \<Longrightarrow> 
  unwindIntoCond (\<Delta>s i) (\<lambda>w s1 s2 statA sv1 sv2 statO. 
          \<Delta>s i w s1 s2 statA sv1 sv2 statO \<or> 
          \<Delta>s (Suc i) w s1 s2 statA sv1 sv2 statO))"
and finish: "unwindIntoCond (\<Delta>s m) (\<Delta>s m)"
shows rsecure
apply(rule distrib_unwind_rsecure[of "Suc m" "\<lambda>i. if i<m then {i,Suc i} else {i}" \<Delta>s, OF _ _ init]) 
using step finish 
by (auto simp: less_Suc_eq_le)

(* *)

definition oor where 
"oor \<Delta> \<Delta>\<^sub>2 \<equiv> \<lambda>w s1 s2 statA sv1 sv2 statO. 
  \<Delta> w s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO"

lemma oorI1: 
"\<Delta> w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor \<Delta> \<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO"
unfolding oor_def by simp

lemma oorI2: 
"\<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor \<Delta> \<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO"
unfolding oor_def by simp

definition oor3 where 
"oor3 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<equiv> \<lambda>w s1 s2 statA sv1 sv2 statO. 
  \<Delta> w s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO"

lemma oor3I1: 
"\<Delta> w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor3 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO"
unfolding oor3_def by simp

lemma oor3I2: 
"\<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor3 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO"
unfolding oor3_def by simp

lemma oor3I3: 
"\<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor3 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO"
unfolding oor3_def by simp

definition oor4 where 
"oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<equiv> \<lambda>w s1 s2 statA sv1 sv2 statO. 
  \<Delta> w s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO"

lemma oor4I1: 
"\<Delta> w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO"
unfolding oor4_def by simp

lemma oor4I2: 
"\<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO"
unfolding oor4_def by simp

lemma oor4I3: 
"\<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO"
unfolding oor4_def by simp

lemma oor4I4: 
"\<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor4 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO"
  unfolding oor4_def by simp

definition oor5 where 
"oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 \<equiv> \<lambda>w s1 s2 statA sv1 sv2 statO. 
  \<Delta> w s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>5 w s1 s2 statA sv1 sv2 statO"

lemma oor5I1: 
"\<Delta> w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w s1 s2 statA sv1 sv2 statO"
unfolding oor5_def by simp

lemma oor5I2: 
"\<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w s1 s2 statA sv1 sv2 statO"
unfolding oor5_def by simp

lemma oor5I3: 
"\<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w s1 s2 statA sv1 sv2 statO"
unfolding oor5_def by simp

lemma oor5I4: 
"\<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w s1 s2 statA sv1 sv2 statO"
unfolding oor5_def by simp

lemma oor5I5: 
"\<Delta>\<^sub>5 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor5 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 w s1 s2 statA sv1 sv2 statO"
  unfolding oor5_def by simp

definition oor6 where 
"oor6 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 \<Delta>\<^sub>6 \<equiv> \<lambda>w s1 s2 statA sv1 sv2 statO. 
  \<Delta> w s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO \<or> 
  \<Delta>\<^sub>5 w s1 s2 statA sv1 sv2 statO \<or> \<Delta>\<^sub>6 w s1 s2 statA sv1 sv2 statO"

lemma oor6I1: 
"\<Delta> w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor6 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 \<Delta>\<^sub>6 w s1 s2 statA sv1 sv2 statO"
unfolding oor6_def by simp

lemma oor6I2: 
"\<Delta>\<^sub>2 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor6 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 \<Delta>\<^sub>6 w s1 s2 statA sv1 sv2 statO"
unfolding oor6_def by simp

lemma oor6I3: 
"\<Delta>\<^sub>3 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor6 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 \<Delta>\<^sub>6 w s1 s2 statA sv1 sv2 statO"
unfolding oor6_def by simp

lemma oor6I4: 
"\<Delta>\<^sub>4 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor6 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 \<Delta>\<^sub>6 w s1 s2 statA sv1 sv2 statO"
unfolding oor6_def by simp

lemma oor6I5: 
"\<Delta>\<^sub>5 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor6 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 \<Delta>\<^sub>6 w s1 s2 statA sv1 sv2 statO"
unfolding oor6_def by simp

lemma oor6I6: 
"\<Delta>\<^sub>6 w s1 s2 statA sv1 sv2 statO \<Longrightarrow> oor6 \<Delta> \<Delta>\<^sub>2 \<Delta>\<^sub>3 \<Delta>\<^sub>4 \<Delta>\<^sub>5 \<Delta>\<^sub>6 w s1 s2 statA sv1 sv2 statO"
unfolding oor6_def by simp


(* *)

lemma unwind_rsecure_foo:
  assumes init: "initCond \<Delta>\<^sub>0" 
      and step0: "unwindIntoCond \<Delta>\<^sub>0 \<Delta>NN" 
      and stepNN: "unwindIntoCond \<Delta>NN (oor5 \<Delta>NN \<Delta>SN \<Delta>NS \<Delta>SS \<Delta>nonspec)"
      and stepNS: "unwindIntoCond \<Delta>NS (oor4 \<Delta>NN \<Delta>SN \<Delta>NS \<Delta>SS)"
      and stepSN: "unwindIntoCond \<Delta>SN (oor4 \<Delta>NN \<Delta>SN \<Delta>NS \<Delta>SS)"
      and stepSS: "unwindIntoCond \<Delta>SS (oor4 \<Delta>NN \<Delta>SN \<Delta>NS \<Delta>SS)"
      and stepNonspec: "unwindIntoCond \<Delta>nonspec \<Delta>nonspec" 
    shows rsecure
proof-
  define m where m: "m \<equiv> (6::nat)"
  define \<Delta>s where \<Delta>s: "\<Delta>s \<equiv> \<lambda>i::nat. 
  if i = 0 then \<Delta>\<^sub>0
  else if i = 1 then \<Delta>NN  
  else if i = 2 then \<Delta>SN 
  else if i = 3 then \<Delta>NS 
  else if i = 4 then \<Delta>SS
  else \<Delta>nonspec" 
  define nxt where nxt: "nxt \<equiv> \<lambda>i::nat. 
  if i = 0 then {1::nat}
  else if i = 1 then {1,2,3,4,5}  
  else if i = 2 then {1,2,3,4} 
  else if i = 3 then {1,2,3,4}  
  else if i = 4 then {1,2,3,4} 
  else {5}"
  show ?thesis apply(rule distrib_unwind_rsecure[of m nxt \<Delta>s])
    subgoal unfolding m by auto
    subgoal unfolding nxt m by auto
    subgoal using init unfolding \<Delta>s by auto
    subgoal 
      unfolding m nxt \<Delta>s  
      using step0 stepNN stepNS stepSN stepSS stepNonspec
      unfolding oor4_def oor5_def by auto .
qed

(* *)

lemma isIntO_match1: "isIntO s1 \<Longrightarrow> match1 \<Delta> s1 s2 statA sv1 sv2 statO"
unfolding match1_def by auto

lemma isIntO_match2: "isIntO s2 \<Longrightarrow> match2 \<Delta> s1 s2 statA sv1 sv2 statO"
unfolding match2_def by auto

(* *)

lemma match1_1_oorI1: 
"match1_1 \<Delta> s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> 
 match1_1 (oor \<Delta> \<Delta>\<^sub>2) s1 s1' s2 statA sv1 sv2 statO"
apply(rule match1_1_mono) unfolding le_fun_def oor_def by auto

lemma match1_1_oorI2: 
"match1_1 \<Delta>\<^sub>2 s1 s1' s2 statA sv1 sv2 statO \<Longrightarrow> 
 match1_1 (oor \<Delta> \<Delta>\<^sub>2) s1 s1' s2 statA sv1 sv2 statO"
apply(rule match1_1_mono) unfolding le_fun_def oor_def by auto

lemma match1_oorI1: 
"match1 \<Delta> s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match1 (oor \<Delta> \<Delta>\<^sub>2) s1 s2 statA sv1 sv2 statO"
apply(rule match1_mono) unfolding le_fun_def oor_def by auto

lemma match1_oorI2: 
"match1 \<Delta>\<^sub>2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match1 (oor \<Delta> \<Delta>\<^sub>2) s1 s2 statA sv1 sv2 statO"
apply(rule match1_mono) unfolding le_fun_def oor_def by auto

(* *)

lemma match2_1_oorI1: 
"match2_1 \<Delta> s1 s2 s2' statA sv1 sv2 statO \<Longrightarrow> 
 match2_1 (oor \<Delta> \<Delta>\<^sub>2) s1 s2 s2' statA sv1 sv2 statO"
apply(rule match2_1_mono) unfolding le_fun_def oor_def by auto

lemma match2_1_oorI2: 
"match2_1 \<Delta>\<^sub>2 s1 s2 s2' statA sv1 sv2 statO \<Longrightarrow> 
 match2_1 (oor \<Delta> \<Delta>\<^sub>2) s1 s2 s2' statA sv1 sv2 statO"
apply(rule match2_1_mono) unfolding le_fun_def oor_def by auto

lemma match2_oorI1: 
"match2 \<Delta> s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match2 (oor \<Delta> \<Delta>\<^sub>2) s1 s2 statA sv1 sv2 statO"
apply(rule match2_mono) unfolding le_fun_def oor_def by auto

lemma match2_oorI2: 
"match2 \<Delta>\<^sub>2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match2 (oor \<Delta> \<Delta>\<^sub>2) s1 s2 statA sv1 sv2 statO"
apply(rule match2_mono) unfolding le_fun_def oor_def by auto

(* *)

lemma match12_oorI1: 
"match12 \<Delta> s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match12 (oor \<Delta> \<Delta>\<^sub>2) s1 s2 statA sv1 sv2 statO"
apply(rule match12_mono) unfolding le_fun_def oor_def by auto

lemma match12_oorI2: 
"match12 \<Delta>\<^sub>2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 match12 (oor \<Delta> \<Delta>\<^sub>2) s1 s2 statA sv1 sv2 statO"
apply(rule match12_mono) unfolding le_fun_def oor_def by auto

lemma match12_1_oorI1: 
"match12_1 \<Delta> s1' s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_1 (oor \<Delta> \<Delta>\<^sub>2) s1' s2' statA' sv1 sv2 statO"
apply(rule match12_1_mono) unfolding le_fun_def oor_def by auto

lemma match12_1_oorI2: 
"match12_1 \<Delta>\<^sub>2 s1' s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_1 (oor \<Delta> \<Delta>\<^sub>2) s1' s2' statA' sv1 sv2 statO"
apply(rule match12_1_mono) unfolding le_fun_def oor_def by auto

lemma match12_2_oorI1: 
"match12_2 \<Delta> s2 s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_2 (oor \<Delta> \<Delta>\<^sub>2) s2 s2' statA' sv1 sv2 statO"
apply(rule match12_2_mono) unfolding le_fun_def oor_def by auto

lemma match12_2_oorI2: 
"match12_2 \<Delta>\<^sub>2 s2 s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_2 (oor \<Delta> \<Delta>\<^sub>2) s2 s2' statA' sv1 sv2 statO"
apply(rule match12_2_mono) unfolding le_fun_def oor_def by auto

lemma match12_12_oorI1: 
"match12_12 \<Delta> s1' s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_12 (oor \<Delta> \<Delta>\<^sub>2) s1' s2' statA' sv1 sv2 statO"
apply(rule match12_12_mono) unfolding le_fun_def oor_def by auto

lemma match12_12_oorI2: 
"match12_12 \<Delta>\<^sub>2 s1' s2' statA' sv1 sv2 statO \<Longrightarrow> 
 match12_12 (oor \<Delta> \<Delta>\<^sub>2) s1' s2' statA' sv1 sv2 statO"
apply(rule match12_12_mono) unfolding le_fun_def oor_def by auto

(* *)

lemma match_oorI1: 
"react \<Delta> s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 react (oor \<Delta> \<Delta>\<^sub>2) s1 s2 statA sv1 sv2 statO"
apply(rule match_mono) unfolding le_fun_def oor_def by auto

lemma match_oorI2: 
"react \<Delta>\<^sub>2 s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 react (oor \<Delta> \<Delta>\<^sub>2) s1 s2 statA sv1 sv2 statO"
apply(rule match_mono) unfolding le_fun_def oor_def by auto

(* *)

lemma proact_oorI1: 
"proact \<Delta> meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 proact (oor \<Delta> \<Delta>\<^sub>2) meas  s1 s2 statA sv1 sv2 statO"
apply(rule proact_mono) unfolding le_fun_def oor_def by auto

lemma proact_oorI2: 
"proact \<Delta>\<^sub>2 meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 proact (oor \<Delta> \<Delta>\<^sub>2) meas  s1 s2 statA sv1 sv2 statO"
apply(rule proact_mono) unfolding le_fun_def oor_def by auto

lemma move_1_oorI1: 
"move_1 \<Delta> meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_1 (oor \<Delta> \<Delta>\<^sub>2) meas  s1 s2 statA sv1 sv2 statO"
apply(rule move_1_mono) unfolding le_fun_def oor_def by auto

lemma move_1_oorI2: 
"move_1 \<Delta>\<^sub>2 meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_1 (oor \<Delta> \<Delta>\<^sub>2) meas  s1 s2 statA sv1 sv2 statO"
apply(rule move_1_mono) unfolding le_fun_def oor_def by auto

lemma move_2_oorI1: 
"move_2 \<Delta> meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_2 (oor \<Delta> \<Delta>\<^sub>2) meas  s1 s2 statA sv1 sv2 statO"
apply(rule move_2_mono) unfolding le_fun_def oor_def by auto

lemma move_2_oorI2: 
"move_2 \<Delta>\<^sub>2 meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_2 (oor \<Delta> \<Delta>\<^sub>2) meas  s1 s2 statA sv1 sv2 statO"
apply(rule move_2_mono) unfolding le_fun_def oor_def by auto

lemma move_12_oorI1: 
"move_12 \<Delta> meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_12 (oor \<Delta> \<Delta>\<^sub>2) meas  s1 s2 statA sv1 sv2 statO"
apply(rule move_12_mono) unfolding le_fun_def oor_def by auto

lemma move_12_oorI2: 
"move_12 \<Delta>\<^sub>2 meas s1 s2 statA sv1 sv2 statO \<Longrightarrow> 
 move_12 (oor \<Delta> \<Delta>\<^sub>2) meas  s1 s2 statA sv1 sv2 statO"
apply(rule move_12_mono) unfolding le_fun_def oor_def by auto

end (* context Relative_Security *)


context Relative_Security_Determ
begin 

lemma match1_1_defD: "match1_1 \<Delta> s1 s1' s2 statA sv1 sv2 statO \<longleftrightarrow>         
    \<not> finalV sv1 \<and> \<Delta> \<infinity> s1' s2 statA (nextO sv1) sv2 statO"
unfolding match1_1_def validTrans_iff_next by simp

lemma match1_12_defD: "match1_12 \<Delta> s1 s1' s2 statA sv1 sv2 statO \<longleftrightarrow>  
  \<not> finalV sv1 \<and> \<not> finalV sv2 \<and>     
  \<Delta> \<infinity> s1' s2 statA (nextO sv1) (nextO sv2) (sstatO' statO sv1 sv2)"
unfolding match1_12_def validTrans_iff_next by simp

lemmas match1_defsD = match1_def match1_1_defD match1_12_defD

(*  *)

lemma match2_1_defD: "match2_1 \<Delta> s1 s2 s2' statA sv1 sv2 statO \<longleftrightarrow> 
  \<not> finalV sv2 \<and> \<Delta> \<infinity> s1 s2' statA sv1 (nextO sv2) statO"
unfolding match2_1_def validTrans_iff_next by simp

lemma match2_12_defD: "match2_12 \<Delta> s1 s2 s2' statA sv1 sv2 statO \<longleftrightarrow> 
  \<not> finalV sv1 \<and> \<not> finalV sv2 \<and> \<Delta> \<infinity> s1 s2' statA (nextO sv1) (nextO sv2) (sstatO' statO sv1 sv2)"
unfolding match2_12_def validTrans_iff_next by simp

lemmas match2_defsD = match2_def match2_1_defD match2_12_defD

(* *)

lemma match12_1_defD: "match12_1 \<Delta> s1' s2' statA' sv1 sv2 statO \<longleftrightarrow>  
 \<not> finalV sv1 \<and> \<Delta> \<infinity> s1' s2' statA' (nextO sv1) sv2 statO"
unfolding match12_1_def validTrans_iff_next by simp

lemma match12_2_defD: "match12_2 \<Delta> s1' s2' statA' sv1 sv2 statO \<longleftrightarrow>  
  \<not> finalV sv2 \<and> \<Delta> \<infinity> s1' s2' statA' sv1 (nextO sv2) statO"
unfolding match12_2_def validTrans_iff_next by simp

lemma match12_12_defD: "match12_12 \<Delta> s1' s2' statA' sv1 sv2 statO \<longleftrightarrow>  
    (let statO' = sstatO' statO sv1 sv2 in 
    \<not> finalV sv1 \<and> \<not> finalV sv2 \<and>   
    (statA' = Diff \<longrightarrow> statO' = Diff) \<and>       
    \<Delta> \<infinity> s1' s2' statA' (nextO sv1) (nextO sv2) statO')"
unfolding match12_12_def validTrans_iff_next by simp

lemmas match12_defsD = match12_def match12_1_defD match12_2_defD match12_12_defD

lemmas match_deep_defsD = match1_defsD match2_defsD match12_defsD

(* *)

lemma move_1_defD: "move_1 \<Delta> w s1 s2 statA sv1 sv2 statO \<longleftrightarrow> 
   \<not> finalV sv1 \<and> \<Delta> w s1 s2 statA (nextO sv1) sv2 statO"
unfolding move_1_def validTrans_iff_next by simp

lemma move_2_defD: "move_2 \<Delta> w s1 s2 statA sv1 sv2 statO \<longleftrightarrow>  
   \<not> finalV sv2 \<and> \<Delta> w s1 s2 statA sv1 (nextO sv2) statO"
unfolding move_2_def validTrans_iff_next by simp

lemma move_12_defD: "move_12 \<Delta> w s1 s2 statA sv1 sv2 statO \<longleftrightarrow>  
   (let statO' = sstatO' statO sv1 sv2 in 
   \<not> finalV sv1 \<and> \<not> finalV sv2 \<and>     
   \<Delta> w s1 s2 statA (nextO sv1) (nextO sv2) statO')" 
unfolding move_12_def validTrans_iff_next by simp

lemmas proact_defsD = proact_def move_1_defD move_2_defD move_12_defD

end (* context Relative_Security_Determ *)


end 