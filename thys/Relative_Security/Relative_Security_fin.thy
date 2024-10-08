section \<open>Finitary Relative Security\<close>

text \<open> This theory formalizes the finitary version of relative security, 
more precisely the notion expressed in terms of finite traces.  \<close>


theory Relative_Security_fin
imports "Preliminaries/Transition_System" 
begin

declare Let_def[simp]

unbundle no relcomp_syntax


subsection \<open>Finite-trace versions of leakage models and attacker models \<close>

locale Leakage_Mod_fin = System_Mod istate validTrans final
for istate :: "'state \<Rightarrow> bool" and validTrans :: "'state \<times> 'state \<Rightarrow> bool" and final :: "'state \<Rightarrow> bool"
+
fixes S :: "'state list \<Rightarrow> 'secret list"
and A :: "'state trace \<Rightarrow> 'act list" 
and O :: "'state trace \<Rightarrow> 'obs list"
and leakVia :: "'state list \<Rightarrow> 'state list \<Rightarrow> 'leak \<Rightarrow> bool" 


locale Attacker_Mod_fin = System_Mod istate validTrans final
for istate :: "'state \<Rightarrow> bool" and validTrans :: "'state \<times> 'state \<Rightarrow> bool" and final :: "'state \<Rightarrow> bool"
+
fixes S :: "'state list \<Rightarrow> 'secret list"
and A :: "'state trace \<Rightarrow> 'act list" 
and O :: "'state trace \<Rightarrow> 'obs list"
begin

fun leakVia :: "'state list \<Rightarrow> 'state list \<Rightarrow> 'secret list \<times> 'secret list \<Rightarrow> bool" 
where 
"leakVia tr tr' (sl,sl') = (S tr = sl \<and> S tr' = sl' \<and> A tr = A tr' \<and> O tr \<noteq> O tr')"

lemmas leakVia_def = leakVia.simps 

end 

sublocale Attacker_Mod_fin < Leakage_Mod_fin 
where leakVia = leakVia
by standard 


subsection \<open>Locales for increasingly concrete notions of finitary relative security \<close>

(* Very abstract relative security, based on leakage models (as in the paper's section 2.3) *)
locale Relative_Security''_fin = 
  Van: Leakage_Mod_fin istateV validTransV finalV SV AV OV leakViaV
+
  Opt: Leakage_Mod_fin istateO validTransO finalO SO AO OO leakViaO
  for validTransV :: "'stateV \<times> 'stateV \<Rightarrow> bool"
  and istateV :: "'stateV \<Rightarrow> bool" and finalV :: "'stateV \<Rightarrow> bool"
  and SV :: "'stateV list \<Rightarrow> 'secret list"
  and AV :: "'stateV trace \<Rightarrow> 'actV list" 
  and OV :: "'stateV trace \<Rightarrow> 'obsV list"
  and leakViaV :: "'stateV list \<Rightarrow> 'stateV list \<Rightarrow> 'leak \<Rightarrow> bool"   
  (* NB: we have the same notion of secret, but everything else can be different  *)
  and validTransO :: "'stateO \<times> 'stateO \<Rightarrow> bool"
  and istateO :: "'stateO \<Rightarrow> bool" and finalO :: "'stateO \<Rightarrow> bool"
  and SO :: "'stateO list \<Rightarrow> 'secret list"
  and AO :: "'stateO trace \<Rightarrow> 'actO list" 
  and OO :: "'stateO trace \<Rightarrow> 'obsO list"
  and leakViaO :: "'stateO list \<Rightarrow> 'stateO list \<Rightarrow> 'leak \<Rightarrow> bool"  
  (* We also parameterize the relative security notion by a "corresponding state" 
  relationship between states, which in the examples so far has always been taken to 
  be vacuously true. *)
  and corrState :: "'stateV \<Rightarrow> 'stateO \<Rightarrow> bool"
begin

definition rsecure :: bool where 
"rsecure \<equiv> \<forall>l s1 tr1 s2 tr2. 
   istateO s1 \<and> Opt.validFromS s1 tr1 \<and> Opt.completedFrom s1 tr1 \<and> 
   istateO s2 \<and> Opt.validFromS s2 tr2 \<and> Opt.completedFrom s2 tr2 \<and>  
   leakViaO tr1 tr2 l 
   \<longrightarrow> 
   (\<exists>sv1 trv1 sv2 trv2. 
      istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 \<and> 
      Van.validFromS sv1 trv1 \<and> Van.completedFrom sv1 trv1 \<and> 
      Van.validFromS sv2 trv2 \<and> Van.completedFrom sv2 trv2 \<and>  
      leakViaV trv1 trv2 l)"

end (* context Relative_Security'' *)

(* Less abstract relative security, instantiated to attacker models (as in the paper's section 2.4) *)
locale Relative_Security'_fin = 
  Van: Attacker_Mod_fin istateV validTransV finalV SV AV OV 
+
  Opt: Attacker_Mod_fin istateO validTransO finalO SO AO OO 
  for validTransV :: "'stateV \<times> 'stateV \<Rightarrow> bool"
  and istateV :: "'stateV \<Rightarrow> bool" and finalV :: "'stateV \<Rightarrow> bool"
  and SV :: "'stateV list \<Rightarrow> 'secret list"
  and AV :: "'stateV trace \<Rightarrow> 'actV list" 
  and OV :: "'stateV trace \<Rightarrow> 'obsV list"
  (* NB: we have the same notion of secret, but everything else can be different  *)
  and validTransO :: "'stateO \<times> 'stateO \<Rightarrow> bool"
  and istateO :: "'stateO \<Rightarrow> bool" and finalO :: "'stateO \<Rightarrow> bool"
  and SO :: "'stateO list \<Rightarrow> 'secret list"
  and AO :: "'stateO trace \<Rightarrow> 'actO list" 
  and OO :: "'stateO trace \<Rightarrow> 'obsO list"
  and corrState :: "'stateV \<Rightarrow> 'stateO \<Rightarrow> bool"

sublocale Relative_Security'_fin <  Relative_Security''_fin  
where leakViaV = Van.leakVia and leakViaO = Opt.leakVia 
by standard


context Relative_Security'_fin
begin

(* For attacker models, relative security has the following more intuitive formulation 
(expression (\<star>) from the paper's section 2.4) *)

lemma rsecure_def2:
"rsecure \<longleftrightarrow> 
 (\<forall>s1 tr1 s2 tr2.
     istateO s1 \<and> Opt.validFromS s1 tr1 \<and> Opt.completedFrom s1 tr1 \<and> 
     istateO s2 \<and> Opt.validFromS s2 tr2 \<and> Opt.completedFrom s2 tr2 \<and> 
     AO tr1 = AO tr2 \<and> OO tr1 \<noteq> OO tr2
     \<longrightarrow>
     (\<exists>sv1 trv1 sv2 trv2. 
        istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 \<and> 
        Van.validFromS sv1 trv1 \<and> Van.completedFrom sv1 trv1 \<and> 
        Van.validFromS sv2 trv2 \<and> Van.completedFrom sv2 trv2 \<and> 
        SV trv1 = SO tr1 \<and> SV trv2 = SO tr2 \<and> 
        AV trv1 = AV trv2 \<and> OV trv1 \<noteq> OV trv2))" 
unfolding rsecure_def 
unfolding Van.leakVia_def Opt.leakVia_def
by auto metis

end (* context Relative_Security'_fin *)


locale Statewise_Attacker_Mod = System_Mod istate validTrans final
 for istate :: "'state \<Rightarrow> bool" and validTrans :: "'state \<times> 'state \<Rightarrow> bool" and final :: "'state \<Rightarrow> bool"
+
fixes (* secret filtering and production:  *)
   isSec :: "'state \<Rightarrow> bool" and getSec :: "'state \<Rightarrow> 'secret"
 and (* interaction (action and/or observation) filtering and production: *)
   isInt :: "'state \<Rightarrow> bool" and getInt :: "'state \<Rightarrow> 'act \<times> 'obs"
assumes final_not_isInt: "\<And>s. final s \<Longrightarrow> \<not> isInt s"
and final_not_isSec: "\<And>s. final s \<Longrightarrow> \<not> isSec s"
begin


definition getAct :: "'state \<Rightarrow> 'act" where 
"getAct = fst o getInt" 

definition getObs :: "'state \<Rightarrow> 'obs" where 
"getObs = snd o getInt" 

definition "eqObs trn1 trn2 \<equiv> 
 (isInt trn1 \<longleftrightarrow> isInt trn2) \<and> (isInt trn1 \<longrightarrow> getObs trn1 = getObs trn2)"

definition "eqAct trn1 trn2 \<equiv> 
 (isInt trn1 \<longleftrightarrow> isInt trn2) \<and> (isInt trn1 \<longrightarrow> getAct trn1 = getAct trn2)"

(* THE VERSIONS FOR FINITE TRACES FIRST: *)
(* The action function: *)
definition A :: "'state trace \<Rightarrow> 'act list" where 
"A tr \<equiv> filtermap isInt getAct (butlast tr)"


sublocale A: FiltermapBL isInt getAct A
 apply standard unfolding A_def ..


(* The observation function: *)
definition O :: "'state trace \<Rightarrow> 'obs list" where  
"O tr \<equiv> filtermap isInt getObs (butlast tr)"

sublocale O: FiltermapBL isInt getObs O
  apply standard unfolding O_def ..


(* The secrecy function: *)
definition S :: "'state list \<Rightarrow> 'secret list" where 
"S tr \<equiv> filtermap isSec getSec (butlast tr)"

sublocale S: FiltermapBL isSec getSec S
  apply standard unfolding S_def ..

end (* context Statewise_Attacker_Mod *)


sublocale Statewise_Attacker_Mod < Attacker_Mod_fin 
where S = S and A = A and O = O
by standard

locale Rel_Sec = 
  Van: Statewise_Attacker_Mod istateV validTransV finalV isSecV getSecV isIntV getIntV
+
  Opt: Statewise_Attacker_Mod istateO validTransO finalO isSecO getSecO isIntO getIntO
  for validTransV :: "'stateV \<times> 'stateV \<Rightarrow> bool"
  and istateV :: "'stateV \<Rightarrow> bool" and finalV :: "'stateV \<Rightarrow> bool"
  and isSecV :: "'stateV \<Rightarrow> bool" and getSecV :: "'stateV \<Rightarrow> 'secret"
  and isIntV :: "'stateV \<Rightarrow> bool" and getIntV :: "'stateV \<Rightarrow> 'actV \<times> 'obsV"  
  (* NB: we have the same notion of secret, but everything else can be different  *)
  and validTransO :: "'stateO \<times> 'stateO \<Rightarrow> bool"
  and istateO :: "'stateO \<Rightarrow> bool" and finalO :: "'stateO \<Rightarrow> bool"
  and isSecO :: "'stateO \<Rightarrow> bool" and getSecO :: "'stateO \<Rightarrow> 'secret"
  and isIntO :: "'stateO \<Rightarrow> bool" and getIntO :: "'stateO \<Rightarrow> 'actO \<times> 'obsO" 
  (* We also parameterize the relative security notion by a "corresponding state" 
  relationship between states, which in the examples so far has always been taken to 
  be vacuously true. 
  *)
  and corrState :: "'stateV \<Rightarrow> 'stateO \<Rightarrow> bool"


sublocale Rel_Sec <  Relative_Security'_fin
where SV = Van.S and AV = Van.A and OV = Van.O
and SO = Opt.S and AO = Opt.A and OO = Opt.O
by standard


context Rel_Sec
begin 

abbreviation getObsV :: "'stateV \<Rightarrow> 'obsV" where "getObsV \<equiv> Van.getObs"
abbreviation getActV :: "'stateV \<Rightarrow> 'actV" where "getActV \<equiv> Van.getAct"
abbreviation getObsO :: "'stateO \<Rightarrow> 'obsO" where "getObsO \<equiv> Opt.getObs"
abbreviation getActO :: "'stateO \<Rightarrow> 'actO" where "getActO \<equiv> Opt.getAct"

abbreviation reachV where "reachV \<equiv> Van.reach"
abbreviation reachO where "reachO \<equiv> Opt.reach"

abbreviation completedFromV :: "'stateV \<Rightarrow> 'stateV list \<Rightarrow> bool" where "completedFromV \<equiv> Van.completedFrom"
abbreviation completedFromO :: "'stateO \<Rightarrow> 'stateO list \<Rightarrow> bool" where "completedFromO \<equiv> Opt.completedFrom"

lemmas completedFromV_def = Van.completedFrom_def
lemmas completedFromO_def = Opt.completedFrom_def

lemma rsecure_def3:
"rsecure \<longleftrightarrow> 
 (\<forall>s1 tr1 s2 tr2.
     istateO s1 \<and> Opt.validFromS s1 tr1 \<and> completedFromO s1 tr1 \<and> 
     istateO s2 \<and> Opt.validFromS s2 tr2 \<and> completedFromO s2 tr2 \<and> 
     Opt.A tr1 = Opt.A tr2 \<and> Opt.O tr1 \<noteq> Opt.O tr2 \<and> 
     (isIntO s1 \<and> isIntO s2 \<longrightarrow> getActO s1 = getActO s2)
     \<longrightarrow>
     (\<exists>sv1 trv1 sv2 trv2. 
        istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 \<and> 
        Van.validFromS sv1 trv1 \<and> completedFromV sv1 trv1 \<and> 
        Van.validFromS sv2 trv2 \<and> completedFromV sv2 trv2 \<and> 
        Van.S trv1 = Opt.S tr1 \<and> Van.S trv2 = Opt.S tr2 \<and> 
        Van.A trv1 = Van.A trv2 \<and> Van.O trv1 \<noteq> Van.O trv2))" 
  unfolding rsecure_def2 apply (intro iff_allI iffI impI)
  subgoal by auto
  subgoal  
  by clarsimp (metis (full_types) Opt.A.Cons_unfold 
     Opt.completed_Cons Opt.final_not_isInt 
       Simple_Transition_System.validFromS_Cons_iff 
    completedFromO_def list.sel(1) neq_Nil_conv) .

(* *)

definition "eqSec trnO trnA \<equiv> 
 (isSecV trnO = isSecO trnA) \<and> (isSecV trnO \<longrightarrow> getSecV trnO = getSecO trnA)"


lemma eqSec_S_Cons': 
"eqSec trnO trnA \<Longrightarrow> 
 (Van.S (trnO # trO') = Opt.S (trnA # trA')) \<Longrightarrow> Van.S trO' = Opt.S trA'"
apply(cases "trO' = []")
  subgoal apply(cases "trA' = []")
    subgoal by auto
    subgoal unfolding eqSec_def by auto .
  subgoal apply(cases "trA' = []")
    subgoal by auto
    subgoal unfolding eqSec_def by auto . .

lemma eqSec_S_Cons[simp]: 
"eqSec trnO trnA \<Longrightarrow> trO' = [] \<longleftrightarrow> trA' = [] \<Longrightarrow>
 (Van.S (trnO # trO') = Opt.S (trnA # trA')) \<longleftrightarrow> (Van.S trO' = Opt.S trA')"
apply(cases "trO' = []")
  subgoal apply(cases "trA' = []")
    subgoal by auto
    subgoal unfolding eqSec_def by auto .
  subgoal apply(cases "trA' = []")
    subgoal by auto 
    subgoal unfolding eqSec_def by auto . .

end (* context Relative_Security *)

(* DETERMINISTIC VERSION *)

(* Assuming the original transition system is deterministic: *)
locale Relative_Security_Determ = 
Rel_Sec  
  validTransV istateV finalV isSecV getSecV isIntV getIntV
  validTransO istateO finalO isSecO getSecO isIntO getIntO
  corrState
+
System_Mod_Deterministic istateV validTransV finalV nextO
  for validTransV :: "'stateV \<times> 'stateV \<Rightarrow> bool"
  and istateV :: "'stateV \<Rightarrow> bool"
  and finalV :: "'stateV \<Rightarrow> bool"
  and nextO :: "'stateV \<Rightarrow> 'stateV"
  and isSecV :: "'stateV \<Rightarrow> bool" and getSecV :: "'stateV \<Rightarrow> 'secret"
  and isIntV :: "'stateV \<Rightarrow> bool" and getIntV :: "'stateV \<Rightarrow> 'actV \<times> 'obsV"  
  and validTransO :: "'stateO \<times> 'stateO \<Rightarrow> bool"
  and istateO :: "'stateO \<Rightarrow> bool"
  and finalO :: "'stateO \<Rightarrow> bool"
  and isSecO :: "'stateO \<Rightarrow> bool" and getSecO :: "'stateO \<Rightarrow> 'secret"
  and isIntO :: "'stateO \<Rightarrow> bool" and getIntO :: "'stateO \<Rightarrow> 'actO \<times> 'obsO" 
  and corrState :: "'stateV \<Rightarrow> 'stateO \<Rightarrow> bool"


end


 