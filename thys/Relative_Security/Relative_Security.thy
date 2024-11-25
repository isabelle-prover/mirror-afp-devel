section \<open>Relative Security\<close>

text \<open> This theory formalizes the general notion of relative security, 
applicable to possibly infinite traces.  \<close>


theory Relative_Security
imports Relative_Security_fin "Preliminaries/Trivia"
begin

no_notation relcomp (infixr "O" 75)
no_notation relcompp (infixr "OO" 75)


subsection \<open>Leakage models and attacker models \<close>

(* Everything extended to lazy lists (possibly infinite traces) has prefix "l". *)

locale Leakage_Mod = System_Mod istate validTrans final
for istate :: "'state \<Rightarrow> bool" and validTrans :: "'state \<times> 'state \<Rightarrow> bool" and final :: "'state \<Rightarrow> bool"
+
fixes lleakVia :: "'state llist \<Rightarrow> 'state llist \<Rightarrow> 'leak \<Rightarrow> bool" 


locale Attacker_Mod = System_Mod istate validTrans final
for istate :: "'state \<Rightarrow> bool" and validTrans :: "'state \<times> 'state \<Rightarrow> bool" and final :: "'state \<Rightarrow> bool"
+
fixes S :: "'state llist \<Rightarrow> 'secret llist"
and A :: "'state ltrace \<Rightarrow> 'act llist" 
and O :: "'state ltrace \<Rightarrow> 'obs llist"
begin

fun lleakVia :: "'state llist \<Rightarrow> 'state llist \<Rightarrow> 'secret llist \<times> 'secret llist \<Rightarrow> bool" 
where 
"lleakVia tr tr' (sl,sl') = (S tr = sl \<and> S tr' = sl' \<and> A tr = A tr' \<and> O tr \<noteq> O tr')"

lemmas lleakVia_def = lleakVia.simps 

end 

sublocale Attacker_Mod < Leakage_Mod 
where lleakVia = lleakVia
by standard 


subsection \<open>Locales for increasingly concrete notions of relative security \<close>

(* Very abstract relative security, based on leakage models (as in the paper's section 2.3) *)
locale Relative_Security'' = 
  Van: Leakage_Mod istateV validTransV finalV lleakViaV
+
  Opt: Leakage_Mod istateO validTransO finalO lleakViaO
  for validTransV :: "'stateV \<times> 'stateV \<Rightarrow> bool"
  and istateV :: "'stateV \<Rightarrow> bool" and finalV :: "'stateV \<Rightarrow> bool"
  and lleakViaV :: "'stateV llist \<Rightarrow> 'stateV llist \<Rightarrow> 'leak \<Rightarrow> bool"   
  (* NB: we have the same notion of secret, but everything else can be different  *)
  and validTransO :: "'stateO \<times> 'stateO \<Rightarrow> bool"
  and istateO :: "'stateO \<Rightarrow> bool" and finalO :: "'stateO \<Rightarrow> bool"
  and lleakViaO :: "'stateO llist \<Rightarrow> 'stateO llist \<Rightarrow> 'leak \<Rightarrow> bool"  
  (* We also parameterize the relative security notion by a "corresponding state" 
  relationship between states, which in the examples so far has always been taken to 
  be vacuously true. 
  *)
  and corrState :: "'stateV \<Rightarrow> 'stateO \<Rightarrow> bool"
begin


definition lrsecure :: bool where 
"lrsecure \<equiv> \<forall>l s1 tr1 s2 tr2. 
   istateO s1 \<and> Opt.lvalidFromS s1 tr1 \<and> Opt.lcompletedFrom s1 tr1 \<and> 
   istateO s2 \<and> Opt.lvalidFromS s2 tr2 \<and> Opt.lcompletedFrom s2 tr2 \<and>  
   lleakViaO tr1 tr2 l 
   \<longrightarrow> 
   (\<exists>sv1 trv1 sv2 trv2. 
      istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 \<and> 
      Van.lvalidFromS sv1 trv1 \<and> Van.lcompletedFrom sv1 trv1 \<and> 
      Van.lvalidFromS sv2 trv2 \<and> Van.lcompletedFrom sv2 trv2 \<and>  
      lleakViaV trv1 trv2 l)"

end (* context Relative_Security'' *)



(* Less abstract relative security, instantiated to attacker models (as in the paper's section 2.4) *)
locale Relative_Security' = 
  Van: Attacker_Mod istateV validTransV finalV SV AV OV 
+
  Opt: Attacker_Mod istateO validTransO finalO SO AO OO 
  for validTransV :: "'stateV \<times> 'stateV \<Rightarrow> bool"
  and istateV :: "'stateV \<Rightarrow> bool" and finalV :: "'stateV \<Rightarrow> bool"
  and SV :: "'stateV llist \<Rightarrow> 'secret llist"
  and AV :: "'stateV ltrace \<Rightarrow> 'actV llist" 
  and OV :: "'stateV ltrace \<Rightarrow> 'obsV llist"
  (* NB: we have the same notion of secret, but everything else can be different  *)
  and validTransO :: "'stateO \<times> 'stateO \<Rightarrow> bool"
  and istateO :: "'stateO \<Rightarrow> bool" and finalO :: "'stateO \<Rightarrow> bool"
  and SO :: "'stateO llist \<Rightarrow> 'secret llist"
  and AO :: "'stateO ltrace \<Rightarrow> 'actO llist" 
  and OO :: "'stateO ltrace \<Rightarrow> 'obsO llist"
  and corrState :: "'stateV \<Rightarrow> 'stateO \<Rightarrow> bool"

sublocale Relative_Security' <  Relative_Security''  
where lleakViaV = Van.lleakVia and lleakViaO = Opt.lleakVia 
by standard


context Relative_Security'
begin

(* For attacker models, relative security has the following more intuitive formulation 
(expression (\<star>) from the paper's section 2.4) *)

lemma lrsecure_def2:
"lrsecure \<longleftrightarrow> 
 (\<forall>s1 tr1 s2 tr2.
     istateO s1 \<and> Opt.lvalidFromS s1 tr1 \<and> Opt.lcompletedFrom s1 tr1 \<and> 
     istateO s2 \<and> Opt.lvalidFromS s2 tr2 \<and> Opt.lcompletedFrom s2 tr2 \<and> 
     AO tr1 = AO tr2 \<and> OO tr1 \<noteq> OO tr2
     \<longrightarrow>
     (\<exists>sv1 trv1 sv2 trv2. 
        istateV sv1 \<and> istateV sv2 \<and> corrState sv1 s1 \<and> corrState sv2 s2 \<and> 
        Van.lvalidFromS sv1 trv1 \<and> Van.lcompletedFrom sv1 trv1 \<and> 
        Van.lvalidFromS sv2 trv2 \<and> Van.lcompletedFrom sv2 trv2 \<and> 
        SV trv1 = SO tr1 \<and> SV trv2 = SO tr2 \<and> 
        AV trv1 = AV trv2 \<and> OV trv1 \<noteq> OV trv2))" 
unfolding lrsecure_def 
unfolding Van.lleakVia_def Opt.lleakVia_def
by auto metis

end (* context Relative_Security' *)



context Statewise_Attacker_Mod begin

(* Infinitary (lazy list) versions of the operators: *)

(* The action function: *)
definition lA :: "'state ltrace \<Rightarrow> 'act llist" where 
"lA tr \<equiv> lfiltermap isInt getAct (lbutlast tr)"

sublocale lA: LfiltermapBL isInt getAct lA
  apply standard unfolding lA_def ..

lemma lA: "lcompletedFrom s tr \<Longrightarrow> lA tr = lmap getAct (lfilter isInt tr)"
apply(cases "lfinite tr")
  subgoal unfolding lA.lmap_lfilter lbutlast_def  
  by simp (metis final_not_isInt lbutlast_lfinite lcompletedFrom_def lfilter_llist_of lfiltermap_lmap_lfilter lfinite_lfiltermap_butlast llast_llist_of llist_of_list_of lmap_llist_of)
  subgoal unfolding lA.lmap_lfilter lbutlast_def by auto .

(* The observation function: *)
definition lO :: "'state ltrace \<Rightarrow> 'obs llist" where  
"lO tr \<equiv> lfiltermap isInt getObs (lbutlast tr)"

(* lemma lO_LfiltermapBL: \<open>LfiltermapBL isInt getObs lO\<close>
  unfolding lO_def by (standard, auto)
*)

sublocale lO: LfiltermapBL isInt getObs lO
  apply standard unfolding lO_def ..

lemma lO: "lcompletedFrom s tr \<Longrightarrow> lO tr = lmap getObs (lfilter isInt tr)"
apply(cases "lfinite tr")
  subgoal unfolding lO.lmap_lfilter lbutlast_def 
  by simp (metis List_Filtermap.filtermap_def butlast.simps(1) filtermap_butlast final_not_isInt lcompletedFrom_def lfilter_llist_of llist_of_list_of lmap_llist_of)
  subgoal unfolding lO.lmap_lfilter lbutlast_def by auto .

(* The secrecy function: *)
definition lS :: "'state llist \<Rightarrow> 'secret llist" where 
"lS tr \<equiv> lfiltermap isSec getSec (lbutlast tr)"

sublocale lS: LfiltermapBL isSec getSec lS
  apply standard unfolding lS_def ..

lemma lS: "lcompletedFrom s tr \<Longrightarrow> lS tr = lmap getSec (lfilter isSec tr)"
apply(cases "lfinite tr")
  subgoal unfolding lS.lmap_lfilter lbutlast_def 
  by simp (metis List_Filtermap.filtermap_def filtermap_butlast final_not_isSec lcompletedFrom_def lfilter_llist_of llist_of_eq_LNil_conv llist_of_list_of lmap_llist_of)
  subgoal unfolding lS.lmap_lfilter lbutlast_def by auto .


end (* context Statewise_Attacker_Mod *)


sublocale Statewise_Attacker_Mod < Attacker_Mod 
where S = lS and A = lA and O = lO
by standard


sublocale Rel_Sec < Relative_Security'
where SV = Van.lS and AV = Van.lA and OV = Van.lO
and SO = Opt.lS and AO = Opt.lA and OO = Opt.lO
by standard



context Rel_Sec 
begin 

abbreviation lcompletedFromV :: "'stateV \<Rightarrow> 'stateV llist \<Rightarrow> bool" where "lcompletedFromV \<equiv> Van.lcompletedFrom"
abbreviation lcompletedFromO :: "'stateO \<Rightarrow> 'stateO llist \<Rightarrow> bool" where "lcompletedFromO \<equiv> Opt.lcompletedFrom"


lemma eqSec_lS_Cons': 
"eqSec trnO trnA \<Longrightarrow> 
 (Van.lS (trnO $ trO') = Opt.lS (trnA $ trA')) \<Longrightarrow> Van.lS trO' = Opt.lS trA'"
apply(cases "trO' = [[]]")
  subgoal apply(cases "trA' = [[]]")
    subgoal by auto
    subgoal unfolding eqSec_def by auto .
  subgoal apply(cases "trA' = [[]]")
    subgoal by auto
    subgoal unfolding eqSec_def by auto . .

lemma eqSec_lS_Cons[simp]: 
"eqSec trnO trnA \<Longrightarrow> trO' = [[]] \<longleftrightarrow> trA' = [[]] \<Longrightarrow>
 (Van.lS (trnO $ trO') = Opt.lS (trnA $ trA')) \<longleftrightarrow> (Van.lS trO' = Opt.lS trA')"
apply(cases "trO' = [[]]")
  subgoal apply(cases "trA' = [[]]")
    subgoal by auto
    subgoal unfolding eqSec_def by auto .
  subgoal apply(cases "trA' = [[]]")
    subgoal by auto 
    subgoal unfolding eqSec_def by auto . .

end (* context Relative_Security *)

end 