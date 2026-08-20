(*  Title:       Executable algorithms for finite state machines
    ID:
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section "Executable algorithms for finite state machines"

theory FSM_ex
imports FSM ImplHelper
begin

text \<open> The transition relation of a finite state machine is represented as a list of labeled edges \<close>
type_synonym ('s,'a) delta = "('s \<times> 'a \<times> 's) list"

subsection \<open> Word lookup operation \<close>
text \<open>
  Operation that finds some state @{term "q'"} that is reachable from state @{term q} with word @{term w} and has additional property @{term P}.
\<close>


primrec lookup :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) delta \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> 's option" where
  "lookup P d q [] = (if P q then Some q else None)"
| "lookup P d q (e#w) = first_that (\<lambda>t. let (qs,es,q')=t in if q=qs \<and> e=es then lookup P d q' w else None) d"

lemma lookupE1: "!!q. lookup P d q w = Some q' \<Longrightarrow> P q' \<and> (q,w,q') \<in> trcl (set d)" proof (induct w)
  case Nil thus ?case by (cases "P q") simp_all
next
  case (Cons e w) note IHP=this
  hence "first_that (\<lambda>t. let (qs,es,qh)=t in if q=qs \<and> e=es then lookup P d qh w else None) d = Some q'" by simp
  then obtain t where "t\<in>set d \<and> ((let (qs,es,qh)=t in if q=qs \<and> e=es then lookup P d qh w else None) = Some q')" by (blast dest: first_thatE1)
  then obtain qh where 1: "(q,e,qh)\<in>set d \<and> lookup P d qh w = Some q'" 
    by (auto split: prod.splits if_splits)
  moreover from 1 IHP have "P q' \<and> (qh,w,q')\<in>trcl (set d)" by auto
  ultimately show ?case by auto
qed
    
lemma lookupE2: "!!q. lookup P d q w = None \<Longrightarrow> \<not>(\<exists>q'. (P q') \<and> (q,w,q') \<in> trcl (set d))" proof (induct w)
  case Nil thus ?case by (cases "P q") (auto dest: trcl_empty_cons)
next
  case (Cons e w) note IHP=this
  hence "first_that (\<lambda>t. let (qs,es,qh)=t in if q=qs \<and> e=es then lookup P d qh w else None) d = None" by simp
  hence "\<forall>t\<in>set d. (let (qs,es,qh)=t in if q=qs \<and> e=es then lookup P d qh w else None) = None" by (blast dest: first_thatE2)
  hence 1: "!! qs es qh.  (qs,es,qh)\<in>set d \<Longrightarrow> q\<noteq>qs \<or> e\<noteq>es \<or> lookup P d qh w = None" by auto
  show ?case proof (rule notI, elim exE conjE)
    fix q'
    assume C: "P q'" "(q,e#w,q')\<in>trcl (set d)"
    then obtain qh where 2: "(q,e,qh)\<in>set d \<and> (qh,w,q')\<in>trcl (set d)" by (blast dest: trcl_uncons)
    with 1 have "lookup P d qh w = None" by auto
    with C 2 IHP show "False" by auto
  qed
qed

lemma lookupI1: "\<lbrakk>P q'; (q,w,q')\<in>trcl (set d)\<rbrakk> \<Longrightarrow> \<exists>q'. lookup P d q w = Some q'" 
  by (cases "lookup P d q w") (auto dest: lookupE2)

lemma lookupI2: "\<not>(\<exists>q'. P q' \<and> (q,w,q')\<in>trcl (set d)) \<Longrightarrow> lookup P d q w = None"
  by (cases "lookup P d q w") (auto dest: lookupE1)

lemmas lookupE = lookupE1 lookupE2
lemmas lookupI = lookupI1 lookupI2


lemma lookup_trclAD_E1:
  assumes map: "set d = D" and start: "q\<in>Q A" and cons: "D \<subseteq> Q A \<times> \<Sigma> A \<times> Q A"
  assumes A: "lookup P d q w = Some q'"
  shows "P q' \<and> (q,w,q')\<in>trclAD A D"
proof -
  from A map have 1: "P q' \<and> (q,w,q')\<in>trcl D" by (blast dest: lookupE1)
  hence "(q,w,q')\<in>trcl (D \<inter> (Q A \<times> \<Sigma> A \<times> Q A)) \<inter> (Q A \<times> UNIV \<times> UNIV)" using cons start by (subgoal_tac "D = D \<inter> (Q A \<times> \<Sigma> A \<times> Q A)", auto)
  with 1 trclAD_by_trcl' show ?thesis by auto
qed

lemma lookup_trclAD_E2:
  assumes map: "set d = D"
  assumes A: "lookup P d q w = None"
  shows "\<not> (\<exists>q'. P q' \<and> (q,w,q')\<in>trclAD A D)"
proof -
  from map A have "\<not> (\<exists>q'. P q' \<and> (q, w, q') \<in> trcl D)" by (blast dest: lookupE2)
  with trclAD_subset_trcl show ?thesis by auto
qed

lemma lookup_trclAD_I1: "\<lbrakk>set d = D; (q,w,q')\<in>trclAD A D; P q'\<rbrakk> \<Longrightarrow> \<exists>q'. lookup P d q w = Some q'"
  apply (cases "lookup P d q w")
  apply (subgoal_tac "\<not>(\<exists>q'. P q' \<and> (q,w,q')\<in>trclAD A D)")
  apply simp
  apply (rule lookup_trclAD_E2)
  apply auto
  done

lemma lookup_trclAD_I2: "\<lbrakk>set d = D; q\<in>Q A; D \<subseteq> Q A \<times> \<Sigma> A \<times> Q A; \<not>(\<exists>q'. P q' \<and> (q,w,q')\<in>trclAD A D)\<rbrakk> \<Longrightarrow> lookup P d q w = None"
  apply (cases "lookup P d q w", auto)
  apply (subgoal_tac "P a \<and> (q,w,a)\<in>trclAD A (set d)")
  apply blast
  apply (rule lookup_trclAD_E1)
  apply auto
  done

lemmas lookup_trclAD_E = lookup_trclAD_E1 lookup_trclAD_E2
lemmas lookup_trclAD_I = lookup_trclAD_I1 lookup_trclAD_I2 

subsection \<open> Reachable states and alphabet inferred from transition relation \<close>

definition "states d == fst ` (set d) \<union> (snd\<circ>snd) ` (set d)"
definition "alpha d == (fst\<circ>snd) ` (set d)"

lemma statesAlphaI: "(q,a,q')\<in>set d \<Longrightarrow> q\<in>states d \<and> q'\<in>states d \<and> a\<in>alpha d" by (unfold states_def alpha_def, force)
lemma statesE: "q\<in>states d \<Longrightarrow> \<exists>a q'. ((q,a,q')\<in>set d \<or> (q',a,q)\<in>set d)" by (unfold states_def alpha_def, force)
lemma alphaE: "a\<in>alpha d \<Longrightarrow> \<exists>q q'. (q,a,q')\<in>set d" by (unfold states_def alpha_def, force)

lemma states_finite: "finite (states d)" by (unfold states_def, auto)
lemma alpha_finite: "finite (alpha d)" by (unfold alpha_def, auto)

lemma statesAlpha_subset: "set d \<subseteq> states d \<times> alpha d \<times> states d" by (auto dest: statesAlphaI)

lemma states_mono: "set d \<subseteq> set d' \<Longrightarrow> states d \<subseteq> states d'" by (unfold states_def, auto)
lemma alpha_mono: "set d \<subseteq> set d' \<Longrightarrow> alpha d \<subseteq> alpha d'" by (unfold alpha_def, auto)

lemma statesAlpha_insert: "set d' = insert (q,a,q') (set d) \<Longrightarrow> states d' = states d \<union> {q,q'} \<and> alpha d' = insert a (alpha d)"
  by (unfold states_def alpha_def) (simp, blast)

lemma statesAlpha_inv: "\<lbrakk>q\<in>states d; a\<in>alpha d; q'\<in>states d; set d'=insert (q,a,q') (set d)\<rbrakk> \<Longrightarrow> states d = states d' \<and> alpha d = alpha d'"
  by (unfold states_def alpha_def) (simp, blast)

export_code lookup checking SML
  

end
