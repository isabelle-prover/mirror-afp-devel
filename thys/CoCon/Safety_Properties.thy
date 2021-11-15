section \<open>Safety properties\<close>

(* Verification of safety properties *)
theory Safety_Properties
imports Automation_Setup "Bounded_Deducibility_Security.IO_Automaton"
begin


(* Note that the safety properties are only concerned with the
step actions (creation, update and u-update) and their action on the state;
they have nothing to do with the observation actions.  *)


interpretation IO_Automaton where
istate = istate and step = step
done


subsection \<open>Infrastructure for invariance reasoning\<close>

definition cIsInvar :: "(state \<Rightarrow> bool) \<Rightarrow> bool" where
"cIsInvar \<phi> \<equiv> \<forall> s ca. reach s \<and> \<phi> s \<longrightarrow> \<phi> (snd (cStep s ca))"

definition uIsInvar :: "(state \<Rightarrow> bool) \<Rightarrow> bool" where
"uIsInvar \<phi> \<equiv> \<forall> s ua. reach s \<and> \<phi> s \<longrightarrow> \<phi> (snd (uStep s ua))"

definition uuIsInvar :: "(state \<Rightarrow> bool) \<Rightarrow> bool" where
"uuIsInvar \<phi> \<equiv> \<forall> s uua. reach s \<and> \<phi> s \<longrightarrow> \<phi> (snd (uuStep s uua))"

(* for properties on states, of course the observations do not count: *)
lemma invar_cIsInvar_uIsInvar_uuIsInvar:
"invar \<phi> \<longleftrightarrow> cIsInvar \<phi> \<and> uIsInvar \<phi> \<and> uuIsInvar \<phi>" (is "?L \<longleftrightarrow> ?R")
unfolding invar_def cIsInvar_def uIsInvar_def uuIsInvar_def fun_eq_iff
  apply standard
  apply (metis snd_eqD step.simps)
  apply safe
  subgoal for _ a apply(cases a, auto) .
  done

lemma cIsInvar[case_names cUser cConf cPC cChair cPaper cAuthor cConflict cReview]:
assumes
"\<And>s uID p name info email.
       \<lbrakk>reach s; \<phi> s; e_createUser s uID p name info email\<rbrakk>
       \<Longrightarrow> \<phi> (createUser s uID p name info email)"
and
"\<And>s confID uID p name info.
       \<lbrakk>reach s; \<phi> s; e_createConf s confID uID p name info\<rbrakk>
       \<Longrightarrow> \<phi> (createConf s confID uID p name info)"
and
"\<And>s confID uID p uID'.
       \<lbrakk>reach s; \<phi> s; e_createPC s confID uID p uID'\<rbrakk>
       \<Longrightarrow> \<phi> (createPC s confID uID p uID')"
and
"\<And>s confID uID p uID'.
       \<lbrakk>reach s; \<phi> s; e_createChair s confID uID p uID'\<rbrakk>
       \<Longrightarrow> \<phi> (createChair s confID uID p uID')"
and
"\<And>s confID uID p papID name info.
       \<lbrakk>reach s; \<phi> s; e_createPaper s confID uID p papID name info\<rbrakk>
       \<Longrightarrow> \<phi> (createPaper s confID uID p papID name info)"
and
"\<And>s confID uID p papID uID'.
       \<lbrakk>reach s; \<phi> s; e_createAuthor s confID uID p papID uID'\<rbrakk>
       \<Longrightarrow> \<phi> (createAuthor s confID uID p papID uID')"
and
"\<And>s confID uID p papID uID'.
       \<lbrakk>reach s; \<phi> s; e_createConflict s confID uID p papID uID'\<rbrakk>
       \<Longrightarrow> \<phi> (createConflict s confID uID p papID uID')"
and
"\<And>s confID uID p papID uID'.
       \<lbrakk>reach s; \<phi> s; e_createReview s confID uID p papID uID'\<rbrakk>
       \<Longrightarrow> \<phi> (createReview s confID uID p papID uID')"
shows "cIsInvar \<phi>"
unfolding cIsInvar_def apply safe subgoal for _ ca using assms by (cases ca, auto) .

lemma uIsInvar[case_names uUser uConfA uNextPhase uPaperTA uPaperC uPref uReview]:
assumes
"\<And>s uID p p' name info email.
       \<lbrakk>reach s; \<phi> s; e_updateUser s uID p p' name info email\<rbrakk>
       \<Longrightarrow> \<phi> (updateUser s uID p p' name info email)"
 and
"\<And>s confID uID p.
       \<lbrakk>reach s; \<phi> s; e_updateConfA s confID uID p\<rbrakk> \<Longrightarrow> \<phi> (updateConfA s confID uID p)"
and
"\<And>s confID uID p ph.
       \<lbrakk>reach s; \<phi> s; e_updatePhase s confID uID p ph\<rbrakk> \<Longrightarrow> \<phi> (updatePhase s confID uID p ph)"
and
"\<And>s confID uID p paperID name info.
       \<lbrakk>reach s; \<phi> s; e_updatePaperTA s confID uID p paperID name info\<rbrakk>
       \<Longrightarrow> \<phi> (updatePaperTA s confID uID p paperID name info)"
and
"\<And>s confID uID p paperID pc.
       \<lbrakk>reach s; \<phi> s; e_updatePaperC s confID uID p paperID pc\<rbrakk>
       \<Longrightarrow> \<phi> (updatePaperC s confID uID p paperID pc)"
and
"\<And>s confID uID p paperID preference.
       \<lbrakk>reach s; \<phi> s; e_updatePref s confID uID p paperID preference\<rbrakk>
       \<Longrightarrow> \<phi> (updatePref s confID uID p paperID preference)"
and
"\<And>s confID uID p paperID n rc.
       \<lbrakk>reach s; \<phi> s; e_updateReview s confID uID p paperID n rc\<rbrakk>
       \<Longrightarrow> \<phi> (updateReview s confID uID p paperID n rc)"
and
"\<And>s confID uID p paperID fpc.
       \<lbrakk>reach s; \<phi> s; e_updateFPaperC s confID uID p paperID fpc\<rbrakk>
       \<Longrightarrow> \<phi> (updateFPaperC s confID uID p paperID fpc)"
shows "uIsInvar \<phi>"
unfolding uIsInvar_def apply safe using assms subgoal for _ ua by (cases ua, auto) .

lemma uuIsInvar[case_names uuNews uuDis uuReview uuDec]:
assumes
"\<And>s confID uID p comm.
       \<lbrakk>reach s; \<phi> s; e_uupdateNews s confID uID p comm\<rbrakk>
       \<Longrightarrow> \<phi> (uupdateNews s confID uID p comm)"
and
"\<And>s confID uID p paperID comm.
       \<lbrakk>reach s; \<phi> s; e_uupdateDis s confID uID p paperID comm\<rbrakk>
       \<Longrightarrow> \<phi> (uupdateDis s confID uID p paperID comm)"
and
"\<And>s confID uID p paperID n rc.
       \<lbrakk>reach s; \<phi> s; e_uupdateReview s confID uID p paperID n rc\<rbrakk>
       \<Longrightarrow> \<phi> (uupdateReview s confID uID p paperID n rc)"
and
"\<And>s confID uID p paperID decision.
       \<lbrakk>reach s; \<phi> s; e_uupdateDec s confID uID p paperID decision\<rbrakk>
       \<Longrightarrow> \<phi> (uupdateDec s confID uID p paperID decision)"
shows "uuIsInvar \<phi>"
unfolding uuIsInvar_def apply safe subgoal for _ uua using assms by (cases uua, auto) .


subsection \<open>Safety proofs\<close>

(* Simplification and splitting setup: *)
declare option.splits[split] paper.splits[split] discussion.splits[split] role.splits[split]
        Let_def[simp] list_all_iff[simp] list_ex_iff[simp] fun_upd2_def[simp] IDsOK_def[simp]
        if_splits[split]


fun papIDsOfRole where
"papIDsOfRole (Aut papID) = [papID]"
|
"papIDsOfRole (Rev papID n) = [papID]"
|
"papIDsOfRole _ = []"

(* The phase is always \<le> closedPH: *)
definition phase_leq_closedPH :: "state \<Rightarrow> bool" where
"phase_leq_closedPH s \<equiv>
 \<forall> confID. phase s confID \<le> closedPH"

lemma holdsIstate_phase_leq_closedPH: "holdsIstate phase_leq_closedPH"
unfolding IO_Automaton.holdsIstate_def istate_def phase_leq_closedPH_def by auto

lemma cIsInvar_phase_leq_closedPH: "cIsInvar phase_leq_closedPH"
apply (cases phase_leq_closedPH rule: cIsInvar)
by (auto simp: c_defs phase_leq_closedPH_def)

lemma uIsInvar_phase_leq_closedPH: "uIsInvar phase_leq_closedPH"
apply (cases phase_leq_closedPH rule: uIsInvar)
by (auto simp: u_defs phase_leq_closedPH_def)

lemma uuIsInvar_phase_leq_closedPH: "uuIsInvar phase_leq_closedPH"
apply (cases phase_leq_closedPH rule: uuIsInvar)
by (auto simp: uu_defs phase_leq_closedPH_def)

lemma invar_phase_leq_closedPH: "invar phase_leq_closedPH"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_phase_leq_closedPH uIsInvar_phase_leq_closedPH uuIsInvar_phase_leq_closedPH by auto

lemmas phase_leq_closedPH1 =
holdsIstate_invar[OF holdsIstate_phase_leq_closedPH invar_phase_leq_closedPH]

theorem phase_leq_closedPH:
assumes a: "reach s"
shows "phase s confID \<le> closedPH"
using phase_leq_closedPH1[OF a] unfolding phase_leq_closedPH_def by auto

(* A conference ID exsists if its phase is > noPH: *)
definition geq_noPH_confIDs :: "state \<Rightarrow> bool" where
"geq_noPH_confIDs s \<equiv>
 \<forall> confID. phase s confID > noPH \<longrightarrow> confID \<in>\<in> confIDs s"

lemma holdsIstate_geq_noPH_confIDs: "holdsIstate geq_noPH_confIDs"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def geq_noPH_confIDs_def by auto

lemma cIsInvar_geq_noPH_confIDs: "cIsInvar geq_noPH_confIDs"
apply (cases geq_noPH_confIDs rule: cIsInvar)
by (auto simp: c_defs geq_noPH_confIDs_def)

lemma uIsInvar_geq_noPH_confIDs: "uIsInvar geq_noPH_confIDs"
apply (cases geq_noPH_confIDs rule: uIsInvar)
by (auto simp: u_defs geq_noPH_confIDs_def)

lemma uuIsInvar_geq_noPH_confIDs: "uuIsInvar geq_noPH_confIDs"
apply (cases geq_noPH_confIDs rule: uuIsInvar)
by (auto simp: uu_defs geq_noPH_confIDs_def)

lemma invar_geq_noPH_confIDs: "invar geq_noPH_confIDs"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_geq_noPH_confIDs uIsInvar_geq_noPH_confIDs uuIsInvar_geq_noPH_confIDs by auto

lemmas geq_noPH_confIDs1 =
holdsIstate_invar[OF holdsIstate_geq_noPH_confIDs invar_geq_noPH_confIDs]

theorem geq_noPH_confIDs:
assumes a: "reach s"
shows "phase s confID > noPH \<longrightarrow> confID \<in>\<in> confIDs s"
using geq_noPH_confIDs1[OF a] unfolding geq_noPH_confIDs_def by auto

(* All the IDs involved in the "roles" relation are valid IDs of the system: *)
definition roles_IDsOK :: "state \<Rightarrow> bool" where
"roles_IDsOK s \<equiv>
 \<forall> confID uID rl.
   rl \<in>\<in> roles s confID uID \<longrightarrow> IDsOK s [confID] [uID] (papIDsOfRole rl)"

lemma holdsIstate_roles_IDsOK: "holdsIstate roles_IDsOK"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def roles_IDsOK_def by auto

lemma cIsInvar_roles_IDsOK: "cIsInvar roles_IDsOK"
apply (cases roles_IDsOK rule: cIsInvar)
by (auto simp: c_defs roles_IDsOK_def)

lemma uIsInvar_roles_IDsOK: "uIsInvar roles_IDsOK"
apply (cases roles_IDsOK rule: uIsInvar)
by (auto simp: u_defs roles_IDsOK_def)

lemma uuIsInvar_roles_IDsOK: "uuIsInvar roles_IDsOK"
apply (cases roles_IDsOK rule: uuIsInvar)
by (auto simp: uu_defs roles_IDsOK_def)

lemma invar_roles_IDsOK: "invar roles_IDsOK"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_roles_IDsOK uIsInvar_roles_IDsOK uuIsInvar_roles_IDsOK by auto

lemmas roles_IDsOK1 =
holdsIstate_invar[OF holdsIstate_roles_IDsOK invar_roles_IDsOK]

theorem roles_IDsOK:
assumes a: "reach s" and rl: "rl \<in>\<in> roles s confID uID"
shows "IDsOK s [confID] [uID] (papIDsOfRole rl)"
using roles_IDsOK1[OF a] rl unfolding roles_IDsOK_def by auto

corollary roles_confIDs:
assumes a: "reach s" and A: "rl \<in>\<in> roles s confID uID"
shows "confID \<in>\<in> confIDs s"
using roles_IDsOK[OF a] A unfolding IDsOK_def by auto

corollary roles_userIDs:
assumes a: "reach s" and A: "rl \<in>\<in> roles s confID uID"
shows "uID \<in>\<in> userIDs s"
using roles_IDsOK[OF a] A unfolding IDsOK_def by auto

corollary isAut_paperIDs:
assumes a: "reach s" and A: "isAut s confID uID papID"
shows "papID \<in>\<in> paperIDs s confID"
using roles_IDsOK[OF a] A unfolding IDsOK_def by auto

corollary isRevNth_paperIDs:
assumes a: "reach s" and A: "isRevNth s confID uID papID n"
shows "papID \<in>\<in> paperIDs s confID"
using roles_IDsOK[OF a] A unfolding IDsOK_def by auto

corollary isRev_paperIDs:
assumes a: "reach s" and A: "isRev s confID uID papID"
shows "papID \<in>\<in> paperIDs s confID"
using isRevNth_paperIDs[OF a] A unfolding isRev_def2 by auto

corollary isRev_userIDs:
assumes a: "reach s" and A: "isRev s confID uID papID"
shows "uID \<in>\<in> userIDs s"
using roles_userIDs[OF a] A unfolding isRev_def2 by auto

corollary isRev_confIDs:
assumes a: "reach s" and A: "isRev s confID uID papID"
shows "confID \<in>\<in> confIDs s"
using roles_confIDs[OF a] A unfolding isRev_def2 by auto

(* The lists of (conference, user and paper) IDs are non-repetitive *)
definition distinct_IDs :: "state \<Rightarrow> bool" where
"distinct_IDs s \<equiv>
 distinct (confIDs s) \<and> distinct (userIDs s) \<and> (\<forall> confID. distinct (paperIDs s confID))"

lemma holdsIstate_distinct_IDs: "holdsIstate distinct_IDs"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def distinct_IDs_def by auto

lemma cIsInvar_distinct_IDs: "cIsInvar distinct_IDs"
apply (cases distinct_IDs rule: cIsInvar)
by (auto simp: c_defs distinct_IDs_def getAllPaperIDs_def)

lemma uIsInvar_distinct_IDs: "uIsInvar distinct_IDs"
apply (cases distinct_IDs rule: uIsInvar)
by (auto simp: u_defs distinct_IDs_def)

lemma uuIsInvar_distinct_IDs: "uuIsInvar distinct_IDs"
apply (cases distinct_IDs rule: uuIsInvar)
by (auto simp: uu_defs distinct_IDs_def)

lemma invar_distinct_IDs: "invar distinct_IDs"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_distinct_IDs uIsInvar_distinct_IDs uuIsInvar_distinct_IDs by auto

lemmas distinct_IDs1 = holdsIstate_invar[OF holdsIstate_distinct_IDs invar_distinct_IDs]

theorem distinct_IDs:
assumes a: "reach s"
shows "distinct (confIDs s) \<and> distinct (userIDs s) \<and> (\<forall> confID. distinct (paperIDs s confID))"
using distinct_IDs1[OF a] unfolding distinct_IDs_def by auto

lemmas distinct_confIDs = distinct_IDs[THEN conjunct1]
lemmas distinct_userIDs = distinct_IDs[THEN conjunct2, THEN conjunct1]
lemmas distinct_paperIDs = distinct_IDs[THEN conjunct2, THEN conjunct2, rule_format]

(* The list of roles of a user at a conference is non-repetitive *)
definition distinct_roles :: "state \<Rightarrow> bool" where
"distinct_roles s \<equiv>
 \<forall> confID uID. distinct (roles s confID uID)"

lemma holdsIstate_distinct_roles: "holdsIstate distinct_roles"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def distinct_roles_def by auto

lemma cIsInvar_distinct_roles: "cIsInvar distinct_roles"
apply (cases distinct_roles rule: cIsInvar)
by (auto simp: c_defs distinct_roles_def)

lemma uIsInvar_distinct_roles: "uIsInvar distinct_roles"
apply (cases distinct_roles rule: uIsInvar)
by (auto simp: u_defs distinct_roles_def)

lemma uuIsInvar_distinct_roles: "uuIsInvar distinct_roles"
apply (cases distinct_roles rule: uuIsInvar)
by (auto simp: uu_defs distinct_roles_def)

lemma invar_distinct_roles: "invar distinct_roles"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_distinct_roles uIsInvar_distinct_roles uuIsInvar_distinct_roles by auto

lemmas distinct_roles1 = holdsIstate_invar[OF holdsIstate_distinct_roles invar_distinct_roles]

theorem distinct_roles:
assumes a: "reach s"
shows "distinct (roles s confID uID)"
using distinct_roles1[OF a] unfolding distinct_roles_def by auto

(* Only committee members become reviewers: *)
definition isRevNth_isPC :: "state \<Rightarrow> bool" where
"isRevNth_isPC s \<equiv>
 \<forall> confID uID papID n. isRevNth s confID uID papID n \<longrightarrow> isPC s confID uID"

lemma holdsIstate_isRevNth_isPC: "holdsIstate isRevNth_isPC"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def isRevNth_isPC_def by auto

lemma cIsInvar_isRevNth_isPC: "cIsInvar isRevNth_isPC"
apply (cases isRevNth_isPC rule: cIsInvar)
by (auto simp: c_defs isRevNth_isPC_def)

lemma uIsInvar_isRevNth_isPC: "uIsInvar isRevNth_isPC"
apply (cases isRevNth_isPC rule: uIsInvar)
by (auto simp: u_defs isRevNth_isPC_def)

lemma uuIsInvar_isRevNth_isPC: "uuIsInvar isRevNth_isPC"
apply (cases isRevNth_isPC rule: uuIsInvar)
by (auto simp: uu_defs isRevNth_isPC_def)

lemma invar_isRevNth_isPC: "invar isRevNth_isPC"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_isRevNth_isPC uIsInvar_isRevNth_isPC uuIsInvar_isRevNth_isPC by auto

lemmas isRevNth_isPC1 = holdsIstate_invar[OF holdsIstate_isRevNth_isPC invar_isRevNth_isPC]

theorem isRevNth_isPC:
assumes a: "reach s" and R: "isRevNth s confID uID papID n"
shows "isPC s confID uID"
using isRevNth_isPC1[OF a] R unfolding isRevNth_isPC_def by auto

corollary isRev_isPC:
assumes a: "reach s" and R: "isRev s confID uID papID"
shows "isPC s confID uID"
using isRevNth_isPC[OF a] R unfolding isRev_def2 by auto

(* Every conference that has papers is registered: *)
definition paperIDs_confIDs :: "state \<Rightarrow> bool" where
"paperIDs_confIDs s \<equiv>
 \<forall> confID papID.
    papID \<in>\<in> paperIDs s confID \<longrightarrow> confID \<in>\<in> confIDs s"

lemma holdsIstate_paperIDs_confIDs: "holdsIstate paperIDs_confIDs"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def paperIDs_confIDs_def by auto

lemma cIsInvar_paperIDs_confIDs: "cIsInvar paperIDs_confIDs"
apply (cases paperIDs_confIDs rule: cIsInvar)
by (auto simp: c_defs paperIDs_confIDs_def )

lemma uIsInvar_paperIDs_confIDs: "uIsInvar paperIDs_confIDs"
apply (cases paperIDs_confIDs rule: uIsInvar)
by (auto simp: u_defs paperIDs_confIDs_def)

lemma uuIsInvar_paperIDs_confIDs: "uuIsInvar paperIDs_confIDs"
apply (cases paperIDs_confIDs rule: uuIsInvar)
by (auto simp: uu_defs paperIDs_confIDs_def)

lemma invar_paperIDs_confIDs: "invar paperIDs_confIDs"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_paperIDs_confIDs uIsInvar_paperIDs_confIDs uuIsInvar_paperIDs_confIDs by auto

lemmas paperIDs_confIDs1 = holdsIstate_invar[OF holdsIstate_paperIDs_confIDs invar_paperIDs_confIDs]

theorem paperIDs_confIDs:
assumes a: "reach s" and p: "papID \<in>\<in> paperIDs s confID"
shows "confID \<in>\<in> confIDs s"
using paperIDs_confIDs1[OF a] p  unfolding paperIDs_confIDs_def by auto

corollary paperIDs_getAllPaperIDs:
assumes a: "reach s" and p: "papID \<in>\<in> paperIDs s confID"
shows "papID \<in>\<in> getAllPaperIDs s"
using paperIDs_confIDs[OF assms] p unfolding getAllPaperIDs_def by auto

corollary isRevNth_getAllPaperIDs:
assumes a: "reach s" and "isRevNth s confID uID papID n"
shows "papID \<in>\<in> getAllPaperIDs s"
using paperIDs_getAllPaperIDs[OF a isRevNth_paperIDs[OF assms]] .

(* No paper is registered at two conferences: *)
definition paperIDs_equals :: "state \<Rightarrow> bool" where
"paperIDs_equals s \<equiv>
 \<forall> confID1 confID2 papID.
    papID \<in>\<in> paperIDs s confID1 \<and> papID \<in>\<in> paperIDs s confID2
    \<longrightarrow> confID1 = confID2"

lemma holdsIstate_paperIDs_equals: "holdsIstate paperIDs_equals"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def paperIDs_equals_def by auto

lemma cIsInvar_paperIDs_equals: "cIsInvar paperIDs_equals"
apply (cases paperIDs_equals rule: cIsInvar)
by (auto simp: c_defs paperIDs_equals_def paperIDs_getAllPaperIDs)

lemma uIsInvar_paperIDs_equals: "uIsInvar paperIDs_equals"
apply (cases paperIDs_equals rule: uIsInvar)
by (auto simp: u_defs paperIDs_equals_def)

lemma uuIsInvar_paperIDs_equals: "uuIsInvar paperIDs_equals"
apply (cases paperIDs_equals rule: uuIsInvar)
by (auto simp: uu_defs paperIDs_equals_def)

lemma invar_paperIDs_equals: "invar paperIDs_equals"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_paperIDs_equals uIsInvar_paperIDs_equals uuIsInvar_paperIDs_equals by auto

lemmas paperIDs_equals1 = holdsIstate_invar[OF holdsIstate_paperIDs_equals invar_paperIDs_equals]

theorem paperIDs_equals:
assumes a: "reach s" and p: "papID \<in>\<in> paperIDs s confID1" "papID \<in>\<in> paperIDs s confID2"
shows "confID1 = confID2"
using paperIDs_equals1[OF a] p unfolding paperIDs_equals_def by auto

(* Everybody has conflict with their own papers *)
definition isAut_pref_Conflict :: "state \<Rightarrow> bool" where
"isAut_pref_Conflict s \<equiv>
 \<forall> confID uID papID. isAut s confID uID papID \<longrightarrow> pref s uID papID = Conflict"

lemma holdsIstate_isAut_pref_Conflict: "holdsIstate isAut_pref_Conflict"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def isAut_pref_Conflict_def by auto

lemma cIsInvar_isAut_pref_Conflict: "cIsInvar isAut_pref_Conflict"
apply (cases isAut_pref_Conflict rule: cIsInvar)
by (auto simp: c_defs isAut_pref_Conflict_def)

lemma uIsInvar_isAut_pref_Conflict: "uIsInvar isAut_pref_Conflict"
proof(cases isAut_pref_Conflict rule: uIsInvar)
  case (uPref s confID uID p paperID preference)
  thus ?case apply (auto simp: u_defs isAut_pref_Conflict_def)
  apply(frule isAut_paperIDs, simp)
  apply(frule paperIDs_equals, simp, simp, fastforce)
  done
qed (auto simp: u_defs isAut_pref_Conflict_def)

lemma uuIsInvar_isAut_pref_Conflict: "uuIsInvar isAut_pref_Conflict"
apply (cases isAut_pref_Conflict rule: uuIsInvar)
by (auto simp: uu_defs isAut_pref_Conflict_def)

lemma invar_isAut_pref_Conflict: "invar isAut_pref_Conflict"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_isAut_pref_Conflict uIsInvar_isAut_pref_Conflict
uuIsInvar_isAut_pref_Conflict by auto

lemmas isAut_pref_Conflict1 =
holdsIstate_invar[OF holdsIstate_isAut_pref_Conflict invar_isAut_pref_Conflict]

theorem isAut_pref_Conflict:
assumes a: "reach s" and i: "isAut s confID uID papID"
shows "pref s uID papID = Conflict"
using isAut_pref_Conflict1[OF a] i unfolding isAut_pref_Conflict_def by auto

(* A conference in phase noPH has no assigned papers  *)
definition phase_noPH_paperIDs :: "state \<Rightarrow> bool" where
"phase_noPH_paperIDs s \<equiv>
 \<forall> confID. phase s confID = noPH \<longrightarrow> paperIDs s confID = []"

lemma holdsIstate_phase_noPH_paperIDs: "holdsIstate phase_noPH_paperIDs"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def phase_noPH_paperIDs_def by auto

lemma cIsInvar_phase_noPH_paperIDs: "cIsInvar phase_noPH_paperIDs"
apply (cases phase_noPH_paperIDs rule: cIsInvar)
by (auto simp: c_defs phase_noPH_paperIDs_def)

lemma uIsInvar_phase_noPH_paperIDs: "uIsInvar phase_noPH_paperIDs"
apply(cases phase_noPH_paperIDs rule: uIsInvar)
by (auto simp: u_defs phase_noPH_paperIDs_def)

lemma uuIsInvar_phase_noPH_paperIDs: "uuIsInvar phase_noPH_paperIDs"
apply (cases phase_noPH_paperIDs rule: uuIsInvar)
by (auto simp: uu_defs phase_noPH_paperIDs_def)

lemma invar_phase_noPH_paperIDs: "invar phase_noPH_paperIDs"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_phase_noPH_paperIDs uIsInvar_phase_noPH_paperIDs
uuIsInvar_phase_noPH_paperIDs by auto

lemmas phase_noPH_paperIDs1 =
holdsIstate_invar[OF holdsIstate_phase_noPH_paperIDs invar_phase_noPH_paperIDs]

theorem phase_noPH_paperIDs:
assumes a: "reach s" and p: "phase s confID = noPH"
shows "paperIDs s confID = []"
using phase_noPH_paperIDs1[OF a] p unfolding phase_noPH_paperIDs_def by auto

(* Papers only exist starting from the submission phase: *)
definition paperIDs_geq_subPH :: "state \<Rightarrow> bool" where
"paperIDs_geq_subPH s \<equiv>
 \<forall> confID papID. papID \<in>\<in> paperIDs s confID \<longrightarrow> phase s confID \<ge> subPH"

lemma holdsIstate_paperIDs_geq_subPH: "holdsIstate paperIDs_geq_subPH"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def paperIDs_geq_subPH_def by auto

lemma cIsInvar_paperIDs_geq_subPH: "cIsInvar paperIDs_geq_subPH"
apply (cases paperIDs_geq_subPH rule: cIsInvar)
by (auto simp: c_defs paperIDs_geq_subPH_def)

lemma uIsInvar_paperIDs_geq_subPH: "uIsInvar paperIDs_geq_subPH"
apply (cases paperIDs_geq_subPH rule: uIsInvar)
by (fastforce simp: u_defs paperIDs_geq_subPH_def)+

lemma uuIsInvar_paperIDs_geq_subPH: "uuIsInvar paperIDs_geq_subPH"
apply (cases paperIDs_geq_subPH rule: uuIsInvar)
by (auto simp: uu_defs paperIDs_geq_subPH_def)

lemma invar_paperIDs_geq_subPH: "invar paperIDs_geq_subPH"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_paperIDs_geq_subPH uIsInvar_paperIDs_geq_subPH
uuIsInvar_paperIDs_geq_subPH by auto

lemmas paperIDs_geq_subPH1 =
holdsIstate_invar[OF holdsIstate_paperIDs_geq_subPH invar_paperIDs_geq_subPH]

theorem paperIDs_geq_subPH:
assumes a: "reach s" and i: "papID \<in>\<in> paperIDs s confID"
shows "phase s confID \<ge> subPH"
using paperIDs_geq_subPH1[OF a] i unfolding paperIDs_geq_subPH_def by auto

(* Reviewers only exist starting from the reviewing phase: *)
definition isRevNth_geq_revPH :: "state \<Rightarrow> bool" where
"isRevNth_geq_revPH s \<equiv>
 \<forall> confID uID papID n. isRevNth s confID uID papID n \<longrightarrow> phase s confID \<ge> revPH"

lemma holdsIstate_isRevNth_geq_revPH: "holdsIstate isRevNth_geq_revPH"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def isRevNth_geq_revPH_def by auto

lemma cIsInvar_isRevNth_geq_revPH: "cIsInvar isRevNth_geq_revPH"
apply (cases isRevNth_geq_revPH rule: cIsInvar)
by (auto simp: c_defs isRevNth_geq_revPH_def)

lemma uIsInvar_isRevNth_geq_revPH: "uIsInvar isRevNth_geq_revPH"
proof (cases isRevNth_geq_revPH rule: uIsInvar)
  case (uConfA s confID uID p) thus ?case
  by (fastforce simp: u_defs isRevNth_geq_revPH_def)
qed(fastforce simp: u_defs isRevNth_geq_revPH_def)+

lemma uuIsInvar_isRevNth_geq_revPH: "uuIsInvar isRevNth_geq_revPH"
apply (cases isRevNth_geq_revPH rule: uuIsInvar)
by (auto simp: uu_defs isRevNth_geq_revPH_def)

lemma invar_isRevNth_geq_revPH: "invar isRevNth_geq_revPH"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_isRevNth_geq_revPH uIsInvar_isRevNth_geq_revPH
uuIsInvar_isRevNth_geq_revPH by auto

lemmas isRevNth_geq_revPH1 =
holdsIstate_invar[OF holdsIstate_isRevNth_geq_revPH invar_isRevNth_geq_revPH]

theorem isRevNth_geq_revPH:
assumes a: "reach s" and i: "isRevNth s confID uID papID n"
shows "phase s confID \<ge> revPH"
using isRevNth_geq_revPH1[OF a] i unfolding isRevNth_geq_revPH_def by auto

corollary isRev_geq_revPH:
assumes a: "reach s" and i: "isRev s confID uID papID"
shows "phase s confID \<ge> revPH"
using isRevNth_geq_revPH[OF a] i unfolding isRev_def2 by auto

(* Every paper has at least one author: *)
definition paperID_ex_userID :: "state \<Rightarrow> bool" where
"paperID_ex_userID s \<equiv>
 \<forall> confID papID. papID \<in>\<in> paperIDs s confID \<longrightarrow> (\<exists> uID. isAut s confID uID papID)"

lemma holdsIstate_paperID_ex_userID: "holdsIstate paperID_ex_userID"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def paperID_ex_userID_def by auto

lemma cIsInvar_paperID_ex_userID: "cIsInvar paperID_ex_userID"
apply (cases paperID_ex_userID rule: cIsInvar)
by (fastforce simp: c_defs paperID_ex_userID_def paperIDs_confIDs)+

lemma uIsInvar_paperID_ex_userID: "uIsInvar paperID_ex_userID"
apply (cases paperID_ex_userID rule: uIsInvar)
by (fastforce simp: u_defs paperID_ex_userID_def)+

lemma uuIsInvar_paperID_ex_userID: "uuIsInvar paperID_ex_userID"
apply (cases paperID_ex_userID rule: uuIsInvar)
by (auto simp: uu_defs paperID_ex_userID_def)

lemma invar_paperID_ex_userID: "invar paperID_ex_userID"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_paperID_ex_userID uIsInvar_paperID_ex_userID
uuIsInvar_paperID_ex_userID by auto

lemmas paperID_ex_userID1 =
holdsIstate_invar[OF holdsIstate_paperID_ex_userID invar_paperID_ex_userID]

theorem paperID_ex_userID:
assumes a: "reach s" and i: "papID \<in>\<in> paperIDs s confID"
shows "\<exists> uID. isAut s confID uID papID"
using paperID_ex_userID1[OF a] i unfolding paperID_ex_userID_def by auto

(* Nobody reviews a paper with which one has conflict: *)
definition pref_Conflict_isRevNth :: "state \<Rightarrow> bool" where
"pref_Conflict_isRevNth s \<equiv>
 \<forall> confID uID papID n. pref s uID papID = Conflict \<longrightarrow> \<not> isRevNth s confID uID papID n"

lemma holdsIstate_pref_Conflict_isRevNth: "holdsIstate pref_Conflict_isRevNth"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def pref_Conflict_isRevNth_def by auto

lemma cIsInvar_pref_Conflict_isRevNth: "cIsInvar pref_Conflict_isRevNth"
proof (cases pref_Conflict_isRevNth rule: cIsInvar)
  case (cAuthor s confID uID p papID uID') thus ?case
  apply (auto simp: c_defs pref_Conflict_isRevNth_def)
  apply(frule isRevNth_geq_revPH, simp, simp)
  apply(frule isRevNth_paperIDs, simp)
  apply(frule paperIDs_equals, simp, simp, force)
  done
next
  case (cConflict  s confID uID p papID uID') thus ?case
  apply (auto simp: c_defs pref_Conflict_isRevNth_def)
  apply(frule isRevNth_geq_revPH, simp)
  apply(frule isRevNth_paperIDs, simp)
  apply(frule paperIDs_equals, simp, simp, force)
  done
qed (auto simp: c_defs pref_Conflict_isRevNth_def isRevNth_getAllPaperIDs)

lemma uIsInvar_pref_Conflict_isRevNth: "uIsInvar pref_Conflict_isRevNth"
proof(cases pref_Conflict_isRevNth rule: uIsInvar)
  case (uPref s confID uID p paperID pref) thus ?case
  apply (auto simp: u_defs pref_Conflict_isRevNth_def)
  apply(frule isRevNth_geq_revPH, simp)
  apply(frule isRevNth_paperIDs, simp)
  apply(frule paperIDs_equals, simp, simp, force)
  done
qed (auto simp: u_defs pref_Conflict_isRevNth_def)

lemma uuIsInvar_pref_Conflict_isRevNth: "uuIsInvar pref_Conflict_isRevNth"
apply (cases pref_Conflict_isRevNth rule: uuIsInvar)
by (auto simp: uu_defs pref_Conflict_isRevNth_def)

lemma invar_pref_Conflict_isRevNth: "invar pref_Conflict_isRevNth"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_pref_Conflict_isRevNth uIsInvar_pref_Conflict_isRevNth uuIsInvar_pref_Conflict_isRevNth by auto

lemmas pref_Conflict_isRevNth1 =
holdsIstate_invar[OF holdsIstate_pref_Conflict_isRevNth invar_pref_Conflict_isRevNth]

theorem pref_Conflict_isRevNth:
assumes a: "reach s" and i: "pref s uID papID = Conflict"
shows "\<not> isRevNth s confID uID papID n"
using pref_Conflict_isRevNth1[OF a] i unfolding pref_Conflict_isRevNth_def by auto

corollary pref_Conflict_isRev:
assumes a: "reach s" and i: "pref s uID papID = Conflict"
shows "\<not> isRev s confID uID papID"
using pref_Conflict_isRevNth[OF a] i unfolding isRev_def2 by auto

(* Nobody reviews her own paper: *)
corollary pref_isAut_isRevNth:
assumes a: "reach s" and i: "isAut s confID uID papID"
shows "\<not> isRevNth s confID uID papID n"
using pref_Conflict_isRevNth[OF a] isAut_pref_Conflict[OF a i] by auto

corollary pref_isAut_isRev:
assumes a: "reach s" and i: "isAut s confID uID papID"
shows "\<not> isRev s confID uID papID"
using pref_isAut_isRevNth[OF a] i unfolding isRev_def2 by auto

(* Every chair is also a committee member *)
definition isChair_isPC :: "state \<Rightarrow> bool" where
"isChair_isPC s \<equiv>
 \<forall> confID uID. isChair s confID uID \<longrightarrow> isPC s confID uID"

lemma holdsIstate_isChair_isPC: "holdsIstate isChair_isPC"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def isChair_isPC_def by auto

lemma cIsInvar_isChair_isPC: "cIsInvar isChair_isPC"
apply (cases isChair_isPC rule: cIsInvar)
by (auto simp: c_defs isChair_isPC_def)

lemma uIsInvar_isChair_isPC: "uIsInvar isChair_isPC"
apply(cases isChair_isPC rule: uIsInvar)
by (auto simp: u_defs isChair_isPC_def)

lemma uuIsInvar_isChair_isPC: "uuIsInvar isChair_isPC"
apply (cases isChair_isPC rule: uuIsInvar)
by (auto simp: uu_defs isChair_isPC_def)

lemma invar_isChair_isPC: "invar isChair_isPC"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_isChair_isPC uIsInvar_isChair_isPC
uuIsInvar_isChair_isPC by auto

lemmas isChair_isPC1 =
holdsIstate_invar[OF holdsIstate_isChair_isPC invar_isChair_isPC]

theorem isChair_isPC:
assumes a: "reach s" and p: "isChair s confID uID"
shows "isPC s confID uID"
using isChair_isPC1[OF a] p unfolding isChair_isPC_def by auto

(* A user does not get to write more than one review of any given paper: *)
definition isRevNth_equals :: "state \<Rightarrow> bool" where
"isRevNth_equals s \<equiv>
 \<forall> confID uID papID m n.
    isRevNth s confID uID papID m \<and> isRevNth s confID uID papID n
    \<longrightarrow> m = n"

lemma holdsIstate_isRevNth_equals: "holdsIstate isRevNth_equals"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def isRevNth_equals_def by auto

lemma cIsInvar_isRevNth_equals: "cIsInvar isRevNth_equals"
proof (cases isRevNth_equals rule: cIsInvar)
(* this case is merely singled out for documentation: *)
  case (cReview s confID uID p papID uID')
  thus ?case by(fastforce simp add: c_defs isRevNth_equals_def isRev_def2)
qed (auto simp: c_defs isRevNth_equals_def)

lemma uIsInvar_isRevNth_equals: "uIsInvar isRevNth_equals"
apply(cases isRevNth_equals rule: uIsInvar)
by (auto simp: u_defs isRevNth_equals_def)

lemma uuIsInvar_isRevNth_equals: "uuIsInvar isRevNth_equals"
apply (cases isRevNth_equals rule: uuIsInvar)
by (auto simp: uu_defs isRevNth_equals_def)

lemma invar_isRevNth_equals: "invar isRevNth_equals"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_isRevNth_equals uIsInvar_isRevNth_equals
uuIsInvar_isRevNth_equals by auto

lemmas isRevNth_equals1 =
holdsIstate_invar[OF holdsIstate_isRevNth_equals invar_isRevNth_equals]

theorem isRevNth_equals:
assumes a: "reach s" and r: "isRevNth s confID uID papID m" "isRevNth s confID uID papID n"
shows "m = n"
using isRevNth_equals1[OF a] r unfolding isRevNth_equals_def by blast

corollary isRevNth_getReviewIndex:
assumes a: "reach s" and r: "isRevNth s confID uID papID n"
shows "n = getReviewIndex s confID uID papID"
using isRevNth_equals[OF a r] r
by (metis isRev_def2 isRev_def3)


(* A reviewer is always assigned a valid review number: *)
definition isRevNth_less_length :: "state \<Rightarrow> bool" where
"isRevNth_less_length s \<equiv>
 \<forall> confID uID papID n.
    isRevNth s confID uID papID n \<longrightarrow> n < length (reviewsPaper (paper s papID))"

lemma holdsIstate_isRevNth_less_length: "holdsIstate isRevNth_less_length"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def isRevNth_less_length_def by auto

lemma cIsInvar_isRevNth_less_length: "cIsInvar isRevNth_less_length"
apply(cases isRevNth_less_length rule: cIsInvar)
by(fastforce simp: c_defs isRevNth_less_length_def
isRevNth_getAllPaperIDs isRev_def2 isRevNth_paperIDs paperIDs_equals less_SucI)+

lemma uIsInvar_isRevNth_less_length: "uIsInvar isRevNth_less_length"
apply(cases isRevNth_less_length rule: uIsInvar)
by(fastforce simp: u_defs isRevNth_less_length_def
isRevNth_getAllPaperIDs isRev_def2 isRevNth_paperIDs paperIDs_equals less_SucI)+

lemma uuIsInvar_isRevNth_less_length: "uuIsInvar isRevNth_less_length"
apply (cases isRevNth_less_length rule: uuIsInvar)
by(fastforce simp: uu_defs isRevNth_less_length_def
isRevNth_getAllPaperIDs isRev_def2 isRevNth_paperIDs paperIDs_equals less_SucI)+

lemma invar_isRevNth_less_length: "invar isRevNth_less_length"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_isRevNth_less_length uIsInvar_isRevNth_less_length
uuIsInvar_isRevNth_less_length by auto

lemmas isRevNth_less_length1 =
holdsIstate_invar[OF holdsIstate_isRevNth_less_length invar_isRevNth_less_length]

theorem isRevNth_less_length:
assumes "reach s" and "isRevNth s cid uid pid n"
shows "n < length (reviewsPaper (paper s pid))"
using isRevNth_less_length1 assms unfolding isRevNth_less_length_def by blast


(* No two reviewers get assigned the same review: *)
definition isRevNth_equalsU :: "state \<Rightarrow> bool" where
"isRevNth_equalsU s \<equiv>
 \<forall> confID uID uID1 papID n.
    isRevNth s confID uID papID n \<and> isRevNth s confID uID1 papID n
    \<longrightarrow> uID = uID1"

lemma holdsIstate_isRevNth_equalsU: "holdsIstate isRevNth_equalsU"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def isRevNth_equalsU_def by auto

lemma cIsInvar_isRevNth_equalsU: "cIsInvar isRevNth_equalsU"
apply (cases isRevNth_equalsU rule: cIsInvar)
apply(fastforce simp: c_defs isRevNth_equalsU_def)+
proof-
  fix s confID uID p papID uID'
  assume s: "reach s"
  and 0: "isRevNth_equalsU s" "e_createReview s confID uID p papID uID'"
  let ?s' = "createReview s confID uID p papID uID'"
  show "isRevNth_equalsU ?s'"
  unfolding isRevNth_equalsU_def proof clarify
    fix confIDa uIDa uID1 papIDa n
    assume "isRevNth ?s' confIDa uIDa papIDa n" "isRevNth ?s' confIDa uID1 papIDa n"
    thus "uIDa = uID1"
    apply(cases "confIDa = confID \<and> papIDa = papID")
    apply(cases "uIDa = uID", cases "uID1 = uID")
    using s 0 isRevNth_less_length[OF s, of papID n] unfolding isRevNth_less_length_def
    by (fastforce simp: c_defs isRevNth_equalsU_def)+
  qed
qed

lemma uIsInvar_isRevNth_equalsU: "uIsInvar isRevNth_equalsU"
apply(cases isRevNth_equalsU rule: uIsInvar)
by (auto simp: u_defs isRevNth_equalsU_def)

lemma uuIsInvar_isRevNth_equalsU: "uuIsInvar isRevNth_equalsU"
apply (cases isRevNth_equalsU rule: uuIsInvar)
by (auto simp: uu_defs isRevNth_equalsU_def)

lemma invar_isRevNth_equalsU: "invar isRevNth_equalsU"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_isRevNth_equalsU uIsInvar_isRevNth_equalsU
uuIsInvar_isRevNth_equalsU by auto

lemmas isRevNth_equalsU1 =
holdsIstate_invar[OF holdsIstate_isRevNth_equalsU invar_isRevNth_equalsU]

theorem isRevNth_equalsU:
assumes a: "reach s" and r: "isRevNth s confID uID papID n" "isRevNth s confID uID1 papID n"
shows "uID = uID1"
using isRevNth_equalsU1[OF a] r unfolding isRevNth_equalsU_def by blast

(* The reviews form a compact interval (with no gaps): *)
definition reviews_compact :: "state \<Rightarrow> bool" where
"reviews_compact s \<equiv>
 \<forall> confID papID n.
    papID \<in>\<in> paperIDs s confID \<and> n < length (reviewsPaper (paper s papID)) \<longrightarrow>
   (\<exists> uID. isRevNth s confID uID papID n)"

lemma holdsIstate_reviews_compact: "holdsIstate reviews_compact"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def reviews_compact_def by auto

lemma cIsInvar_reviews_compact: "cIsInvar reviews_compact"
apply(cases reviews_compact rule: cIsInvar)
apply(auto simp: c_defs reviews_compact_def
isRevNth_getAllPaperIDs isRev_def2 isRevNth_paperIDs paperIDs_equals less_SucI)
using paperIDs_confIDs
 apply fastforce
apply metis
apply metis
apply metis
using less_Suc_eq apply auto[1]
apply metis
done

lemma uIsInvar_reviews_compact: "uIsInvar reviews_compact"
apply(cases reviews_compact rule: uIsInvar)
by(fastforce simp: u_defs reviews_compact_def
isRevNth_getAllPaperIDs isRev_def2 isRevNth_paperIDs paperIDs_equals less_SucI)+

lemma uuIsInvar_reviews_compact: "uuIsInvar reviews_compact"
apply (cases reviews_compact rule: uuIsInvar)
by(fastforce simp: uu_defs reviews_compact_def
isRevNth_getAllPaperIDs isRev_def2 isRevNth_paperIDs paperIDs_equals less_SucI)+

lemma invar_reviews_compact: "invar reviews_compact"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_reviews_compact uIsInvar_reviews_compact
uuIsInvar_reviews_compact by auto

lemmas reviews_compact1 =
holdsIstate_invar[OF holdsIstate_reviews_compact invar_reviews_compact]

theorem reviews_compact:
assumes "reach s" and "n < length (reviewsPaper (paper s pid))"
and "pid \<in>\<in> paperIDs s cid"
shows "\<exists> uid. isRevNth s cid uid pid n"
using reviews_compact1 assms unfolding reviews_compact_def by blast


(* The list of roles for each conference-user is nonrepetitive: *)
definition roles_nonrep :: "state \<Rightarrow> bool" where
"roles_nonrep s \<equiv>
 \<forall> confID uID.
    distinct (roles s confID uID)"

lemma holdsIstate_roles_nonrep: "holdsIstate roles_nonrep"
unfolding IO_Automaton.holdsIstate_def istate_def istate_def roles_nonrep_def by auto

lemma cIsInvar_roles_nonrep: "cIsInvar roles_nonrep"
apply(cases roles_nonrep rule: cIsInvar)
by (auto simp: c_defs roles_nonrep_def
isRevNth_getAllPaperIDs isRev_def2 isRevNth_paperIDs paperIDs_equals less_SucI)

lemma uIsInvar_roles_nonrep: "uIsInvar roles_nonrep"
apply(cases roles_nonrep rule: uIsInvar)
by(fastforce simp: u_defs roles_nonrep_def
isRevNth_getAllPaperIDs isRev_def2 isRevNth_paperIDs paperIDs_equals less_SucI)+

lemma uuIsInvar_roles_nonrep: "uuIsInvar roles_nonrep"
apply (cases roles_nonrep rule: uuIsInvar)
by(fastforce simp: uu_defs roles_nonrep_def
isRevNth_getAllPaperIDs isRev_def2 isRevNth_paperIDs paperIDs_equals less_SucI)+

lemma invar_roles_nonrep: "invar roles_nonrep"
unfolding invar_cIsInvar_uIsInvar_uuIsInvar
using cIsInvar_roles_nonrep uIsInvar_roles_nonrep
uuIsInvar_roles_nonrep by auto

lemmas roles_nonrep1 =
holdsIstate_invar[OF holdsIstate_roles_nonrep invar_roles_nonrep]

theorem roles_nonrep:
assumes "reach s"
shows "distinct (roles s confID uID)"
using roles_nonrep1 assms unfolding roles_nonrep_def by blast


subsection\<open>Properties of the step function\<close>

lemma step_outErr_eq: "step s a = (outErr, s') \<Longrightarrow> s'= s"
apply (cases a)
  subgoal for x1 apply (cases x1, simp_all add: c_defs) .
  subgoal for x2 apply (cases x2, simp_all add: u_defs) .
  subgoal for x3 apply (cases x3, simp_all add: uu_defs) .
  by auto

lemma phase_increases:
assumes "step s a = (ou,s')"
shows "phase s cid \<le> phase s' cid"
using assms
apply (cases a)
  subgoal for x1 apply(cases x1) apply(auto simp: c_defs) .
  subgoal for x2 apply(cases x2) apply(auto simp: u_defs) .
  subgoal for x3 apply(cases x3) apply(auto simp: uu_defs) .
  by auto

lemma phase_increases2: "phase s CID \<le> phase (snd (step s a)) CID"
by (metis phase_increases snd_conv surj_pair)

lemma confIDs_mono:
assumes "step s a = (ou,s')" and "cid \<in>\<in> confIDs s"
shows "cid \<in>\<in> confIDs s'"
using assms
apply (cases a)
  subgoal for x1 apply(cases x1) apply(auto simp: c_defs) .
  subgoal for x2 apply(cases x2) apply(auto simp: u_defs) .
  subgoal for x3 apply(cases x3) apply(auto simp: uu_defs) .
  by auto

lemma userIDs_mono:
assumes "step s a = (ou,s')" and "uid \<in>\<in> userIDs s"
shows "uid \<in>\<in> userIDs s'"
using assms
apply (cases a)
  subgoal for x1 apply(cases x1) apply(auto simp: c_defs) .
  subgoal for x2 apply(cases x2) apply(auto simp: u_defs) .
  subgoal for x3 apply(cases x3) apply(auto simp: uu_defs) .
  by auto

lemma paperIDs_mono:
assumes "step s a = (ou,s')" and "pid \<in>\<in> paperIDs s cid"
shows "pid \<in>\<in> paperIDs s' cid"
using assms
apply (cases a)
  subgoal for x1 apply(cases x1) apply(auto simp: c_defs) .
  subgoal for x2 apply(cases x2) apply(auto simp: u_defs) .
  subgoal for x3 apply(cases x3) apply(auto simp: uu_defs) .
  by auto

lemma isPC_persistent:
assumes "isPC s cid uid" and "step s a = (ou, s')"
shows "isPC s' cid uid"
using assms apply (cases a)
  subgoal for x1 apply(cases x1) apply(auto simp: c_defs) .
  subgoal for x2 apply(cases x2) apply(auto simp: u_defs) .
  subgoal for x3 apply(cases x3) apply(auto simp: uu_defs) .
  by auto

lemma isChair_persistent:
assumes "isChair s cid uid" and "step s a = (ou, s')"
shows "isChair s' cid uid"
using assms apply (cases a)
  subgoal for x1 apply(cases x1) apply(auto simp: c_defs) .
  subgoal for x2 apply(cases x2) apply(auto simp: u_defs) .
  subgoal for x3 apply(cases x3) apply(auto simp: uu_defs) .
  by auto


subsection \<open>Action-safety properties\<close>

lemma pref_Conflict_disPH:
assumes "reach s" and "pid \<in>\<in> paperIDs s cid" and "pref s uid pid \<noteq> Conflict" and "phase s cid = disPH"
and "step s a = (ou, s')"
shows "pref s' uid pid \<noteq> Conflict"
proof-
  have 1: "cid \<in>\<in> confIDs s" using assms by (metis geq_noPH_confIDs zero_less_Suc)
  thus ?thesis using assms
  apply(cases a)
    subgoal for x1 apply(cases x1, auto simp: c_defs getAllPaperIDs_def)
       apply (metis Suc_inject Zero_not_Suc paperIDs_equals)
      apply (metis Suc_inject Zero_not_Suc paperIDs_equals) .
    subgoal for x2 apply(cases x2, auto simp: u_defs)
      apply (metis Suc_inject Zero_not_Suc paperIDs_equals) .
    subgoal for x3 apply(cases x3, auto simp: uu_defs) .
    by auto
qed

lemma isRevNth_persistent:
assumes "reach s" and "isRevNth s cid uid pid n"
and "step s a = (ou, s')"
shows "isRevNth s' cid uid pid n"
using assms apply (cases a)
  subgoal for x1 apply(cases x1) apply(auto simp: c_defs roles_confIDs) .
  subgoal for x2 apply(cases x2) apply(auto simp: u_defs) .
  subgoal for x3 apply(cases x3) apply(auto simp: uu_defs) .
  by auto

lemma nonempty_decsPaper_persist:
assumes s: "reach s"
and pid: "pid \<in>\<in> paperIDs s cid"
and "decsPaper (paper s pid) \<noteq> []" and "step s a = (ou,s')"
shows "decsPaper (paper s' pid) \<noteq> []"
proof-
  have "cid \<in>\<in> confIDs s" using s pid by (metis paperIDs_confIDs)
  thus ?thesis using assms apply(cases a)
    subgoal for x1 apply(cases x1, auto simp: c_defs getAllPaperIDs_def) .
    subgoal for x2 apply(cases x2, auto simp: u_defs) .
    subgoal for x3 apply(cases x3, auto simp: uu_defs) .
    by auto
qed

lemma nonempty_reviews_persist:
assumes s: "reach s"
and r: "isRevNth s cid uid pid n"
and "(reviewsPaper (paper s pid))!n \<noteq> []" and "step s a = (ou,s')"
shows "(reviewsPaper (paper s' pid))!n \<noteq> []"
proof-
  have pid: "pid \<in>\<in> paperIDs s cid" using s r by (metis isRevNth_paperIDs)
  have cid: "cid \<in>\<in> confIDs s" using s pid by (metis paperIDs_confIDs)
  have n: "n < length (reviewsPaper (paper s pid))" using s r by (metis isRevNth_less_length)
  show ?thesis using assms pid cid n apply(cases a)
    subgoal for x1 apply(cases x1, auto simp: c_defs getAllPaperIDs_def) .
    subgoal for x2 apply(cases x2, auto simp: u_defs)
      apply (metis not_Cons_self2 nth_list_update_eq nth_list_update_neq) .
    subgoal for x3 apply(cases x3, auto simp: uu_defs)
      apply (metis list.distinct(1) nth_list_update_eq nth_list_update_neq) .
    by auto
qed

lemma revPH_pref_persists:
assumes "reach s"
"pid \<in>\<in> paperIDs s cid" and "phase s cid \<ge> revPH"
and "step s a = (ou,s')"
shows "pref s' uid pid = pref s uid pid"
using assms apply(cases a)
  subgoal for x1 apply(cases x1) apply(auto simp: c_defs paperIDs_getAllPaperIDs)
    using paperIDs_equals apply fastforce
    using paperIDs_equals apply fastforce .
  subgoal for x2 apply(cases x2) apply(auto simp: u_defs)
    using paperIDs_equals apply fastforce .
  subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
  by auto


subsection \<open>Miscellaneous\<close>

(* Simps bringing the "paper" field all the way to the left---useful for situations
   where the states are equal everywhere but on the paper field. *)
lemma updates_commute_paper:
 "\<And> uu. s \<lparr>confIDs := uu, paper := pp\<rparr> = s \<lparr>paper := pp, confIDs := uu\<rparr>"
 "\<And> uu. s \<lparr>conf := uu, paper := pp\<rparr> = s \<lparr>paper := pp, conf := uu\<rparr>"

 "\<And> uu. s \<lparr>userIDs := uu, paper := pp\<rparr> = s \<lparr>paper := pp, userIDs := uu\<rparr>"
 "\<And> uu. s \<lparr>pass := uu, paper := pp\<rparr> = s \<lparr>paper := pp, pass := uu\<rparr>"
 "\<And> uu. s \<lparr>user := uu, paper := pp\<rparr> = s \<lparr>paper := pp, user := uu\<rparr>"
 "\<And> uu. s \<lparr>roles := uu, paper := pp\<rparr> = s \<lparr>paper := pp, roles := uu\<rparr>"

 "\<And> uu. s \<lparr>paperIDs := uu, paper := pp\<rparr> = s \<lparr>paper := pp, paperIDs := uu\<rparr>"

 "\<And> uu. s \<lparr>pref := uu, paper := pp\<rparr> = s \<lparr>paper := pp, pref := uu\<rparr>"
 "\<And> uu. s \<lparr>voronkov := uu, paper := pp\<rparr> = s \<lparr>paper := pp, voronkov := uu\<rparr>"
 "\<And> uu. s \<lparr>news := uu, paper := pp\<rparr> = s \<lparr>paper := pp, news := uu\<rparr>"
 "\<And> uu. s \<lparr>phase := uu, paper := pp\<rparr> = s \<lparr>paper := pp, phase := uu\<rparr>"
by (auto intro: state.equality)


(* The implication between the implicit- and explicit conference ID selectors *)

lemma isAUT_imp_isAut:
assumes "reach s" and "pid \<in>\<in> paperIDs s cid" and "isAUT s uid pid"
shows "isAut s cid uid pid"
by (metis assms isAUT_def isAut_paperIDs paperIDs_equals)

lemma isREVNth_imp_isRevNth:
assumes "reach s" and "pid \<in>\<in> paperIDs s cid" and "isREVNth s uid pid n"
shows "isRevNth s cid uid pid n"
by (metis assms isREVNth_def isRevNth_paperIDs paperIDs_equals)


(* BEGIN phase properties *)

lemma phase_increases_validTrans:
assumes "validTrans (Trans s a ou s')"
shows "phase s cid \<le> phase s' cid"
using assms apply(cases a)
  subgoal for x1 apply(cases x1, auto simp: c_defs split: if_splits) .
  subgoal for x2 apply(cases x2, auto simp: u_defs split: if_splits paper.splits) .
  subgoal for x3 apply(cases x3, auto simp: uu_defs split: if_splits paper.splits) .
  by auto

lemma phase_increases_validTrans2:
assumes "validTrans tr"
shows "phase (srcOf tr) cid \<le> phase (tgtOf tr) cid"
using assms phase_increases_validTrans by (cases tr) auto

lemma phase_increases_trace:
assumes vtr: "valid tr" and ij: "i \<le> j" and j: "j < length tr"
shows "phase (srcOf (tr!i)) cid \<le> phase (srcOf (tr!j)) cid"
proof(cases "i < j")
case False thus ?thesis using ij by auto
next
case True thus ?thesis
using j proof(induction j)
  case (Suc jj)
  show ?case
  proof(cases "jj = i")
    case True
    obtain tr1 tr2 where tr: "tr = tr1 @ (tr!i) # (tr!(Suc jj)) # tr2"
    unfolding True by (metis Cons_nth_drop_Suc Suc.prems(2) Suc_lessD True id_take_nth_drop)
    hence "validTrans (tr!i) \<and> tgtOf (tr!i) = srcOf (tr!(Suc jj))"
    unfolding True by (metis Suc Suc_lessD True valid_validTrans_nth valid_validTrans_nth_srcOf_tgtOf vtr)
    thus ?thesis using phase_increases_validTrans Suc by (cases "tr!i") auto
  next
    case False hence 1: "i < jj \<and> jj < length tr" using Suc by auto
    hence "phase (srcOf (tr!i)) cid \<le> phase (srcOf (tr!jj)) cid" using Suc by auto
    also have "phase (srcOf (tr!jj)) cid \<le> phase (tgtOf (tr!jj)) cid"
    using phase_increases_validTrans2 by (metis 1 valid_validTrans_nth vtr)
    also have "... = phase (srcOf (tr!(Suc jj))) cid"
    by (metis Suc valid_validTrans_nth_srcOf_tgtOf vtr)
    finally show ?thesis .
  qed
qed auto
qed

lemma phase_increases_trace_srcOf_tgtOf:
assumes vtr: "valid tr" and ij: "i \<le> j" and j: "j < length tr"
shows "phase (srcOf (tr!i)) cid \<le> phase (tgtOf (tr!j)) cid"
  using phase_increases_trace[OF assms]
  using j le_trans phase_increases_validTrans2 valid_validTrans_nth vtr by blast

lemma phase_increases_trace_srcOf_hd:
assumes v: "valid tr" and l: "length tr > 1" and "i < length tr"
shows "phase (srcOf (hd tr)) cid \<le> phase (srcOf (tr!i)) cid"
using phase_increases_trace assms
by (metis gr_implies_not0 hd_Cons_tl leI length_0_conv nth_Cons_0)

lemma phase_increases_trace_srcOf_last:
assumes v: "valid tr" and l: "length tr > 1" and i: "i < length tr"
shows "phase (srcOf (tr!i)) cid \<le> phase (srcOf (last tr)) cid"
proof-
  have 1: "last tr = tr!(length tr - 1)"
  by (metis i last_conv_nth list.size(3) not_less0)
  show ?thesis unfolding 1 using assms
  by (metis Suc_diff_1 Suc_leI Suc_le_mono gr_implies_not0 length_0_conv
          length_greater_0_conv lessI phase_increases_trace)
qed

lemma phase_increases_trace_srcOf_tgtOf_last:
assumes v: "valid tr" and l: "length tr > 1" and i: "i < length tr"
shows "phase (srcOf (tr!i)) cid \<le> phase (tgtOf (last tr)) cid"
proof-
  have 1: "last tr = tr!(length tr - 1)"
  by (metis i last_conv_nth list.size(3) not_less0)
  have "phase (srcOf (tr!i)) cid \<le> phase (srcOf (last tr)) cid" using
  phase_increases_trace_srcOf_last[OF assms] .
  also have "... \<le> phase (tgtOf (last tr)) cid" unfolding 1
  by (metis Suc_le_D diff_Suc_1 l lessI less_eq_Suc_le phase_increases_validTrans2 v valid_validTrans_nth)
  finally show ?thesis by (simp add: le_funD)
qed

lemma valid_tgtPf_last_srcOf:
assumes "valid tr" and "s \<in>\<in> map tgtOf tr"
shows "s = tgtOf (last tr) \<or> s \<in>\<in> map srcOf tr"
using assms by induction auto

lemma phase_constant:
assumes v: "valid tr" and l: "length tr > 0" and
ph: "phase (srcOf (hd tr)) cid = phase (tgtOf (last tr)) cid"
shows "set (map (\<lambda> trn. phase (srcOf trn) cid) tr) \<subseteq> {phase (srcOf (hd tr)) cid} \<and>
       set (map (\<lambda> trn. phase (tgtOf trn) cid) tr) \<subseteq> {phase (srcOf (hd tr)) cid}"
proof(cases "length tr > 1")
  case False
  then obtain trn where tr: "tr = [trn]" using l by (cases tr) auto
  show ?thesis using assms unfolding tr by auto
next
  case True note l = True
  show ?thesis proof safe
    {fix ph assume "ph \<in>\<in> map (\<lambda> trn. phase (srcOf trn) cid) tr"
     then obtain i where i: "i < length tr" and phe: "ph = phase (srcOf(tr!i)) cid"
     by (smt comp_apply in_set_conv_nth length_map nth_map)
     have "phase (srcOf (hd tr)) cid \<le> ph"
     unfolding phe using v l i phase_increases_trace_srcOf_hd by blast
     moreover have "ph \<le> phase (tgtOf (last tr)) cid"
     unfolding phe using v l i phase_increases_trace_srcOf_tgtOf_last by auto
     ultimately show "ph = phase (srcOf (hd tr)) cid" using ph by simp
    } note 0 = this
    fix ph assume "ph \<in>\<in> map (\<lambda> trn. phase (tgtOf trn) cid) tr"
    then obtain s where "s \<in>\<in> map tgtOf tr" and phs: "ph = phase s cid" by auto
    hence "s = tgtOf (last tr) \<or> s \<in>\<in> map srcOf tr" using valid_tgtPf_last_srcOf[OF v] by auto
    thus "ph = phase (srcOf (hd tr)) cid" using 0[of ph] ph unfolding phs by auto
  qed
qed

lemma phase_cases:
assumes "step s a = (ou, s')"
obtains (noPH) "\<not> cid \<in>\<in> confIDs s \<or> phase s cid = noPH"
(* the conf. does not exist yet or the voronkov has not yet approved it *)
      | (Id) "phase s' cid = phase s cid"
      | (Upd) uid p ph where "phase s' cid = ph" "a = Uact (uPhase cid uid p ph)" "e_updatePhase s cid uid p ph"
using assms proof (cases a)
  case (Cact ca)
  then show thesis using assms
    by (cases ca) (auto simp: c_defs split: if_splits intro: that)
next
  case (Uact ua)
  then show thesis using assms
    apply (cases ua)
    subgoal by (auto simp: u_defs split: if_splits paper.splits intro: that)
    subgoal for x21 apply(cases "x21 = cid")
      by (auto simp: u_defs split: if_splits paper.splits intro: that)
    subgoal for x31 apply(cases "cid = x31")
      by (auto simp: u_defs split: if_splits paper.splits intro: that)
    by (auto simp: u_defs split: if_splits paper.splits intro: that)
next
  case (UUact uua)
  then show thesis using assms by (cases uua) (auto simp: uu_defs split: if_splits paper.splits intro: that)
qed auto

lemma phase_mono: "reachFrom s s' \<Longrightarrow> phase s cid \<le> phase s' cid"
proof (induction rule: reachFrom_step_induct)
  case (Step s' a ou s'')
    then show ?case
    proof (cases a)
      case (Cact cAct) with Step show ?thesis by (cases cAct) (auto simp add: c_defs split: if_splits) next
      case (Uact uAct) with Step show ?thesis by (cases uAct) (auto simp add: u_defs split: if_splits paper.split) next
      case (UUact uAct) with Step show ?thesis by (cases uAct) (auto simp add: uu_defs split: if_splits paper.split)
    qed (auto)
qed (auto)

lemma validTrans_rAct_lAct_srcOf_tgtOf:
assumes "validTrans trn"
and "actOf trn = Ract rAct \<or> actOf trn = Lact lAct"
shows "tgtOf trn = srcOf trn"
using assms by (cases trn) auto

lemma valid_rAct_lAct_srcOf_tgtOf:
assumes "valid tr"
and "\<And> a. a \<in>\<in> map actOf tr \<Longrightarrow> (\<exists> rAct. a = Ract rAct) \<or> (\<exists> lAct. a = Lact lAct)"
shows "srcOf ` (set tr) \<subseteq> {srcOf (hd tr)}"
using assms by (induction) (simp_all, metis validTrans_rAct_lAct_srcOf_tgtOf)

lemma validFrom_rAct_lAct_srcOf_tgtOf:
assumes "validFrom s tr"
and "\<And> a. a \<in>\<in> map actOf tr \<Longrightarrow> (\<exists> rAct. a = Ract rAct) \<or> (\<exists> lAct. a = Lact lAct)"
shows "srcOf ` (set tr) \<subseteq> {s}"
using assms valid_rAct_lAct_srcOf_tgtOf unfolding validFrom_def by auto

lemma tgtOf_last_traceOf_Ract_Lact[simp]:
assumes "al \<noteq> []" "set al \<subseteq> range Ract \<union> range Lact"
shows "tgtOf (last (traceOf s al)) = s"
using assms by (induction al arbitrary: s) auto

(* END phase properties *)

lemma paperIDs_cases:
assumes "step s a = (ou, s')"
obtains (Id) "paperIDs s' cid = paperIDs s cid"
      | (Create) cid uid p pid tit ab  where
           "paperIDs s' cid = pid # paperIDs s cid" "a = Cact (cPaper cid uid p pid tit ab)"
           "e_createPaper s cid uid p pid tit ab"
using assms proof (cases a)
  case (Cact ca)
  then show thesis using assms
    by (cases ca) (auto simp: c_defs split: if_splits intro: that)
next
  case (Uact ua)
  then show thesis using assms
    by (cases ua) (auto simp: u_defs split: if_splits paper.splits intro: that)
next
  case (UUact ua)
  then show thesis using assms
    by (cases ua) (auto simp: uu_defs split: if_splits paper.splits intro: that)
qed auto

lemma paperIDs_decPH_const:
assumes s: "step s a = (ou, s')" and "phase s cid > subPH"
shows "paperIDs s' cid = paperIDs s cid"
  using assms
  apply (elim paperIDs_cases[where cid = cid])
  subgoal .
  subgoal for cida
    apply(cases "cida = cid", auto)
    using s by (auto simp: c_defs) .

end
