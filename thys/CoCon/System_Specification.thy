section \<open>System specification\<close>

text \<open>This section formalizes the CoCon system as an I/O automaton.
We call the inputs ``actions''.\<close>

theory System_Specification
imports Prelim
begin

subsection \<open>System state\<close>


text \<open>The superuser of the system is called ``voronkov'',
as a form acknowledgement for our inspiration from EasyChair
when creating CoCon.
\<close>

record state =
  confIDs :: "confID list"
  conf :: "confID \<Rightarrow> conf"
  (*  *)
  userIDs :: "userID list"
  pass :: "userID \<Rightarrow> password"
  user :: "userID \<Rightarrow> user"
  roles :: "confID \<Rightarrow> userID \<Rightarrow> role list"
  (*  *)
  paperIDs :: "confID \<Rightarrow> paperID list"
  paper :: "paperID \<Rightarrow> paper"
  (*  *)
  pref :: "userID \<Rightarrow> paperID \<Rightarrow> preference" (* preference, including eventual conflicts *)
  (*  *)
  voronkov :: "userID"
  (*  *)
  news :: "confID \<Rightarrow> string list"
  phase :: "confID \<Rightarrow> phase" (* the current phase *)
  (*  *)


(* Note: Some of the fields are redundant, e.g., paperIDs can in principle be recovered from "roles";
however, this and other redundant fields are used very often, so it is efficient to keep them *)


(* Various discriminators ("is") and selectors ("get") on the database: *)
abbreviation isPC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> bool" (*  program committee (PC) membership *) where
"isPC s confID uID \<equiv> PC \<in>\<in> roles s confID uID"
abbreviation isChair :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> bool" (* being one of the conference chairs *)  where
"isChair s confID uID \<equiv> Chair \<in>\<in> roles s confID uID"
abbreviation isAut :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> paperID \<Rightarrow> bool" (*  authorship of a certain paper *) where
"isAut s confID uID papID \<equiv> Aut papID \<in>\<in> roles s confID uID"
definition isAutSome :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> bool" (*  authorship of some paper *) where
"isAutSome s confID uID \<equiv> list_ex (isAut s confID uID) (paperIDs s confID)"
(* all the authors of a given paper: *)
definition authors :: "state \<Rightarrow> confID \<Rightarrow> paperID \<Rightarrow> userID list" where
"authors s confID papID \<equiv> filter (\<lambda> uID. isAut s confID uID papID) (userIDs s)"
abbreviation isRevNth :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> paperID \<Rightarrow> nat \<Rightarrow> bool" (*  paper reviewer (nth review) *)
where
"isRevNth s confID uID papID n \<equiv> Rev papID n \<in>\<in> roles s confID uID"
definition isRev :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> paperID \<Rightarrow> bool" (*  paper reviewer *) where
"isRev s confID uID papID \<equiv> list_ex (isRevRoleFor papID) (roles s confID uID)"
(* Get the reviewer role for a certain triple (user, conference, paper), if any: *)
definition getRevRole :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> paperID \<Rightarrow> role option" where
"getRevRole s confID uID papID \<equiv> List.find (isRevRoleFor papID) (roles s confID uID)"
(* get the n-th review of a paper *)
definition getNthReview :: "state \<Rightarrow> paperID \<Rightarrow> nat \<Rightarrow> review" where
"getNthReview s papID n \<equiv> (reviewsPaper (paper s papID))!n"
(* get all the paper IDs (for all conferences) from the system: *)
definition getAllPaperIDs :: "state \<Rightarrow> paperID list" where
"getAllPaperIDs s \<equiv> concat [paperIDs s confID. confID \<leftarrow> confIDs s]"
definition getReviewIndex :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> paperID \<Rightarrow> nat" where
"getReviewIndex s confID uID papID \<equiv>
 case getRevRole s confID uID papID of Some (Rev papID' n) \<Rightarrow> n"
(* get, for a conference and a paper, the reviews together with the IDs of the reviewers: *)
definition getReviewersReviews :: "state \<Rightarrow> confID \<Rightarrow> paperID \<Rightarrow> (userID * review) list" where
"getReviewersReviews s confID papID \<equiv>
 [(uID, getNthReview s papID (getReviewIndex s confID uID papID)).
    uID \<leftarrow> userIDs s,
    isRev s confID uID papID
 ]"

(* Not used in the implementation: *)
definition isAUT :: "state \<Rightarrow> userID \<Rightarrow> paperID \<Rightarrow> bool" where
"isAUT s uID papID \<equiv> \<exists> confID. isAut s confID uID papID"
definition isREVNth :: "state \<Rightarrow> userID \<Rightarrow> paperID \<Rightarrow> nat \<Rightarrow> bool" where
"isREVNth s uID papID n \<equiv> \<exists> confID. isRevNth s confID uID papID n"


lemma isRev_getRevRole:
assumes "isRev s confID uID papID"
shows "getRevRole s confID uID papID \<noteq> None"
using assms list_ex_find unfolding isRev_def getRevRole_def by auto

lemma getRevRole_Some:
assumes "getRevRole s confID uID papID = Some role"
shows "\<exists> n. role = Rev papID n"
using assms unfolding getRevRole_def unfolding find_Some_iff apply (cases role, auto)
by (metis isRevRoleFor.simps)+

lemma isRev_getRevRole2:
assumes "isRev s confID uID papID"shows "\<exists> n. getRevRole s confID uID papID = Some (Rev papID n)"
using assms getRevRole_Some by (cases "getRevRole s confID uID papID") (auto simp: isRev_getRevRole)

lemma isRev_imp_isRevNth_getReviewIndex:
assumes "isRev s confID uID papID"
shows "isRevNth s confID uID papID (getReviewIndex s confID uID papID)"
proof-
  obtain n where 1: "getRevRole s confID uID papID = Some (Rev papID n)"
  using isRev_getRevRole2[OF assms] by auto
  hence "isRevNth s confID uID papID n"
  unfolding getRevRole_def unfolding find_Some_iff by auto
  moreover have "getReviewIndex s confID uID papID = n" using 1 unfolding getReviewIndex_def by simp
  ultimately show ?thesis by auto
qed

(* nonexecutable, but more useful version of the definition: *)
lemma isRev_def2:
"isRev s confID uID papID \<longleftrightarrow> (\<exists> n. isRevNth s confID uID papID n)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A thus ?B using isRev_imp_isRevNth_getReviewIndex by blast
next
  assume ?B thus ?A unfolding isRev_def list_ex_iff by force
qed

(* more precise definition, but not always needed: *)
lemma isRev_def3:
"isRev s confID uID papID \<longleftrightarrow> isRevNth s confID uID papID (getReviewIndex s confID uID papID)"
by (metis isRev_def2 isRev_imp_isRevNth_getReviewIndex)

lemma getFreshPaperID_getAllPaperIDs[simp]:
  assumes "confID \<in>\<in> confIDs s"
  shows "\<not> getFreshPaperID (getAllPaperIDs s) \<in>\<in> paperIDs s confID"
  using assms getFreshPaperID[of "getAllPaperIDs s"]
  by (auto simp: getAllPaperIDs_def)

lemma getRevRole_Some_Rev:
"getRevRole s cid uid pid = Some (Rev pid' n) \<Longrightarrow> pid' = pid"
by (metis getRevRole_Some role.inject)

lemma getRevRole_Some_Rev_isRevNth:
"getRevRole s cid uid pid = Some (Rev pid' n) \<Longrightarrow> isRevNth s cid uid pid n"
  unfolding getRevRole_def find_Some_iff
  apply (elim exE)
  subgoal for i
    apply(cases "roles s cid uid ! i")
       apply auto
    by (metis nth_mem)
  done

(* This assumes that the list of conference IDs has exactly one element: *)
definition IDsOK :: "state \<Rightarrow> confID list \<Rightarrow> userID list \<Rightarrow> paperID list \<Rightarrow> bool"
where
"IDsOK s cIDs uIDs papIDs \<equiv>
 list_all (\<lambda> confID. confID \<in>\<in> confIDs s) cIDs \<and>
 list_all (\<lambda> uID. uID \<in>\<in> userIDs s) uIDs \<and>
 list_all (\<lambda> papID. papID \<in>\<in> paperIDs s (hd cIDs)) papIDs"


subsection \<open>The actions\<close>

subsubsection\<open>Initialization of the system\<close>

definition istate :: state
where
"istate \<equiv>
 \<lparr>
  confIDs = [],
  conf = (\<lambda> confID. emptyConf),
  userIDs = [voronkovUserID],
  pass = (\<lambda> uID. emptyPass),
  user = (\<lambda> uID. emptyUser),
  roles = (\<lambda> confID uID. []),
  paperIDs = (\<lambda> confID. []),
  paper = (\<lambda> papID. emptyPaper),
  pref = (\<lambda> uID papID. NoPref),
  voronkov = voronkovUserID,
  news = (\<lambda> confID. []),
  phase = (\<lambda> confID. noPH)
 \<rparr>"



subsubsection\<open>Actions unbound by any existing conference (with its phases)\<close>

(* Create new user (user) in the system: *)
(* if given user ID already taken, generate a fresh one *)
definition createUser ::  "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> state"
where
"createUser s uID p name info email \<equiv>
 let uIDs = userIDs s
 in
 s \<lparr>userIDs := uID # uIDs,
    user := (user s) (uID := User name info email),
    pass := (pass s) (uID := p)\<rparr>"
(* the the web interface, one should prompt the user multiple times for entering
 an unused ID *)

definition e_createUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool" where
"e_createUser s uID p name info email \<equiv>
 \<not> uID \<in>\<in> userIDs s"

(* updates information for user (himself), including password: *)
definition updateUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> password \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> state"
where
"updateUser s uID p p' name info email \<equiv>
 s \<lparr>user := (user s) (uID := User name info email),
    pass := (pass s) (uID := p')\<rparr>"

definition e_updateUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> password \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool"
where
"e_updateUser s uID p p' name info email \<equiv>
 IDsOK s [] [uID] [] \<and> pass s uID = p"


(* read if the current user is the voronkov: *)
definition readAmIVoronkov :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"readAmIVoronkov s uID p \<equiv>
 uID = voronkov s "

definition e_readAmIVoronkov :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_readAmIVoronkov s uID p \<equiv>
 IDsOK s [] [uID] [] \<and> pass s uID = p"

(* Read the name and info of a user (except for password): *)
(* There are several needs for this primitive action:
   -- either I read my own info
   -- or I am an author, and therefore I read the PC members' name and info to declare a conflict
   -- or I am a chair, and therefore I read all PC members's info to assign papers for reviewing
   -- or I am an author and need to add coauthors
*)
definition readUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> string * string * string"
where
"readUser s uID p uID' \<equiv>
 case user s uID' of User name info email \<Rightarrow> (name, info, email)"

definition e_readUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_readUser s uID p uID' \<equiv>
 IDsOK s [] [uID,uID'] [] \<and> pass s uID = p"

(* Request for a new conference *)

(* The request takes place by creating a new conference with ID assigned as above for users.
The conference will remain in the default "noPH" phase until aproval.
The creator becomes a chair (a fortiori a PC member). *)
definition createConf :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> string \<Rightarrow> string \<Rightarrow> state"
where
"createConf s confID uID p name info \<equiv>
 let confIDs = confIDs s
 in
 s \<lparr>confIDs := confID # confIDs,
    conf := (conf s) (confID := Conf name info),
    roles := fun_upd2 (roles s) confID uID [PC,Chair]
   \<rparr>"
(* again, in the web interface the user will be prompted repeatedly until he gets it right *)

definition e_createConf :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool"
where
"e_createConf s confID uID p name info \<equiv>
 IDsOK s [] [uID] [] \<and> pass s uID = p \<and>
 \<not> confID \<in>\<in> confIDs s"

(* Read the info of a conference: any user can do it  *)
definition readConf :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> string * string * (role list) * phase"
where
"readConf s confID uID p \<equiv>
 (nameConf (conf s confID), infoConf (conf s confID),
  [rl \<leftarrow> roles s confID uID. \<not> isRevRole rl], phase s confID)"

definition e_readConf :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_readConf s confID uID p \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p"

(* list all conferences: *)
definition listConfs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> confID list"
where
"listConfs s uID p \<equiv>
 confIDs s"

definition e_listConfs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listConfs s uID p \<equiv>
 IDsOK s [] [uID] [] \<and> pass s uID = p \<and>
 uID = voronkov s"

(* list conferences awaiting approval: *)
definition listAConfs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> confID list"
where
"listAConfs s uID p \<equiv>
 [confID. confID \<leftarrow> confIDs s, phase s confID = noPH]"

definition e_listAConfs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listAConfs s uID p \<equiv>
 IDsOK s [] [uID] [] \<and> pass s uID = p \<and>
 uID = voronkov s"

(* list conferences in the submission phase: any user can see this *)
definition listSConfs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> confID list"
where
"listSConfs s uID p \<equiv>
 [confID. confID \<leftarrow> confIDs s, phase s confID = subPH]"

definition e_listSConfs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listSConfs s uID p \<equiv>
 IDsOK s [] [uID] [] \<and> pass s uID = p"

(* list my conferences: *)
definition listMyConfs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> confID list"
where
"listMyConfs s uID p \<equiv>
 [confID. confID \<leftarrow> confIDs s , roles s confID uID \<noteq> []]"

definition e_listMyConfs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listMyConfs s uID p \<equiv>
 IDsOK s [] [uID] [] \<and> pass s uID = p"

(* list all users of the system (useful when assigning coauthors to papers): *)
definition listAllUsers :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID list"
where
"listAllUsers s uID p \<equiv>
 userIDs s"

definition e_listAllUsers :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listAllUsers s uID p \<equiv>
 IDsOK s [] [uID] [] \<and> pass s uID = p"

(* list all paper IDs of the system (useful whn generating a fresh paper ID): *)
definition listAllPapers :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID list"
where
"listAllPapers s uID p \<equiv>
 getAllPaperIDs s"

definition e_listAllPapers :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listAllPapers s uID p \<equiv>
 IDsOK s [] [uID] [] \<and> pass s uID = p"


subsubsection\<open>Actions available in the noPH phase\<close>

(* Approving a new conference should be done by the voronkov, and happens by changing
the phase from noPH to setPH.
This is an update action: it updates the conference approval status
Note that, after approval, the voronkov should not have further access to the conference:
he can only act if the phase is noPH. *)
definition updateConfA :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> state"
where
"updateConfA s confID uID p \<equiv>
 s \<lparr>phase := (phase s) (confID := setPH)\<rparr>"

definition e_updateConfA :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_updateConfA s confID uID p \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 uID = voronkov s \<and> phase s confID = noPH"


subsubsection\<open>Actions available in the setPH phase\<close>

(* make a user a PC member *)
definition createPC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> state"
where
"createPC s confID uID p uID' \<equiv>
 let rls = roles s confID uID'
 in
 s \<lparr>roles := fun_upd2 (roles s) confID uID' (List.insert PC rls)\<rparr>"

definition e_createPC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_createPC s confID uID p uID' \<equiv>
 let uIDs = userIDs s
 in
 IDsOK s [confID] [uID,uID'] [] \<and> pass s uID = p \<and>
 phase s confID = setPH \<and> isChair s confID uID"

(* make a user a chair (a fortiori a PC member) *)
definition createChair :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> state"
where
"createChair s confID uID p uID' \<equiv>
 let rls = roles s confID uID'
 in
 s \<lparr>roles := fun_upd2 (roles s) confID uID' (List.insert PC (List.insert Chair rls))\<rparr>"

definition e_createChair :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_createChair s confID uID p uID' \<equiv>
 let uIDs = userIDs s
 in
 IDsOK s [confID] [uID,uID'] [] \<and> pass s uID = p \<and>
 phase s confID = setPH \<and> isChair s confID uID"


subsubsection\<open>Actions available starting from the setPH phase\<close>

definition updatePhase :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> phase \<Rightarrow> state" where
"updatePhase s confID uID p ph \<equiv>
 s \<lparr>phase := (phase s) (confID := ph)\<rparr>"

definition e_updatePhase :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> phase \<Rightarrow> bool" where
"e_updatePhase s confID uID p ph \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 phase s confID \<ge> setPH \<and> phase s confID < closedPH \<and> isChair s confID uID \<and>
 ph = SucPH (phase s confID)"
(* The phase move is only allowed if the indicated phase is the successor of the current phase.
   Yet, in the kernel we also require the explicit indication of the phase for being able to track
   it for verification.  *)
(* In the web interface, the user is prompted with the question
"Are you sure you want to move to the next phase?" *)

(* Add an event, i.e., undestructively update the news: *)
definition uupdateNews :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> string \<Rightarrow> state"
where
"uupdateNews s confID uID p ev \<equiv>
 let evs = news s confID
 in
 s \<lparr>news := (news s) (confID := ev # evs)\<rparr>"

definition e_uupdateNews :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> string \<Rightarrow> bool"
where
"e_uupdateNews s confID uID p ev \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 phase s confID \<ge> setPH \<and> phase s confID < closedPH \<and> isChair s confID uID"

definition readNews :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> string list"
where
"readNews s confID uID p \<equiv>
 news s confID"

definition e_readNews :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_readNews s confID uID p \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 phase s confID \<ge> setPH \<and> isPC s confID uID"

(* list the committee members: *)
definition listPC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID list"
where
"listPC s confID uID p \<equiv>
 [uID. uID \<leftarrow> userIDs s, isPC s confID uID]"

definition e_listPC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listPC s confID uID p \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 (phase s confID \<ge> subPH \<or> (phase s confID \<ge> setPH \<and> isChair s confID uID))"

(* list the chairs: *)
definition listChair :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID list"
where
"listChair s confID uID p \<equiv>
 [uID. uID \<leftarrow> userIDs s, isChair s confID uID]"

definition e_listChair :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listChair s confID uID p \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 (phase s confID \<ge> subPH \<or> (phase s confID \<ge> setPH \<and> isChair s confID uID))"


subsubsection\<open>Actions available in the subPH phase\<close>

(* create new paper: *)
definition createPaper :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> string \<Rightarrow> string \<Rightarrow> state"
where
"createPaper s confID uID p papID title abstract \<equiv>
 let papIDs = paperIDs s confID;
     rls = roles s confID uID
 in
 s \<lparr>paperIDs := (paperIDs s) (confID := papID # papIDs),
    paper := (paper s) (papID := Paper title abstract NoPContent [] (Dis []) []),
    roles := fun_upd2 (roles s) confID uID (List.insert (Aut papID) rls),
    pref :=  fun_upd2 (pref s) uID papID Conflict\<rparr>"
(* this contains an update to the preference too, to make sure that a user does not end up
reviewing his own paper! note that preference can be set even if the author is not a reviewer,
which is OK*)

definition e_createPaper :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool"
where
"e_createPaper s confID uID p papID name info \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 phase s confID = subPH \<and>
 \<not> papID \<in>\<in> getAllPaperIDs s"

(* add author to a paper: only an author can do this *)
definition createAuthor :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> userID \<Rightarrow> state"
where
"createAuthor s confID uID p papID uID' \<equiv>
 let rls = roles s confID uID'
 in
 s \<lparr>roles := fun_upd2 (roles s) confID uID' (List.insert (Aut papID) rls),
    pref :=  fun_upd2 (pref s) uID' papID Conflict\<rparr>"
(* again, preference is set to Conflict *)

definition e_createAuthor :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> userID \<Rightarrow> bool"
where
"e_createAuthor s confID uID p papID uID' \<equiv>
 IDsOK s [confID] [uID,uID'] [papID] \<and> pass s uID = p \<and>
 phase s confID = subPH \<and> isAut s confID uID papID \<and> uID \<noteq> uID'"

(* update name (title) and info of paper: *)
definition updatePaperTA :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> string \<Rightarrow> string \<Rightarrow> state"
where
"updatePaperTA s confID uID p papID title abstract \<equiv>
 case paper s papID of Paper title' abstract' pc reviews dis decs \<Rightarrow>
 s \<lparr>paper := (paper s) (papID := Paper title abstract pc reviews dis decs)\<rparr>"

definition e_updatePaperTA :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool"
where
"e_updatePaperTA s confID uID p papID name info \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID = subPH \<and> isAut s confID uID papID"

(* upload new version of paper content: *)
definition updatePaperC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> pcontent \<Rightarrow> state"
where
"updatePaperC s confID uID p papID pc \<equiv>
 case paper s papID of Paper title abstract pc' reviews dis decs \<Rightarrow>
 s \<lparr>paper := (paper s) (papID := Paper title abstract pc reviews dis decs)\<rparr>"

definition e_updatePaperC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> pcontent \<Rightarrow> bool"
where
"e_updatePaperC s confID uID p papID pc \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID = subPH \<and> isAut s confID uID papID"

(* declare conflict of the authored paper with a committee member*)
definition createConflict :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> userID \<Rightarrow> state"
where
"createConflict s confID uID p papID uID' \<equiv>
 s \<lparr>pref := fun_upd2 (pref s) uID' papID Conflict\<rparr>"

definition e_createConflict :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> userID \<Rightarrow> bool"
where
"e_createConflict s confID uID p papID uID' \<equiv>
 IDsOK s [confID] [uID,uID'] [papID] \<and> pass s uID = p \<and>
 phase s confID = subPH \<and> isAut s confID uID papID \<and> isPC s confID uID'"


subsubsection\<open>Actions available starting from the subPH phase\<close>

(* read a paper's title, abstract and authors: *)
definition readPaperTAA :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow>
    (string * string *  userID list)"
where
"readPaperTAA s confID uID p papID \<equiv>
 case paper s papID of Paper title abstract pc reviews dis decs \<Rightarrow>
   (title, abstract, [uID. uID \<leftarrow> userIDs s , isAut s confID uID papID])"

definition e_readPaperTAA :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_readPaperTAA s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID \<ge> subPH \<and> (isAut s confID uID papID \<or> isPC s confID uID)"

(* read a paper's content: *)
definition readPaperC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> pcontent"
where
"readPaperC s confID uID p papID \<equiv>
 case paper s papID of Paper title abstract pc reviews dis decs \<Rightarrow> pc"

definition e_readPaperC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_readPaperC s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 (
  phase s confID \<ge> subPH \<and> isAut s confID uID papID \<or>
  phase s confID \<ge> bidPH \<and> isPC s confID uID
 )"

(* Note that the difference between the enabledness of readPaperTAA and that of readPaperC is
that the latter is allowed for the PC members only in the bidding phase.  *)

(* list all papers associated to a conference (with which the committee member does not have conflict): *)
definition listPapers :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID list"
where
"listPapers s confID uID p \<equiv>
 let paps = paper s in
 [papID. papID \<leftarrow> paperIDs s confID]"

definition e_listPapers :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listPapers s confID uID p \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 phase s confID \<ge> subPH \<and> isPC s confID uID"

(* list my (authored) papers: *)
definition listMyPapers :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID list"
where
"listMyPapers s confID uID p \<equiv>
 let paps = paper s in
 [papID. papID \<leftarrow> paperIDs s confID, isAut s confID uID papID]"

definition e_listMyPapers :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listMyPapers s confID uID p \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 phase s confID \<ge> subPH"


subsubsection\<open>Actions available in the bidPH phase\<close>

(* update (my) preference: *)
definition updatePref :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> preference \<Rightarrow> state"
where
"updatePref s confID uID p papID pr \<equiv>
 s \<lparr>pref := fun_upd2 (pref s) uID papID pr\<rparr>"

definition e_updatePref :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> preference \<Rightarrow> bool"
where
"e_updatePref s confID uID p papID pr \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID = bidPH \<and> isPC s confID uID \<and>
 \<not> isAut s confID uID papID"
(* note: if an author of the paper, conflict was marked in the first place,
   and updating is not allowed *)


subsubsection\<open>Actions available starting from the bidPH phase\<close>

(* read (my) preference: *)
definition readPref :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> preference"
where
"readPref s confID uID p papID \<equiv>
 pref s uID papID"

definition e_readPref :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_readPref s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID \<ge> bidPH \<and> isPC s confID uID"


subsubsection\<open>Actions available in the revPH phase\<close>

(* read preferences of a committee member (useful for the chair to read the preferences of the
committee members: *)

definition readPrefOfPC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> userID \<Rightarrow> preference"
where
"readPrefOfPC s confID uID p papID uID' \<equiv>
 pref s uID' papID"

definition e_readPrefOfPC :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> userID\<Rightarrow> bool"
where
"e_readPrefOfPC s confID uID p papID uID' \<equiv>
 IDsOK s [confID] [uID,uID'] [papID] \<and> pass s uID = p \<and>
 (phase s confID \<ge> bidPH \<and> isChair s confID uID \<and> isPC s confID uID'
  \<or>
  phase s confID = subPH \<and> isAut s confID uID papID)"
(* unique violation of monotonicity for read actions: an author can read the preferences of the PC chair
  in the submission phase, but not later, as later they will have been updated by the chairs *)

(* create a review and assign a reviewer: *)
definition createReview :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> userID \<Rightarrow> state"
where
"createReview s confID uID p papID uID' \<equiv>
 case paper s papID of Paper title abstract pc reviews dis decs \<Rightarrow>
   let rls = roles s confID uID'; n = length (reviewsPaper (paper s papID));
       reviews' = reviews @ [emptyReview]
   in
   s \<lparr>roles := fun_upd2 (roles s) confID uID' (List.insert (Rev papID n) rls),
      paper := fun_upd (paper s) papID (Paper title abstract pc reviews' dis decs)
     \<rparr>"
(* note: the new review is added at the end, in order not to disrupt the indexing of the other reviews *)

definition e_createReview :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> userID \<Rightarrow> bool"
where
"e_createReview s confID uID p papID uID' \<equiv>
 IDsOK s [confID] [uID,uID'] [papID] \<and> pass s uID = p \<and>
 phase s confID = revPH \<and>
 isChair s confID uID \<and> pref s uID papID \<noteq> Conflict \<and>
 isPC s confID uID' \<and> \<not> isRev s confID uID' papID \<and> pref s uID' papID \<noteq> Conflict"

(* update the review that I write: *)
definition updateReview ::
"state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> nat \<Rightarrow> rcontent \<Rightarrow> state"
where
"updateReview s confID uID p papID n rc \<equiv>
 case paper s papID of Paper title abstract pc reviews dis decs \<Rightarrow>
   let review = [rc]; reviews' = list_update reviews n review
   in
   s \<lparr>paper := fun_upd (paper s) papID (Paper title abstract pc reviews' dis decs)\<rparr>"

definition e_updateReview ::
"state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> nat \<Rightarrow> rcontent \<Rightarrow> bool"
where
"e_updateReview s confID uID p papID n rc \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID = revPH \<and> isRev s confID uID papID \<and>
 getReviewIndex s confID uID papID = n"


subsubsection\<open>Actions available starting from the revPH phase\<close>

(* read the review that I write: *)
definition readMyReview :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> nat * review"
where
"readMyReview s confID uID p papID \<equiv>
 case getRevRole s confID uID papID of
   Some (Rev papID' n) \<Rightarrow> (n, getNthReview s papID n)"

definition e_readMyReview :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_readMyReview s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID \<ge> revPH \<and> isRev s confID uID papID"

(* list my assigned papers: *)
definition listMyAssignedPapers :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID list"
where
"listMyAssignedPapers s confID uID p \<equiv>
 let paps = paper s in
 [papID. papID \<leftarrow> paperIDs s confID, isRev s confID uID papID]"

definition e_listMyAssignedPapers :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listMyAssignedPapers s confID uID p \<equiv>
 IDsOK s [confID] [uID] [] \<and> pass s uID = p \<and>
 phase s confID \<ge> revPH \<and> isPC s confID uID"


definition listAssignedReviewers :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> userID list"
where
"listAssignedReviewers s confID uID p papID \<equiv>
 [uID \<leftarrow> userIDs s. isRev s confID uID papID]"

definition e_listAssignedReviewers :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_listAssignedReviewers s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID \<ge> revPH \<and>
 isChair s confID uID \<and> pref s uID papID \<noteq> Conflict"


subsubsection\<open>Actions available in the disPH phase\<close>

(* undestructively update the discussion with a comment: *)
definition uupdateDis :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> string \<Rightarrow> state"
where
"uupdateDis s confID uID p papID comm \<equiv>
 case paper s papID of Paper title abstract pc reviews (Dis comments) decs \<Rightarrow>
   s \<lparr>paper := fun_upd (paper s) papID (Paper title abstract pc reviews (Dis (comm # comments)) decs)\<rparr>"

definition e_uupdateDis :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> string \<Rightarrow> bool"
where
"e_uupdateDis s confID uID p papID comm \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID = disPH \<and> isPC s confID uID \<and> pref s uID papID \<noteq> Conflict"

(* correct my review during the discussion
(instance of a undestructive update) *)
definition uupdateReview ::
"state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> nat \<Rightarrow> rcontent \<Rightarrow> state"
where
"uupdateReview s confID uID p papID n rc \<equiv>
 case paper s papID of Paper title abstract pc reviews dis decs \<Rightarrow>
   let review = rc # (reviews ! n); reviews' = list_update reviews n review
   in
   s \<lparr>paper := fun_upd (paper s) papID (Paper title abstract pc reviews' dis decs)\<rparr>"

definition e_uupdateReview ::
"state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> nat \<Rightarrow> rcontent \<Rightarrow> bool"
where
"e_uupdateReview s confID uID p papID n rc \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID = disPH \<and> isRev s confID uID papID \<and>
 getReviewIndex s confID uID papID = n"

(* update the decision for a paper (again undestructive update) : *)
definition uupdateDec :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> decision \<Rightarrow> state"
where
"uupdateDec s confID uID p papID dec \<equiv>
 case paper s papID of Paper title abstract pc reviews dis decs \<Rightarrow>
   s \<lparr>paper := fun_upd (paper s) papID (Paper title abstract pc reviews dis (dec # decs))\<rparr>"

definition e_uupdateDec :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> decision \<Rightarrow> bool"
where
"e_uupdateDec s confID uID p papID dec \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID = disPH \<and> isChair s confID uID \<and> pref s uID papID \<noteq> Conflict"


subsubsection\<open>Actions available starting from the disPH phase\<close>

(* read all the reviews to a paper (including all the updates) with the IDs of the reviewers: *)
definition readReviews :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> (userID * review) list"
where
"readReviews s confID uID p papID \<equiv>
 getReviewersReviews s confID papID"

definition e_readReviews :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_readReviews s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID \<ge> disPH \<and> isPC s confID uID \<and> pref s uID papID \<noteq> Conflict"

(* read the decisions (i.e., the decision history) for a paper: *)
definition readDecs :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> decision list"
where
"readDecs s confID uID p papID \<equiv>
 case paper s papID of Paper title abstract pc reviews dis decs \<Rightarrow> decs"

definition e_readDecs :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_readDecs s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID \<ge> disPH \<and> isPC s confID uID \<and> pref s uID papID \<noteq> Conflict"

(* read the discussion to a paper: *)
definition readDis :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> string list"
where
"readDis s confID uID p papID \<equiv>
 case paper s papID of Paper title abstract pc reviews (Dis comments) decs \<Rightarrow> comments"

definition e_readDis :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_readDis s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID \<ge> disPH \<and> isPC s confID uID \<and> pref s uID papID \<noteq> Conflict"



subsubsection\<open>Actions available starting from the notifPH phase\<close>

(* read final reviews to a paper: available to the authors and all non-conflicted PC members *)
definition readFinalReviews :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> review list"
where
"readFinalReviews s confID uID p papID \<equiv>
 map (\<lambda> rev. case rev of [] \<Rightarrow> [(NoExp,NoScore,emptyStr)]
                        |((exp,score,comm) # rv) \<Rightarrow> [(exp,score,comm)])
 (reviewsPaper (paper s papID))"

definition e_readFinalReviews :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_readFinalReviews s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID \<ge> notifPH \<and> (isAut s confID uID papID \<or> (isPC s confID uID \<and> pref s uID papID \<noteq> Conflict))"

(* read the final decision for a paper available to the authors and all PC members (including conflicted PC members):*)
definition readFinalDec :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> decision"
where
"readFinalDec s confID uID p papID \<equiv>
 case paper s papID of Paper title abstract pc reviews dis decs \<Rightarrow>
   case decs of [] \<Rightarrow> NoDecision | dec # decs \<Rightarrow> dec"

definition e_readFinalDec :: "state \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> paperID \<Rightarrow> bool"
where
"e_readFinalDec s confID uID p papID \<equiv>
 IDsOK s [confID] [uID] [papID] \<and> pass s uID = p \<and>
 phase s confID \<ge> notifPH \<and> (isAut s confID uID papID \<or> isPC s confID uID)"


subsection\<open>The step function\<close>

datatype out =
  outOK | outErr | (* OK and error, outputs for list, update and u-update  actions *)
  outBool bool|
  outSTRT "string * string * string" | outSTRL "string list" | outCONF "string * string * role list * phase" |
  outPREF preference |
  outCON pcontent |
  outNREV "nat * review" | outREVL "review list" | outRREVL "(userID * review) list" |
  outDEC "decision" | outDECL "decision list" |
  outCIDL "confID list" |   outUIDL "userID list" | outPIDL "paperID list"|
  outSTRPAL "string * string * userID list"

datatype cAct =
  cUser userID password string string string
 |cConf confID userID password string string
 |cPC confID userID password userID
 |cChair confID userID password userID
 |cPaper confID userID password paperID string string
 |cAuthor confID userID password paperID userID
 |cConflict confID userID password paperID userID
 |cReview confID userID password paperID userID

lemmas c_defs =
e_createUser_def createUser_def
e_createConf_def createConf_def
e_createPC_def createPC_def
e_createChair_def createChair_def
e_createAuthor_def createAuthor_def
e_createConflict_def createConflict_def
e_createPaper_def createPaper_def
e_createReview_def createReview_def

fun cStep :: "state \<Rightarrow> cAct \<Rightarrow> out * state" where
"cStep s (cUser uID p name info email) =
 (if e_createUser s uID p name info email
    then (outOK, createUser s uID p name info email)
    else (outErr, s))"
|
"cStep s (cConf confID uID p name info) =
 (if e_createConf s confID uID p name info
    then (outOK, createConf s confID uID p name info)
    else (outErr, s))"
|
"cStep s (cPC confID uID p uID') =
 (if e_createPC s confID uID p uID'
    then (outOK, createPC s confID uID p uID')
    else (outErr, s))"
|
"cStep s (cChair confID uID p uID') =
 (if e_createChair s confID uID p uID'
    then (outOK, createChair s confID uID p uID')
    else (outErr, s))"
|
"cStep s (cPaper confID uID p papID name info) =
 (if e_createPaper s confID uID p papID name info
    then (outOK, createPaper s confID uID p papID name info)
    else (outErr, s))"
|
"cStep s (cAuthor confID uID p papID uID') =
 (if e_createAuthor s confID uID p papID uID'
    then (outOK, createAuthor s confID uID p papID uID')
    else (outErr, s))"
|
"cStep s (cConflict confID uID p papID uID') =
 (if e_createConflict s confID uID p papID uID'
    then (outOK, createConflict s confID uID p papID uID')
    else (outErr, s))"
|
"cStep s (cReview confID uID p papID uID') =
 (if e_createReview s confID uID p papID uID'
    then (outOK, createReview s confID uID p papID uID')
    else (outErr, s))"


datatype uAct =
  uUser userID password password string string string
 |uConfA confID userID password
 |uPhase confID userID password phase
 |uPaperTA confID userID password paperID string string
 |uPaperC confID userID password paperID pcontent
 |uPref confID userID password paperID preference
 |uReview confID userID password paperID nat rcontent

lemmas u_defs =
e_updateUser_def updateUser_def
e_updateConfA_def updateConfA_def
e_updatePhase_def updatePhase_def
e_updatePaperTA_def updatePaperTA_def
e_updatePaperC_def updatePaperC_def
e_updatePref_def updatePref_def
e_updateReview_def updateReview_def

fun uStep :: "state \<Rightarrow> uAct \<Rightarrow> out * state" where
"uStep s (uUser uID p p' name info email) =
 (if e_updateUser s uID p p' name info email
    then (outOK, updateUser s uID p p' name info email)
    else (outErr, s))"
|
"uStep s (uConfA confID uID p) =
 (if e_updateConfA s confID uID p
    then (outOK, updateConfA s confID uID p)
    else (outErr, s))"
|
"uStep s (uPhase confID uID p ph) =
 (if e_updatePhase s confID uID p ph
    then (outOK, updatePhase s confID uID p ph)
    else (outErr, s))"
|
"uStep s (uPaperTA confID uID p papID name info) =
 (if e_updatePaperTA s confID uID p papID name info
    then (outOK, updatePaperTA s confID uID p papID name info)
    else (outErr, s))"
|
"uStep s (uPaperC confID uID p papID pc) =
 (if e_updatePaperC s confID uID p papID pc
    then (outOK, updatePaperC s confID uID p papID pc)
    else (outErr, s))"
|
"uStep s (uPref confID uID p papID pr) =
 (if e_updatePref s confID uID p papID pr
    then (outOK, updatePref s confID uID p papID pr)
    else (outErr, s))"
|
"uStep s (uReview confID uID p papID n rc) =
 (if e_updateReview s confID uID p papID n rc
    then (outOK, updateReview s confID uID p papID n rc)
    else (outErr, s))"


datatype uuAct =
  uuNews confID userID password string
 |uuDis confID userID password paperID string
 |uuReview confID userID password paperID nat rcontent
 |uuDec confID userID password paperID decision

lemmas uu_defs =
e_uupdateNews_def uupdateNews_def
e_uupdateDis_def uupdateDis_def
e_uupdateReview_def uupdateReview_def
uupdateDec_def e_uupdateDec_def

fun uuStep :: "state \<Rightarrow> uuAct \<Rightarrow> out * state" where
"uuStep s (uuNews confID uID p ev) =
 (if e_uupdateNews s confID uID p ev
    then (outOK, uupdateNews s confID uID p ev)
    else (outErr, s))"
|
"uuStep s (uuDis confID uID p papID comm) =
 (if e_uupdateDis s confID uID p papID comm
    then (outOK, uupdateDis s confID uID p papID comm)
    else (outErr, s))"
|
"uuStep s (uuReview confID uID p papID n rc) =
 (if e_uupdateReview s confID uID p papID n rc
    then (outOK, uupdateReview s confID uID p papID n rc)
    else (outErr, s))"
|
"uuStep s (uuDec confID uID p papID dec) =
 (if e_uupdateDec s confID uID p papID dec
    then (outOK, uupdateDec s confID uID p papID dec)
    else (outErr, s))"

datatype rAct =
  rAmIVoronkov userID password
 |rUser userID password userID
 |rConf confID userID password
 |rNews confID userID password
 |rPaperTAA confID userID password paperID
 |rPaperC confID userID password paperID
 |rPref confID userID password paperID
 |rMyReview confID userID password paperID
 |rReviews confID userID password paperID
 |rDecs confID userID password paperID
 |rDis confID userID password paperID
 |rFinalReviews confID userID password paperID
 |rFinalDec confID userID password paperID
 |rPrefOfPC confID userID password paperID userID

lemmas r_defs =
  readAmIVoronkov_def e_readAmIVoronkov_def
 readUser_def e_readUser_def
 readConf_def e_readConf_def
 readNews_def e_readNews_def
 readPaperTAA_def e_readPaperTAA_def
 readPaperC_def e_readPaperC_def
 readPref_def e_readPref_def
 readMyReview_def e_readMyReview_def
 readReviews_def e_readReviews_def
 readDecs_def e_readDecs_def
 readDis_def e_readDis_def
 readFinalReviews_def e_readFinalReviews_def
 readFinalDec_def e_readFinalDec_def
 readPrefOfPC_def e_readPrefOfPC_def

fun rObs :: "state \<Rightarrow> rAct \<Rightarrow> out" where
"rObs s (rAmIVoronkov uID p) =
 (if e_readAmIVoronkov s uID p then outBool (readAmIVoronkov s uID p) else outErr)"
|
"rObs s (rUser uID p uID') =
 (if e_readUser s uID p uID' then outSTRT (readUser s uID p uID') else outErr)"
|
"rObs s (rConf confID uID p) =
 (if e_readConf s confID uID p then outCONF (readConf s confID uID p) else outErr)"
|
"rObs s (rNews confID uID p) =
 (if e_readNews s confID uID p then outSTRL (readNews s confID uID p) else outErr)"
|
"rObs s (rPaperTAA confID uID p papID) =
 (if e_readPaperTAA s confID uID p papID then outSTRPAL (readPaperTAA s confID uID p papID) else outErr)"
|
"rObs s (rPaperC confID uID p papID) =
 (if e_readPaperC s confID uID p papID then outCON (readPaperC s confID uID p papID) else outErr)"
|
"rObs s (rPref confID uID p papID) =
 (if e_readPref s confID uID p papID then outPREF (readPref s confID uID p papID) else outErr)"
|
"rObs s (rMyReview confID uID p papID) =
 (if e_readMyReview s confID uID p papID then outNREV (readMyReview s confID uID p papID) else outErr)"
|
"rObs s (rReviews confID uID p papID) =
 (if e_readReviews s confID uID p papID then outRREVL (readReviews s confID uID p papID) else outErr)"
|
"rObs s (rDecs confID uID p papID) =
 (if e_readDecs s confID uID p papID then outDECL (readDecs s confID uID p papID) else outErr)"
|
"rObs s (rDis confID uID p papID) =
 (if e_readDis s confID uID p papID then outSTRL (readDis s confID uID p papID) else outErr)"
|
"rObs s (rFinalReviews confID uID p papID) =
 (if e_readFinalReviews s confID uID p papID then outREVL (readFinalReviews s confID uID p papID) else outErr)"
|
"rObs s (rFinalDec confID uID p papID) =
 (if e_readFinalDec s confID uID p papID then outDEC (readFinalDec s confID uID p papID) else outErr)"
|
"rObs s (rPrefOfPC confID uID p papID uID') =
 (if e_readPrefOfPC s confID uID p papID uID' then outPREF (readPrefOfPC s confID uID p papID uID') else outErr)"

datatype lAct =
  lConfs userID password
 |lAConfs userID password
 |lSConfs userID password
 |lMyConfs userID password
 |lAllUsers userID password
 |lAllPapers userID password
 |lPC confID userID password
 |lChair confID userID password
 |lPapers confID userID password
 |lMyPapers confID userID password
 |lMyAssignedPapers confID userID password
 |lAssignedReviewers confID userID password paperID

lemmas l_defs =
 listConfs_def e_listConfs_def
 listAConfs_def e_listAConfs_def
 listSConfs_def e_listSConfs_def
 listMyConfs_def e_listMyConfs_def
 listAllUsers_def e_listAllUsers_def
 listAllPapers_def e_listAllPapers_def
 listPC_def e_listPC_def
 listChair_def e_listChair_def
 listPapers_def e_listPapers_def
 listMyPapers_def e_listMyPapers_def
 listMyAssignedPapers_def e_listMyAssignedPapers_def
 listAssignedReviewers_def e_listAssignedReviewers_def

fun lObs :: "state \<Rightarrow> lAct \<Rightarrow> out" where
"lObs s (lConfs uID p) =
 (if e_listConfs s uID p then outCIDL (listConfs s uID p) else outErr)"
|
"lObs s (lAConfs uID p) =
 (if e_listAConfs s uID p then outCIDL (listAConfs s uID p) else outErr)"
|
"lObs s (lSConfs uID p) =
 (if e_listSConfs s uID p then outCIDL (listSConfs s uID p) else outErr)"
|
"lObs s (lMyConfs uID p) =
 (if e_listMyConfs s uID p then outCIDL (listMyConfs s uID p) else outErr)"
|
"lObs s (lAllUsers uID p) =
 (if e_listAllUsers s uID p then outUIDL (listAllUsers s uID p) else outErr)"
|
"lObs s (lAllPapers uID p) =
 (if e_listAllPapers s uID p then outPIDL (listAllPapers s uID p) else outErr)"
|
"lObs s (lPC confID uID p) =
 (if e_listPC s confID uID p then outUIDL (listPC s confID uID p) else outErr)"
|
"lObs s (lChair confID uID p) =
 (if e_listChair s confID uID p then outUIDL (listChair s confID uID p) else outErr)"
|
"lObs s (lPapers confID uID p) =
 (if e_listPapers s confID uID p then outPIDL (listPapers s confID uID p) else outErr)"
|
"lObs s (lMyPapers confID uID p) =
 (if e_listMyPapers s confID uID p then outPIDL (listMyPapers s confID uID p) else outErr)"
|
"lObs s (lMyAssignedPapers confID uID p) =
 (if e_listMyAssignedPapers s confID uID p then outPIDL (listMyAssignedPapers s confID uID p) else outErr)"
|
"lObs s (lAssignedReviewers confID uID p papID) =
 (if e_listAssignedReviewers s confID uID p papID
   then outUIDL (listAssignedReviewers s confID uID p papID) else outErr)"

datatype act =
(* 3 kinds of effects: creation, update and undestructive update *)
  Cact cAct | Uact uAct | UUact uuAct |
(* 2 kinds of observations: reading and listing (the latter mainly printing IDs) *)
  Ract rAct | Lact lAct

fun step :: "state \<Rightarrow> act \<Rightarrow> out * state" where
"step s (Cact ca) = cStep s ca"
|
"step s (Uact ua) = uStep s ua"
|
"step s (UUact uua) = uuStep s uua"
|
"step s (Ract ra) = (rObs s ra, s)"
|
"step s (Lact la) = (lObs s la, s)"

export_code step istate getFreshPaperID in Scala


text \<open>Some action selectors, used for verification:\<close>

(* The user (subject) of an action: *)
fun cUserOfA :: "cAct \<Rightarrow> userID" where
"cUserOfA (cUser uID p name info email) = uID" (* time when a uID appears is an action of uID itself *)
|
"cUserOfA (cConf confID uID p name info) = uID"
|
"cUserOfA (cPC confID uID p uID') = uID"
|
"cUserOfA (cChair confID uID p uID') = uID"
|
"cUserOfA (cPaper confID uID p papID name info) = uID"
|
"cUserOfA (cAuthor confID uID p papID uID') = uID"
|
"cUserOfA (cConflict confID uID p papID uID') = uID"
|
"cUserOfA (cReview confID uID p papID uID') = uID"

fun uUserOfA :: "uAct \<Rightarrow> userID" where
"uUserOfA (uUser uID p p' name info email) = uID"
|
"uUserOfA (uConfA confID uID p) = uID"
|
"uUserOfA (uPhase confID uID p ph) = uID"
|
"uUserOfA (uPaperTA confID uID p papID name info) = uID"
|
"uUserOfA (uPaperC confID uID p papID pc) = uID"
|
"uUserOfA (uPref confID uID p papID pr) = uID"
|
"uUserOfA (uReview confID uID p papID n rc) = uID"

fun uuUserOfA :: "uuAct \<Rightarrow> userID" where
"uuUserOfA (uuNews confID uID p ev) = uID"
|
"uuUserOfA (uuDis confID uID p papID comm) = uID"
|
"uuUserOfA (uuReview confID uID p papID n rc) = uID"
|
"uuUserOfA (uuDec confID uID p papID dec) = uID"

fun rUserOfA :: "rAct \<Rightarrow> userID" where
"rUserOfA (rAmIVoronkov uID p) = uID"
|
"rUserOfA (rUser uID p uID') = uID"
|
"rUserOfA (rConf confID uID p) = uID"
|
"rUserOfA (rNews confID uID p) = uID"
|
"rUserOfA (rPaperTAA confID uID p papID) = uID"
|
"rUserOfA (rPaperC confID uID p papID) = uID"
|
"rUserOfA (rPref confID uID p papID) = uID"
|
"rUserOfA (rMyReview confID uID p papID) = uID"
|
"rUserOfA (rReviews confID uID p papID) = uID"
|
"rUserOfA (rDecs confID uID p papID) = uID"
|
"rUserOfA (rDis confID uID p papID) = uID"
|
"rUserOfA (rFinalReviews confID uID p papID) = uID"
|
"rUserOfA (rFinalDec confID uID p papID) = uID"
|
"rUserOfA (rPrefOfPC confID uID p papID uID') = uID"

fun lUserOfA :: "lAct \<Rightarrow> userID" where
"lUserOfA (lConfs uID p) = uID"
|
"lUserOfA (lAConfs uID p) = uID"
|
"lUserOfA (lSConfs uID p) = uID"
|
"lUserOfA (lMyConfs uID p) = uID"
|
"lUserOfA (lAllUsers uID p) = uID"
|
"lUserOfA (lAllPapers uID p) = uID"
|
"lUserOfA (lPC confID uID p) = uID"
|
"lUserOfA (lChair confID uID p) = uID"
|
"lUserOfA (lPapers confID uID p) = uID"
|
"lUserOfA (lMyPapers confID uID p) = uID"
|
"lUserOfA (lMyAssignedPapers confID uID p) = uID"
|
"lUserOfA (lAssignedReviewers confID uID p papID) = uID"

fun userOfA :: "act \<Rightarrow> userID" where
"userOfA (Cact ca) = cUserOfA ca"
|
"userOfA (Uact ua) = uUserOfA ua"
|
"userOfA (UUact uua) = uuUserOfA uua"
|
"userOfA (Ract ra) = rUserOfA ra"
|
"userOfA (Lact la) = lUserOfA la"


(* The conference (framework, context) of an action: *)
fun cConfOfA :: "cAct \<Rightarrow> confID option" where
"cConfOfA (cUser uID p name info email) = None"
|
"cConfOfA (cConf confID uID p name info) = Some confID"
(* time when a confID appears is an action bearing its ID *)
|
"cConfOfA (cPC confID uID p uID') = Some confID"
|
"cConfOfA (cChair confID uID p uID') = Some confID"
|
"cConfOfA (cPaper confID uID p papID name info) = Some confID"
|
"cConfOfA (cAuthor confID uID p papID uID') = Some confID"
|
"cConfOfA (cConflict confID uID p papID uID') = Some confID"
|
"cConfOfA (cReview confID uID p papID uID') = Some confID"

fun uConfOfA :: "uAct \<Rightarrow> confID option" where
"uConfOfA (uUser uID p p' name info email) = None"
|
"uConfOfA (uConfA confID uID p) = Some confID"
|
"uConfOfA (uPhase confID uID p ph) = Some confID"
|
"uConfOfA (uPaperTA confID uID p papID name info) = Some confID"
|
"uConfOfA (uPaperC confID uID p papID pc) = Some confID"
|
"uConfOfA (uPref confID uID p papID pr) = Some confID"
|
"uConfOfA (uReview confID uID p papID n rc) = Some confID"

fun uuConfOfA :: "uuAct \<Rightarrow> confID option" where
"uuConfOfA (uuNews confID uID p ev) = Some confID"
|
"uuConfOfA (uuDis confID uID p papID comm) = Some confID"
|
"uuConfOfA (uuReview confID uID p papID n rc) = Some confID"
|
"uuConfOfA (uuDec confID uID p papID dec) = Some confID"

fun rConfOfA :: "rAct \<Rightarrow> confID option" where
"rConfOfA (rAmIVoronkov uID p) = None"
|
"rConfOfA (rUser uID p uID') = None"
|
"rConfOfA (rConf confID uID p) = Some confID"
|
"rConfOfA (rNews confID uID p) = Some confID"
|
"rConfOfA (rPaperTAA confID uID p papID) = Some confID"
|
"rConfOfA (rPaperC confID uID p papID) = Some confID"
|
"rConfOfA (rPref confID uID p papID) = Some confID"
|
"rConfOfA (rMyReview confID uID p papID) = Some confID"
|
"rConfOfA (rReviews confID uID p papID) = Some confID"
|
"rConfOfA (rDecs confID uID p papID) = Some confID"
|
"rConfOfA (rDis confID uID p papID) = Some confID"
|
"rConfOfA (rFinalReviews confID uID p papID) = Some confID"
|
"rConfOfA (rFinalDec confID uID p papID) = Some confID"
|
"rConfOfA (rPrefOfPC confID uID p papID uID') = Some confID"


fun lConfOfA :: "lAct \<Rightarrow> confID option" where
"lConfOfA (lConfs uID p) = None"
|
"lConfOfA (lAConfs uID p) = None"
|
"lConfOfA (lSConfs uID p) = None"
|
"lConfOfA (lMyConfs uID p) = None"
|
"lConfOfA (lAllUsers uID p) = None"
|
"lConfOfA (lAllPapers uID p) = None"
|
"lConfOfA (lPC confID uID p) = Some confID"
|
"lConfOfA (lChair confID uID p) = Some confID"
|
"lConfOfA (lPapers confID uID p) = Some confID"
|
"lConfOfA (lMyPapers confID uID p) = Some confID"
|
"lConfOfA (lMyAssignedPapers confID uID p) = Some confID"
|
"lConfOfA (lAssignedReviewers confID uID p papID) = Some confID"

fun confOfA :: "act \<Rightarrow> confID option" where
"confOfA (Cact ca) = cConfOfA ca"
|
"confOfA (Uact ua) = uConfOfA ua"
|
"confOfA (UUact uua) = uuConfOfA uua"
|
"confOfA (Ract ra) = rConfOfA ra"
|
"confOfA (Lact la) = lConfOfA la"


(* The paper of an action: *)
fun cPaperOfA :: "cAct \<Rightarrow> paperID option" where
"cPaperOfA (cUser uID p name info email) = None"
|
"cPaperOfA (cPaper confID uID p papID name info) = Some papID"
(* time when a paperID appears is an action bearing its ID *)
|
"cPaperOfA (cPC confID uID p uID') = None"
|
"cPaperOfA (cChair confID uID p uID') = None"
|
"cPaperOfA (cConf confID uID p name info) = None"
|
"cPaperOfA (cAuthor confID uID p papID uID') = Some papID"
|
"cPaperOfA (cConflict confID uID p papID uID') = Some papID"
|
"cPaperOfA (cReview confID uID p papID uID') = Some papID"

fun uPaperOfA :: "uAct \<Rightarrow> paperID option" where
"uPaperOfA (uUser uID p p' name info email) = None"
|
"uPaperOfA (uConfA confID uID p) = None"
|
"uPaperOfA (uPhase confID uID p ph) = None"
|
"uPaperOfA (uPaperTA confID uID p papID name info) = Some papID"
|
"uPaperOfA (uPaperC confID uID p papID pc) = Some papID"
|
"uPaperOfA (uPref confID uID p papID pr) = Some papID"
|
"uPaperOfA (uReview confID uID p papID n rc) = Some papID"

fun uuPaperOfA :: "uuAct \<Rightarrow> paperID option" where
"uuPaperOfA (uuNews confID uID p ev) = None"
|
"uuPaperOfA (uuDis confID uID p papID comm) = Some papID"
|
"uuPaperOfA (uuReview confID uID p papID n rc) = Some papID"
|
"uuPaperOfA (uuDec confID uID p papID dec) = Some papID"

fun rPaperOfA :: "rAct \<Rightarrow> paperID option" where
"rPaperOfA (rAmIVoronkov uID p) = None"
|
"rPaperOfA (rUser uID p uID') = None"
|
"rPaperOfA (rConf confID uID p) = None"
|
"rPaperOfA (rNews confID uID p) = None"
|
"rPaperOfA (rPaperTAA confID uID p papID) = Some papID"
|
"rPaperOfA (rPaperC confID uID p papID) = Some papID"
|
"rPaperOfA (rPref confID uID p papID) = Some papID"
|
"rPaperOfA (rMyReview confID uID p papID) = Some papID"
|
"rPaperOfA (rReviews confID uID p papID) = Some papID"
|
"rPaperOfA (rDecs confID uID p papID) = Some papID"
|
"rPaperOfA (rDis confID uID p papID) = Some papID"
|
"rPaperOfA (rFinalReviews confID uID p papID) = Some papID"
|
"rPaperOfA (rFinalDec confID uID p papID) = Some papID"
|
"rPaperOfA (rPrefOfPC confID uID p papID uID') = Some papID"

fun lPaperOfA :: "lAct \<Rightarrow> paperID option" where
"lPaperOfA (lConfs uID p) = None"
|
"lPaperOfA (lAConfs uID p) = None"
|
"lPaperOfA (lSConfs uID p) = None"
|
"lPaperOfA (lMyConfs uID p) = None"
|
"lPaperOfA (lAllUsers uID p) = None"
|
"lPaperOfA (lAllPapers uID p) = None"
|
"lPaperOfA (lPC confID uID p) = None"
|
"lPaperOfA (lChair confID uID p) = None"
|
"lPaperOfA (lPapers confID uID p) = None"
|
"lPaperOfA (lMyPapers confID uID p) = None"
|
"lPaperOfA (lMyAssignedPapers confID uID p) = None"
|
"lPaperOfA (lAssignedReviewers confID uID p papID) = Some papID"

fun paperOfA :: "act \<Rightarrow> paperID option" where
"paperOfA (Cact ca) = cPaperOfA ca"
|
"paperOfA (Uact ua) = uPaperOfA ua"
|
"paperOfA (UUact uua) = uuPaperOfA uua"
|
"paperOfA (Ract ra) = rPaperOfA ra"
|
"paperOfA (Lact la) = lPaperOfA la"

(* Note: unlike confOfA and paperOfA which may be "None", userOfA always returns a user ID.  *)



end
