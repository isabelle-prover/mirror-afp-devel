section \<open>System specification\<close>

theory System_Specification
imports Prelim
begin

(* This is the system specification of COSMED.
*)

declare List.insert[simp]

subsection \<open>The state\<close>

record state =
  admin :: userID
  (*  *)
  pendingUReqs :: "userID list"
  userReq :: "userID \<Rightarrow> req"
  userIDs :: "userID list"
  user :: "userID \<Rightarrow> user"
  pass :: "userID \<Rightarrow> password"
  (*  *)
  pendingFReqs :: "userID \<Rightarrow> userID list"
  friendReq :: "userID \<Rightarrow> userID \<Rightarrow> req"
  friendIDs :: "userID \<Rightarrow> userID list"
  (*  *)
  postIDs :: "postID list"
  post :: "postID \<Rightarrow> post"
  owner :: "postID \<Rightarrow> userID"
  vis :: "postID \<Rightarrow> vis"

definition IDsOK :: "state \<Rightarrow> userID list \<Rightarrow> postID list \<Rightarrow> bool"
where
"IDsOK s uIDs pIDs \<equiv>
 list_all (\<lambda> uID. uID \<in>\<in> userIDs s) uIDs \<and>
 list_all (\<lambda> pID. pID \<in>\<in> postIDs s) pIDs"


subsection \<open>The actions\<close>

subsubsection\<open>Initialization of the system\<close>

definition istate :: state
where
"istate \<equiv>
 \<lparr>
  admin = emptyUserID,

  pendingUReqs = [],
  userReq = (\<lambda> uID. emptyReq),
  userIDs = [],
  user = (\<lambda> uID. emptyUser),
  pass = (\<lambda> uID. emptyPass),

  pendingFReqs = (\<lambda> uID. []),
  friendReq = (\<lambda> uID uID'. emptyReq),
  friendIDs = (\<lambda> uID. []),

  postIDs = [],
  post = (\<lambda> papID. emptyPost),
  owner = (\<lambda> pID. emptyUserID),
  vis = (\<lambda> pID. FriendV)
 \<rparr>"


subsubsection\<open>Starting action\<close>

(* This initiates the system. It has the following parameters:
  -- uID, p, name: the admin user id, name and password
*)
definition startSys ::
"state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> state"
where
"startSys s uID p \<equiv>
 s \<lparr>admin := uID,
    userIDs := [uID],
    user := (user s) (uID := emptyUser),
    pass := (pass s) (uID := p)\<rparr>"

definition e_startSys :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow>  bool"
where
"e_startSys s uID p \<equiv> userIDs s = []"


subsubsection\<open>Creation actions\<close>


(* Create new user request: we allow users to choose their own IDs; they could be their email addresses. *)
definition createNUReq :: "state \<Rightarrow> userID \<Rightarrow> req \<Rightarrow> state"
where
"createNUReq s uID reqInfo \<equiv>
 s \<lparr>pendingUReqs := pendingUReqs s @ [uID],
    userReq := (userReq s)(uID := reqInfo)
\<rparr>"

definition e_createNUReq :: "state \<Rightarrow> userID \<Rightarrow> req \<Rightarrow> bool"
where
"e_createNUReq s uID req \<equiv>
 admin s \<in>\<in> userIDs s \<and> \<not> uID \<in>\<in> userIDs s \<and> \<not> uID \<in>\<in> pendingUReqs s"
(* a new-user request can be created only if the system has started, i.e., if an admin exists *)

(* The admin actually creates a user by approving a pending new-user request.
E.g., the admin can add an  arbitrary password and send it by email to that user.
Then the user can change his password. *)
definition createUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> state"
where
"createUser s uID p uID' p' \<equiv>
 s \<lparr>userIDs := uID' # (userIDs s),
    user := (user s) (uID' := emptyUser),
    pass := (pass s) (uID' := p'),
    pendingUReqs := remove1 uID' (pendingUReqs s),
    userReq := (userReq s)(uID := emptyReq)\<rparr>"

definition e_createUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_createUser s uID p uID' p' \<equiv>
 IDsOK s [uID] [] \<and> pass s uID = p \<and> uID = admin s \<and> uID' \<in>\<in> pendingUReqs s"


(* Create post: note that post ID is an action parameter, and that the enabledness action
checks that it is fresh.
The web interface will actually generate it, using getFresh. *)
definition createPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> title \<Rightarrow> state"
where
"createPost s uID p pID title \<equiv>
 s \<lparr>postIDs := pID # postIDs s,
    post := (post s) (pID := Ntc title emptyText emptyImg),
    owner := (owner s) (pID := uID)\<rparr>"
(* Recall from the initial state that the initial visibility is FriendV *)

definition e_createPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> title \<Rightarrow> bool"
where
"e_createPost s uID p pID title \<equiv>
 IDsOK s [uID] [] \<and> pass s uID = p \<and>
 \<not> pID \<in>\<in> postIDs s"

(* Friendship: *)
(* Create friend request, namely uID Reqs friendship of uID': *)
definition createFriendReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> req \<Rightarrow> state"
where
"createFriendReq s uID p uID' req \<equiv>
 let pfr = pendingFReqs s in
 s \<lparr>pendingFReqs := pfr (uID' := pfr uID' @ [uID]),
    friendReq := fun_upd2 (friendReq s) uID uID' req\<rparr>"

definition e_createFriendReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> req \<Rightarrow> bool"
where
"e_createFriendReq s uID p uID' req \<equiv>
 IDsOK s [uID,uID'] [] \<and> pass s uID = p \<and>
 \<not> uID \<in>\<in> pendingFReqs s uID' \<and> \<not> uID \<in>\<in> friendIDs s uID'"

(* Create friend, by approving a friend request (namely uID approves the request from uID').
Friendship is symmetric, hence the two updates to "friend";
also, the friendship request is canceled upon approval.  *)
definition createFriend :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> state"
where
"createFriend s uID p uID' \<equiv>
 let fr = friendIDs s; pfr = pendingFReqs s in
 s \<lparr>friendIDs := fr (uID := fr uID @ [uID'], uID' := fr uID' @ [uID]),
    pendingFReqs := pfr (uID := remove1 uID' (pfr uID), uID' := remove1 uID (pfr uID')),
    friendReq := fun_upd2 (fun_upd2 (friendReq s) uID' uID emptyReq) uID uID' emptyReq\<rparr>"

definition e_createFriend :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_createFriend s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] \<and> pass s uID = p \<and>
 uID' \<in>\<in> pendingFReqs s uID"


subsubsection\<open>Updating actions\<close>

(* Users can update their passwords and names: *)
definition updateUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> password \<Rightarrow> name \<Rightarrow> inform \<Rightarrow> state"
where
"updateUser s uID p p' name info \<equiv>
 s \<lparr>user := (user s) (uID := Usr name info),
    pass := (pass s) (uID := p')\<rparr>"

definition e_updateUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> password \<Rightarrow> name \<Rightarrow> inform \<Rightarrow> bool"
where
"e_updateUser s uID p p' name info \<equiv>
 IDsOK s [uID] [] \<and> pass s uID = p"


(* Updates of the post components: *)
definition updatePost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> post \<Rightarrow> state"
where
"updatePost s uID p pID pst \<equiv>
 s \<lparr>post := (post s) (pID := pst)\<rparr>"

definition e_updatePost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> post \<Rightarrow> bool"
where
"e_updatePost s uID p pID pst \<equiv>
 IDsOK s [uID] [pID] \<and> pass s uID = p \<and>
 owner s pID = uID"

definition updateVisPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> vis \<Rightarrow> state"
where
"updateVisPost s uID p pID vs \<equiv>
 s \<lparr>vis := (vis s) (pID := vs)\<rparr>"

definition e_updateVisPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> vis \<Rightarrow> bool"
where
"e_updateVisPost s uID p pID vs \<equiv>
 IDsOK s [uID] [pID] \<and> pass s uID = p \<and>
 owner s pID = uID \<and> vs \<in> {FriendV, PublicV}"



subsubsection\<open>Deletion (removal) actions\<close>

(* Delete friend:   *)
definition deleteFriend :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> state"
where
"deleteFriend s uID p uID' \<equiv>
 let fr = friendIDs s in
 s \<lparr>friendIDs := fr (uID := removeAll uID' (fr uID), uID' := removeAll uID (fr uID'))\<rparr>"

definition e_deleteFriend :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_deleteFriend s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] \<and> pass s uID = p \<and>
 uID' \<in>\<in> friendIDs s uID"


subsubsection\<open>Reading actions\<close>

(* Read new user request: *)
definition readNUReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> req"
where
"readNUReq s uID p uID' \<equiv> userReq s uID'"

definition e_readNUReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_readNUReq s uID p uID' \<equiv>
 IDsOK s [uID] [] \<and> pass s uID = p \<and>
 uID = admin s \<and> uID' \<in>\<in> pendingUReqs s"

(* A user can read their name and info (and so can all the other users), but not the password: *)
definition readUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> name \<times> inform"
where
"readUser s uID p uID' \<equiv> niUser (user s uID')"

definition e_readUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_readUser s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] \<and> pass s uID = p"

(* A user can check if he is the admin: *)
definition readAmIAdmin :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"readAmIAdmin s uID p \<equiv> uID = admin s"

definition e_readAmIAdmin :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_readAmIAdmin s uID p \<equiv>
 IDsOK s [uID] [] \<and> pass s uID = p"

(* Reading posts: *)
definition readPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> post"
where
"readPost s uID p pID \<equiv> post s pID"

definition e_readPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> bool"
where
"e_readPost s uID p pID \<equiv>
 let post = post s pID in
 IDsOK s [uID] [pID] \<and> pass s uID = p \<and>
 (owner s pID = uID \<or> uID \<in>\<in> friendIDs s (owner s pID) \<or> vis s pID = PublicV)"

definition readVisPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> vis"
where
"readVisPost s uID p pID \<equiv> vis s pID"

definition e_readVisPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> bool"
where
"e_readVisPost s uID p pID \<equiv>
 let post = post s pID in
 IDsOK s [uID] [pID] \<and> pass s uID = p \<and>
 (owner s pID = uID \<or> uID \<in>\<in> friendIDs s (owner s pID) \<or> vis s pID = PublicV)"

definition readOwnerPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> userID"
where
"readOwnerPost s uID p pID \<equiv> owner s pID"

definition e_readOwnerPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> bool"
where
"e_readOwnerPost s uID p pID \<equiv>
 let post = post s pID in
 IDsOK s [uID] [pID] \<and> pass s uID = p \<and>
 (owner s pID = uID \<or> uID \<in>\<in> friendIDs s (owner s pID) \<or> vis s pID = PublicV)"


(* Friendship: *)
(* Read friendship request to me: *)
definition readFriendReqToMe :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> req"
where
"readFriendReqToMe s uID p uID' \<equiv> friendReq s uID' uID"

definition e_readFriendReqToMe :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_readFriendReqToMe s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] \<and> pass s uID = p \<and>
 uID' \<in>\<in> pendingFReqs s uID"

(* Read friendship request from me: *)
definition readFriendReqFromMe :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> req"
where
"readFriendReqFromMe s uID p uID' \<equiv> friendReq s uID uID'"

definition e_readFriendReqFromMe :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_readFriendReqFromMe s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] \<and> pass s uID = p \<and>
 uID \<in>\<in> pendingFReqs s uID'"


subsubsection\<open>Listing actions\<close>

(* list pending new user requests: *)
definition listPendingUReqs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID list"
where
"listPendingUReqs s uID p \<equiv> pendingUReqs s"

definition e_listPendingUReqs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listPendingUReqs s uID p \<equiv>
 IDsOK s [uID] [] \<and> pass s uID = p \<and> uID = admin s"

(* list all users of the system: *)
definition listAllUsers :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID list"
where
"listAllUsers s uID p \<equiv> userIDs s"

definition e_listAllUsers :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listAllUsers s uID p \<equiv> IDsOK s [uID] [] \<and> pass s uID = p"


(* List a user's friends: *)
definition listFriends :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> userID list"
where
"listFriends s uID p uID' \<equiv> friendIDs s uID'"

definition e_listFriends :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_listFriends s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] \<and> pass s uID = p \<and>
 (uID = uID' \<or> uID \<in>\<in> friendIDs s uID')"

(* list posts:: *)
definition listPosts :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> (userID \<times> postID) list"
where
"listPosts s uID p \<equiv>
  [(owner s pID, pID).
    pID \<leftarrow> postIDs s,
    vis s pID = PublicV \<or> uID \<in>\<in> friendIDs s (owner s pID) \<or> uID = owner s pID
  ]"

definition e_listPosts :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listPosts s uID p \<equiv> IDsOK s [uID] [] \<and> pass s uID = p"



subsection\<open>The step function\<close>

datatype out =
  (* Outputs for creation and update actions, as well as for other actions with errors: *)
  outOK | outErr |
  (* Outputs for reading actions: *)
  outBool bool| outNI "name \<times> inform" | outPost post |
  outImg img | outVis vis | outReq req |
  (* Outputs for listing actions: *)
  outUID "userID" | outUIDL "userID list" |
  outUIDNIDL "(userID \<times> postID)list"
  (* outNone (* Used later for global actions *) *)


(* Start actions (only one, but wrapped for uniformity): *)
datatype sActt =
  sSys userID password

lemmas s_defs =
e_startSys_def startSys_def

fun sStep :: "state \<Rightarrow> sActt \<Rightarrow> out * state" where
"sStep s (sSys uID p) =
 (if e_startSys s uID p
    then (outOK, startSys s uID p)
    else (outErr, s))"

fun sUserOfA :: "sActt \<Rightarrow> userID" where
 "sUserOfA (sSys uID p) = uID"

(* Creation actions: *)
datatype cActt =
  cNUReq userID req
 |cUser userID password userID password
 |cFriendReq userID password userID req
 |cFriend userID password userID
 |cPost userID password postID title

lemmas c_defs =
e_createNUReq_def createNUReq_def
e_createUser_def createUser_def
e_createFriendReq_def createFriendReq_def
e_createFriend_def createFriend_def
e_createPost_def createPost_def

fun cStep :: "state \<Rightarrow> cActt \<Rightarrow> out * state" where
"cStep s (cNUReq uID req) =
 (if e_createNUReq s uID req
    then (outOK, createNUReq s uID req)
    else (outErr, s))"
|
"cStep s (cUser uID p uID' p') =
 (if e_createUser s uID p uID' p'
    then (outOK, createUser s uID p uID' p')
    else (outErr, s))"
|
"cStep s (cFriendReq uID p uID' req) =
 (if e_createFriendReq s uID p uID' req
    then (outOK, createFriendReq s uID p uID' req)
    else (outErr, s))"
|
"cStep s (cFriend uID p uID') =
 (if e_createFriend s uID p uID'
    then (outOK, createFriend s uID p uID')
    else (outErr, s))"
|
"cStep s (cPost uID p pID title) =
 (if e_createPost s uID p pID title
    then (outOK, createPost s uID p pID title)
    else (outErr, s))"

fun cUserOfA :: "cActt \<Rightarrow> userID option" where
 "cUserOfA (cNUReq uID req) = Some uID"
|"cUserOfA (cUser uID p uID' p') = Some uID"
|"cUserOfA (cFriendReq uID p uID' req) = Some uID"
|"cUserOfA (cFriend uID p uID') = Some uID"
|"cUserOfA (cPost uID p pID title) = Some uID"



(* Deletion (removal) actions -- currently only friends can be deleted *)

datatype dActt =
  dFriend userID password userID

lemmas d_defs =
e_deleteFriend_def deleteFriend_def

fun dStep :: "state \<Rightarrow> dActt \<Rightarrow> out * state" where
"dStep s (dFriend uID p uID') =
 (if e_deleteFriend s uID p uID'
    then (outOK, deleteFriend s uID p uID')
    else (outErr, s))"

fun dUserOfA :: "dActt \<Rightarrow> userID" where
 "dUserOfA (dFriend uID p uID') = uID"

(* Update actions: *)
datatype uActt =
  uUser userID password password name inform
 |uPost userID password postID post
 |uVisPost userID password postID vis

lemmas u_defs =
e_updateUser_def updateUser_def
e_updatePost_def updatePost_def
e_updateVisPost_def updateVisPost_def

fun uStep :: "state \<Rightarrow> uActt \<Rightarrow> out * state" where
"uStep s (uUser uID p p' name info) =
 (if e_updateUser s uID p p' name info
    then (outOK, updateUser s uID p p' name info)
    else (outErr, s))"
|
"uStep s (uPost uID p pID pst) =
 (if e_updatePost s uID p pID pst
    then (outOK, updatePost s uID p pID pst)
    else (outErr, s))"
|
"uStep s (uVisPost uID p pID visStr) =
 (if e_updateVisPost s uID p pID visStr
    then (outOK, updateVisPost s uID p pID visStr)
    else (outErr, s))"

fun uUserOfA :: "uActt \<Rightarrow> userID" where
 "uUserOfA (uUser uID p p' name info) = uID"
|"uUserOfA (uPost uID p pID pst) = uID"
|"uUserOfA (uVisPost uID p pID visStr) = uID"


(* Read actions: *)
datatype rActt =
  rNUReq userID password userID
 |rUser userID password userID
 |rAmIAdmin userID password
 |rPost userID password postID
 |rVisPost userID password postID
 |rOwnerPost userID password postID
 |rFriendReqToMe userID password userID
 |rFriendReqFromMe userID password userID

lemmas r_defs =
 readNUReq_def e_readNUReq_def
 readUser_def e_readUser_def
 readAmIAdmin_def e_readAmIAdmin_def
 readPost_def e_readPost_def
 readVisPost_def e_readVisPost_def
 readOwnerPost_def e_readOwnerPost_def
 readFriendReqToMe_def e_readFriendReqToMe_def
 readFriendReqFromMe_def e_readFriendReqFromMe_def

fun rObs :: "state \<Rightarrow> rActt \<Rightarrow> out" where
"rObs s (rNUReq uID p uID') =
 (if e_readNUReq s uID p uID' then outReq (readNUReq s uID p uID') else outErr)"
|
"rObs s (rUser uID p uID') =
 (if e_readUser s uID p uID' then outNI (readUser s uID p uID') else outErr)"
|
"rObs s (rAmIAdmin uID p) =
 (if e_readAmIAdmin s uID p then outBool (readAmIAdmin s uID p) else outErr)"
|
"rObs s (rPost uID p pID) =
 (if e_readPost s uID p pID then outPost (readPost s uID p pID) else outErr)"
|
"rObs s (rVisPost uID p pID) =
 (if e_readVisPost s uID p pID then outVis (readVisPost s uID p pID) else outErr)"
|
"rObs s (rOwnerPost uID p pID) =
 (if e_readOwnerPost s uID p pID then outUID (readOwnerPost s uID p pID) else outErr)"
|
"rObs s (rFriendReqToMe uID p uID') =
 (if e_readFriendReqToMe s uID p uID' then outReq (readFriendReqToMe s uID p uID') else outErr)"
|
"rObs s (rFriendReqFromMe uID p uID') =
 (if e_readFriendReqFromMe s uID p uID' then outReq (readFriendReqFromMe s uID p uID') else outErr)"


fun rUserOfA :: "rActt \<Rightarrow> userID option" where
 "rUserOfA (rNUReq uID p uID') = Some uID"
|"rUserOfA (rUser uID p uID') = Some uID"
|"rUserOfA (rAmIAdmin uID p) = Some uID"
|"rUserOfA (rPost uID p pID) = Some uID"
|"rUserOfA (rVisPost uID p pID) = Some uID"
|"rUserOfA (rOwnerPost uID p pID) = Some uID"
|"rUserOfA (rFriendReqToMe uID p uID') = Some uID"
|"rUserOfA (rFriendReqFromMe uID p uID') = Some uID"


(* Listing actions *)
datatype lActt =
  lPendingUReqs userID password
 |lAllUsers userID password
 |lFriends userID password userID
 |lPosts userID password


lemmas l_defs =
 listPendingUReqs_def e_listPendingUReqs_def
 listAllUsers_def e_listAllUsers_def
 listFriends_def e_listFriends_def
 listPosts_def e_listPosts_def


fun lObs :: "state \<Rightarrow> lActt \<Rightarrow> out" where
"lObs s (lPendingUReqs uID p) =
 (if e_listPendingUReqs s uID p then outUIDL (listPendingUReqs s uID p) else outErr)"
|
"lObs s (lAllUsers uID p) =
 (if e_listAllUsers s uID p then outUIDL (listAllUsers s uID p) else outErr)"
|
"lObs s (lFriends uID p uID') =
 (if e_listFriends s uID p uID' then outUIDL (listFriends s uID p uID') else outErr)"
|
"lObs s (lPosts uID p) =
 (if e_listPosts s uID p then outUIDNIDL (listPosts s uID p) else outErr)"


fun lUserOfA :: "lActt \<Rightarrow> userID option" where
 "lUserOfA (lPendingUReqs uID p) = Some uID"
|"lUserOfA (lAllUsers uID p) = Some uID"
|"lUserOfA (lFriends uID p uID') = Some uID"
|"lUserOfA (lPosts uID p) = Some uID"



(* All actions: *)
datatype act =
  Sact sActt |
(* 3 kinds of effects: creation, deletion and update *)
  Cact cActt | Dact dActt | Uact uActt |
(* 2 kinds of observations: reading and listing (the latter mainly printing IDs) *)
  Ract rActt | Lact lActt


fun step :: "state \<Rightarrow> act \<Rightarrow> out * state" where
"step s (Sact sa) = sStep s sa"
|
"step s (Cact ca) = cStep s ca"
|
"step s (Dact da) = dStep s da"
|
"step s (Uact ua) = uStep s ua"
|
"step s (Ract ra) = (rObs s ra, s)"
|
"step s (Lact la) = (lObs s la, s)"

fun userOfA :: "act \<Rightarrow> userID option" where
"userOfA (Sact sa) = Some (sUserOfA sa)"
|
"userOfA (Cact ca) = cUserOfA ca"
|
"userOfA (Dact da) = Some (dUserOfA da)"
|
"userOfA (Uact ua) = Some (uUserOfA ua)"
|
"userOfA (Ract ra) = rUserOfA ra"
|
"userOfA (Lact la) = lUserOfA la"



subsection \<open>Code generation\<close>

export_code step istate getFreshPostID in Scala


end
