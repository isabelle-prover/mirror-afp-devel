section \<open>The CoSMeDis single node specification\<close>

text \<open>This is the specification of a CoSMeDis node, as described
in Sections II and IV.B of \<^cite>\<open>"cosmedis-SandP2017"\<close>.
NB: What that paper refers to as "nodes" are referred in this formalization
as "APIs".

A CoSMeDis node extends CoSMed \<^cite>\<open>"cosmed-itp2016" and "cosmed-jar2018" and "cosmed-AFP"\<close>
with inter-node communication actions.
\<close>

theory System_Specification
  imports
    Prelim
    "Bounded_Deducibility_Security.IO_Automaton"
begin

text \<open>An aspect not handled in this specification is the uniqueness of the node IDs. These
are assumed to be handled externally as follows: a node ID is an URI, and therefore is unique.\<close>

declare List.insert[simp]

subsection \<open>The state\<close>

record state =
  admin :: userID
  (*  *)
  pendingUReqs :: "userID list"
  userReq :: "userID \<Rightarrow> requestInfo"
  userIDs :: "userID list"
  user :: "userID \<Rightarrow> user"
  pass :: "userID \<Rightarrow> password"
  (*  *)
  pendingFReqs :: "userID \<Rightarrow> userID list"
  friendReq :: "userID \<Rightarrow> userID \<Rightarrow> requestInfo"
  friendIDs :: "userID \<Rightarrow> userID list"
  (* Outer friendship, i.e., friendship with users of other (server) APIs. This will effectively
     mean access to the friend-only outer posts retrieved from that server.
     There are two lists:
      - friendship authorizations sent by users of this API, and
      - friendship authorizations received from other APIs. *)
  sentOuterFriendIDs :: "userID \<Rightarrow> (apiID \<times> userID) list"
  recvOuterFriendIDs :: "userID \<Rightarrow> (apiID \<times> userID) list"
  (*  *)
  postIDs :: "postID list"
  post :: "postID \<Rightarrow> post"
  owner :: "postID \<Rightarrow> userID"
  vis :: "postID \<Rightarrow> vis"
  (* The server-api IDs represents the apis whose posts can be read by this api. *)
  (* The following setting ensures that clashes on post IDs from different apis are harmless: *)
  (* Pending request sent by this API to other APIs with the wish that they become servers (and the current API
       becomes their client); this has to be approved by the respective APIs *)
  pendingSApiReqs :: "apiID list"
  sApiReq :: "apiID \<Rightarrow> requestInfo"
  serverApiIDs :: "apiID list"
  (* Password (key) to be used (by both parties) for communication with each server API. *)
  serverPass :: "apiID \<Rightarrow> password"
  outerPostIDs :: "apiID \<Rightarrow> postID list"
  outerPost :: "apiID \<Rightarrow> postID \<Rightarrow> post"
  outerOwner :: "apiID \<Rightarrow> postID \<Rightarrow> userID"
  outerVis :: "apiID \<Rightarrow> postID \<Rightarrow> vis"
  (*  *)
  (* The client-api IDs represents the apis that can read this api's posts *)
  (* Pending requests from APIs that want to become clients; this has to be approved by the admin *)
  pendingCApiReqs :: "apiID list"
  cApiReq :: "apiID \<Rightarrow> requestInfo"
  clientApiIDs :: "apiID list"
  (* Password (key) to be used (by both parties) for communication with each client API. *)
  clientPass :: "apiID \<Rightarrow> password"
  sharedWith :: "postID \<Rightarrow> (apiID \<times> bool) list"
  (* for a post, stores the client apis with which the post was shared together with a boolean flag
     indicating whether the version the api has is up-to-date *)

(* The api IDs will be the URLs of the corresponding APIs *)
(* Note that only the client APIs need a password -- the server API are themselves contacted by this API. *)

(* Note that IDsOK refers only to the registered users, posts, server APIs and their served outerPosts,
and client apis. It does not refer to user IDs or api IDs contained in any pending requests.
*)
definition IDsOK :: "state \<Rightarrow> userID list \<Rightarrow> postID list \<Rightarrow> (apiID \<times> postID list) list \<Rightarrow> apiID list \<Rightarrow> bool"
where
"IDsOK s uIDs pIDs saID_pIDs_s caIDs \<equiv>
 list_all (\<lambda> uID. uID \<in>\<in> userIDs s) uIDs \<and>
 list_all (\<lambda> pID. pID \<in>\<in> postIDs s) pIDs \<and>
 list_all (\<lambda> (aID,pIDs). aID \<in>\<in> serverApiIDs s \<and>
 list_all (\<lambda> pID. pID \<in>\<in> outerPostIDs s aID) pIDs) saID_pIDs_s \<and>
 list_all (\<lambda> aID. aID \<in>\<in> clientApiIDs s) caIDs"


subsection \<open>The actions\<close>

subsubsection \<open>Initialization of the system\<close>


definition istate :: state
where
"istate \<equiv>
 \<lparr>
  admin = emptyUserID,

  pendingUReqs = [],
  userReq = (\<lambda> uID. emptyRequestInfo),
  userIDs = [],
  user = (\<lambda> uID. emptyUser),
  pass = (\<lambda> uID. emptyPass),

  pendingFReqs = (\<lambda> uID. []),
  friendReq = (\<lambda> uID uID'. emptyRequestInfo),
  friendIDs = (\<lambda> uID. []),

  sentOuterFriendIDs = (\<lambda> uID. []),
  recvOuterFriendIDs = (\<lambda> uID. []),

  postIDs = [],
  post = (\<lambda> papID. emptyPost),
  owner = (\<lambda> pID. emptyUserID),
  vis = (\<lambda> pID. FriendV),

  pendingSApiReqs = [],
  sApiReq = (\<lambda> aID. emptyRequestInfo),
  serverApiIDs = [],
  serverPass = (\<lambda> aID. emptyPass),
  outerPostIDs = (\<lambda> aID. []),
  outerPost = (\<lambda> aID papID. emptyPost),
  outerOwner = (\<lambda> aID papID. emptyUserID),
  outerVis = (\<lambda> aID pID. FriendV),

  pendingCApiReqs = [],
  cApiReq = (\<lambda> aID. emptyRequestInfo),
  clientApiIDs = [],
  clientPass = (\<lambda> aID. emptyPass),
  sharedWith = (\<lambda>pID. [])
 \<rparr>"


subsubsection \<open>Starting action\<close>

(* This initiates the current api. It has the following parameters:
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


subsubsection \<open>Creation actions\<close>


(* Create new user request: we allow users to choose their own IDs; they could be their email addresses. *)
definition createNUReq :: "state \<Rightarrow> userID \<Rightarrow> requestInfo \<Rightarrow> state"
where
"createNUReq s uID reqInfo \<equiv>
 s \<lparr>pendingUReqs := pendingUReqs s @ [uID],
    userReq := (userReq s)(uID := reqInfo)
\<rparr>"

definition e_createNUReq :: "state \<Rightarrow> userID \<Rightarrow> requestInfo \<Rightarrow> bool"
where
"e_createNUReq s uID requestInfo \<equiv>
 admin s \<in>\<in> userIDs s \<and> \<not> uID \<in>\<in> userIDs s \<and> \<not> uID \<in>\<in> pendingUReqs s"
(* a new-user request can be created only if the api has started, i.e., if an admin exists *)

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
    userReq := (userReq s)(uID := emptyRequestInfo)\<rparr>"

definition e_createUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_createUser s uID p uID' p' \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and> uID = admin s \<and> uID' \<in>\<in> pendingUReqs s"


(* Create post: note that post ID is an action parameter, and that the enabledness action
checks that it is fresh.
The API's interface will actually generate it, using getFresh. *)
definition createPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> state"
where
"createPost s uID p pID \<equiv>
 s \<lparr>postIDs := pID # postIDs s,
    post := (post s) (pID := emptyPost),
    owner := (owner s) (pID := uID)\<rparr>"
(* Recall from the initial state that the initial visibility is FriendV *)

definition e_createPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> bool"
where
"e_createPost s uID p pID \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and>
 \<not> pID \<in>\<in> postIDs s"

(* Friendship: *)
(* Create friend request, namely uID Reqs friendship of uID': *)
definition createFriendReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> requestInfo \<Rightarrow> state"
where
"createFriendReq s uID p uID' req \<equiv>
 let pfr = pendingFReqs s in
 s \<lparr>pendingFReqs := pfr (uID' := pfr uID' @ [uID]),
    friendReq := fun_upd2 (friendReq s) uID uID' req\<rparr>"

definition e_createFriendReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> requestInfo \<Rightarrow> bool"
where
"e_createFriendReq s uID p uID' req \<equiv>
 IDsOK s [uID,uID'] [] [] [] \<and> pass s uID = p \<and>
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
    friendReq := fun_upd2 (fun_upd2 (friendReq s) uID' uID emptyRequestInfo) uID uID' emptyRequestInfo\<rparr>"

definition e_createFriend :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_createFriend s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] [] [] \<and> pass s uID = p \<and>
 uID' \<in>\<in> pendingFReqs s uID"


subsubsection \<open>Deletion (removal) actions\<close>

(* Delete friend:   *)
definition deleteFriend :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> state"
where
"deleteFriend s uID p uID' \<equiv>
 let fr = friendIDs s in
 s \<lparr>friendIDs := fr (uID := removeAll uID' (fr uID), uID' := removeAll uID (fr uID'))\<rparr>"


definition e_deleteFriend :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_deleteFriend s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] [] [] \<and> pass s uID = p \<and>
 uID' \<in>\<in> friendIDs s uID"


subsubsection \<open>Updating actions\<close>

(* Users can update their passwords and names: *)
definition updateUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> password \<Rightarrow> name \<Rightarrow> inform \<Rightarrow> state"
where
"updateUser s uID p p' name info \<equiv>
 s \<lparr>user := (user s) (uID := Usr name info),
    pass := (pass s) (uID := p')\<rparr>"

definition e_updateUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> password \<Rightarrow> name \<Rightarrow> inform \<Rightarrow> bool"
where
"e_updateUser s uID p p' name info \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p"

definition updatePost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> post \<Rightarrow> state"
where
"updatePost s uID p pID pst \<equiv>
 let sW = sharedWith s in
 s \<lparr>post := (post s) (pID := pst),
    sharedWith := sW (pID := map (\<lambda> (aID,_). (aID,False)) (sW pID))\<rparr>"

definition e_updatePost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> post \<Rightarrow> bool"
where
"e_updatePost s uID p pID pst \<equiv>
 IDsOK s [uID] [pID] [] [] \<and> pass s uID = p \<and>
 owner s pID = uID"

definition updateVisPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> vis \<Rightarrow> state"
where
"updateVisPost s uID p pID vs \<equiv>
 s \<lparr>vis := (vis s) (pID := vs)\<rparr>"

definition e_updateVisPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> vis \<Rightarrow> bool"
where
"e_updateVisPost s uID p pID vs \<equiv>
 IDsOK s [uID] [pID] [] [] \<and> pass s uID = p \<and>
 owner s pID = uID \<and> vs \<in> {FriendV, PublicV}"

(* Note: Of course, the outer posts cannot be updated from this API. *)


subsubsection \<open>Reading actions\<close>

(* Read new user request: *)
definition readNUReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> requestInfo"
where
"readNUReq s uID p uID' \<equiv> userReq s uID'"

definition e_readNUReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_readNUReq s uID p uID' \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and>
 uID = admin s \<and> uID' \<in>\<in> pendingUReqs s"

(* A user can read their name (and so can all the other users), but not the password: *)
definition readUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> name"
where
"readUser s uID p uID' \<equiv> nameUser (user s uID')"

definition e_readUser :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_readUser s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] [] [] \<and> pass s uID = p"

(* A user can check if he is the admin: *)
definition readAmIAdmin :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"readAmIAdmin s uID p \<equiv> uID = admin s"

definition e_readAmIAdmin :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_readAmIAdmin s uID p \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p"

(* Reading posts: *)

definition readPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> post"
where
"readPost s uID p pID \<equiv> post s pID"

definition e_readPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> bool"
where
"e_readPost s uID p pID \<equiv>
 IDsOK s [uID] [pID] [] [] \<and> pass s uID = p \<and>
 (owner s pID = uID \<or> uID \<in>\<in> friendIDs s (owner s pID) \<or> vis s pID = PublicV)"

definition readOwnerPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> userID"
where
"readOwnerPost s uID p pID \<equiv> owner s pID"

definition e_readOwnerPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> bool"
where
"e_readOwnerPost s uID p pID \<equiv>
 IDsOK s [uID] [pID] [] [] \<and> pass s uID = p \<and>
 (admin s = uID \<or> owner s pID = uID \<or> uID \<in>\<in> friendIDs s (owner s pID) \<or> vis s pID = PublicV)"

definition readVisPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> vis"
where
"readVisPost s uID p pID \<equiv> vis s pID"

definition e_readVisPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> bool"
where
"e_readVisPost s uID p pID \<equiv>
 IDsOK s [uID] [pID] [] [] \<and> pass s uID = p \<and>
 (admin s = uID \<or> owner s pID = uID \<or> uID \<in>\<in> friendIDs s (owner s pID) \<or> vis s pID = PublicV)"

(* Reading outer posts: *)

definition readOPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> postID \<Rightarrow> post"
where
"readOPost s uID p aID pID \<equiv> outerPost s aID pID"

definition e_readOPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> postID \<Rightarrow> bool"
where
"e_readOPost s uID p aID pID \<equiv>
 IDsOK s [uID] [] [(aID,[pID])] [] \<and> pass s uID = p \<and>
 (admin s = uID \<or> (aID,outerOwner s aID pID) \<in>\<in> recvOuterFriendIDs s uID \<or> outerVis s aID pID = PublicV)"

definition readOwnerOPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> postID \<Rightarrow> userID"
where
"readOwnerOPost s uID p aID pID \<equiv> outerOwner s aID pID"

definition e_readOwnerOPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> postID \<Rightarrow> bool"
where
"e_readOwnerOPost s uID p aID pID \<equiv>
 IDsOK s [uID] [] [(aID,[pID])] [] \<and> pass s uID = p \<and>
 (admin s = uID \<or> (aID,outerOwner s aID pID) \<in>\<in> recvOuterFriendIDs s uID \<or> outerVis s aID pID = PublicV)"

definition readVisOPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> postID \<Rightarrow> vis"
where
"readVisOPost s uID p aID pID \<equiv> outerVis s aID pID"

definition e_readVisOPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> postID \<Rightarrow> bool"
where
"e_readVisOPost s uID p aID pID \<equiv>
 let post = outerPost s aID pID in
 IDsOK s [uID] [] [(aID,[pID])] [] \<and> pass s uID = p \<and>
 (admin s = uID \<or> (aID,outerOwner s aID pID) \<in>\<in> recvOuterFriendIDs s uID \<or>
  outerVis s aID pID = PublicV)"



(* Friendship: *)
(* Read friendship request to me: *)
definition readFriendReqToMe :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> requestInfo"
where
"readFriendReqToMe s uID p uID' \<equiv> friendReq s uID' uID"

definition e_readFriendReqToMe :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_readFriendReqToMe s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] [] [] \<and> pass s uID = p \<and>
 uID' \<in>\<in> pendingFReqs s uID"

(* Read friendship request from me: *)
definition readFriendReqFromMe :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> requestInfo"
where
"readFriendReqFromMe s uID p uID' \<equiv> friendReq s uID uID'"

definition e_readFriendReqFromMe :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_readFriendReqFromMe s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] [] [] \<and> pass s uID = p \<and>
 uID \<in>\<in> pendingFReqs s uID'"

(* Read request posted to a desired server api: *)
definition readSApiReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> requestInfo"
where
"readSApiReq s uID p uID' \<equiv> sApiReq s uID'"

definition e_readSApiReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> bool"
where
"e_readSApiReq s uID p uID' \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and>
 uID = admin s \<and> uID' \<in>\<in> pendingSApiReqs s"

(* Read request from possible client api: *)
definition readCApiReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> requestInfo"
where
"readCApiReq s uID p uID' \<equiv> cApiReq s uID'"

definition e_readCApiReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> bool"
where
"e_readCApiReq s uID p uID' \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and>
 uID = admin s \<and> uID' \<in>\<in> pendingCApiReqs s"


subsubsection \<open>Listing actions\<close>

(* list pending new user Reqs: *)
definition listPendingUReqs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID list"
where
"listPendingUReqs s uID p \<equiv> pendingUReqs s"

definition e_listPendingUReqs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listPendingUReqs s uID p \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and> uID = admin s"

(* list all users of the system: *)
definition listAllUsers :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID list"
where
"listAllUsers s uID p \<equiv> userIDs s"

definition e_listAllUsers :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listAllUsers s uID p \<equiv> IDsOK s [uID] [] [] [] \<and> pass s uID = p"

(* List a user's friends: *)
definition listFriends :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> userID list"
where
"listFriends s uID p uID' \<equiv> friendIDs s uID'"

definition e_listFriends :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_listFriends s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] [] [] \<and> pass s uID = p \<and>
 (uID = uID' \<or> uID \<in>\<in> friendIDs s uID')"

(* List the outer friendship authorizations sent by a user: *)
definition listSentOuterFriends :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> (apiID \<times> userID) list"
where
"listSentOuterFriends s uID p uID' \<equiv> sentOuterFriendIDs s uID'"

definition e_listSentOuterFriends :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> bool"
where
"e_listSentOuterFriends s uID p uID' \<equiv>
 IDsOK s [uID,uID'] [] [] [] \<and> pass s uID = p \<and>
 (uID = uID' \<or> uID \<in>\<in> friendIDs s uID')"

(* List the outer friendship authorizations received by a user: *)
definition listRecvOuterFriends :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> (apiID \<times> userID) list"
where
"listRecvOuterFriends s uID p \<equiv> recvOuterFriendIDs s uID"

definition e_listRecvOuterFriends :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listRecvOuterFriends s uID p \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p"

(* list posts internal to the api: *)
definition listInnerPosts :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> (userID \<times> postID) list"
where
"listInnerPosts s uID p \<equiv>
  [(owner s pID, pID).
    pID \<leftarrow> postIDs s,
    vis s pID \<noteq> FriendV \<or> uID \<in>\<in> friendIDs s (owner s pID) \<or> uID = owner s pID
  ]"

definition e_listInnerPosts :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listInnerPosts s uID p \<equiv> IDsOK s [uID] [] [] [] \<and> pass s uID = p"

(* list posts from other apis: *)
definition listOuterPosts :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> (apiID \<times> postID) list"
where
"listOuterPosts s uID p \<equiv>
  [(saID, pID).
    saID \<leftarrow> serverApiIDs s,
    pID \<leftarrow> outerPostIDs s saID,
    outerVis s saID pID = PublicV \<or> (saID, outerOwner s saID pID) \<in>\<in> recvOuterFriendIDs s uID
  ]"

definition e_listOuterPosts :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listOuterPosts s uID p \<equiv> IDsOK s [uID] [] [] [] \<and> pass s uID = p"

(* List all the api clients who have already received this post: *)
definition listClientsPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> (apiID \<times> bool) list"
where
"listClientsPost s uID p pID \<equiv> sharedWith s pID"

(* Only the admin can see these: *)
definition e_listClientsPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> bool"
where
"e_listClientsPost s uID p pID \<equiv>
 IDsOK s [uID] [pID] [] [] \<and> pass s uID = p \<and> uID = admin s"


(* list the pending Reqs from the current API to other APIs for them to become servers:  *)
definition listPendingSApiReqs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID list"
where
"listPendingSApiReqs s uID p \<equiv> pendingSApiReqs s"

definition e_listPendingSApiReqs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listPendingSApiReqs s uID p \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and> uID = admin s"

(* list the IDs of the server apis: *)
definition listServerAPIs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID list"
where
"listServerAPIs s uID p \<equiv> serverApiIDs s"

definition e_listServerAPIs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listServerAPIs s uID p \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and> uID = admin s"


(* list the pending Reqs from APIs that want to become clients of the current API:  *)
definition listPendingCApiReqs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID list"
where
"listPendingCApiReqs s uID p \<equiv> pendingCApiReqs s"

definition e_listPendingCApiReqs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listPendingCApiReqs s uID p \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and> uID = admin s"

(* list the IDs of the client apis: *)
definition listClientAPIs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID list"
where
"listClientAPIs s uID p \<equiv> clientApiIDs s"

definition e_listClientAPIs :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> bool"
where
"e_listClientAPIs s uID p \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and> uID = admin s"


subsubsection \<open>Actions of communication with other APIs\<close>

(* Note: Some of the communication actions are special in the following sense:
The initiator (the api's admin or, in the case of create outer friend, an arbitrary user, uID)
is different from the observer (another api, aID).  *)

(* The next 4 actions implement the protocol of connecting a server and a client:
-- It starts with the synchronized sendServerReq (with potential client as sender) and
  receiveClientReq (with potential server as receiver)
-- It finishes with the synchronized connectClient (with potential server as sender) and
 connectServer (with potential client as receiver)
 *)


(* Send request to potential server.
 sendServerReq s uID p aID reqInfo does the following: User uID (the admin)
send request to api aID wishing to subscribe to this server;
 In the implementation, the request info along with the URL of the current api (i.e., this api's ID)
 will be sent to the given api aID. *)
definition sendServerReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> requestInfo \<Rightarrow> (apiID \<times> requestInfo) \<times> state"
where
"sendServerReq s uID p aID reqInfo \<equiv>
 ((aID,reqInfo),
  s \<lparr>pendingSApiReqs := pendingSApiReqs s @ [aID],
     sApiReq := (sApiReq s) (aID := reqInfo)\<rparr>)"

definition e_sendServerReq :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> requestInfo \<Rightarrow> bool"
where
"e_sendServerReq s uID p aID reqInfo \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and>
 uID = admin s \<and> \<not> aID \<in>\<in> pendingSApiReqs s"

(* Receive request from potential client.
receiveClientReq s aID reqInfo does the following: receives registration request from
potential client api aID (which is a URL) with request info reqInfo. This action is
not trigered from any user of the current API -- it is an even coming from outside.
*)

definition receiveClientReq :: "state \<Rightarrow> apiID \<Rightarrow> requestInfo \<Rightarrow> state"
where
"receiveClientReq s aID reqInfo \<equiv>
 s \<lparr>pendingCApiReqs := pendingCApiReqs s @ [aID],
    cApiReq := (cApiReq s) (aID := reqInfo)\<rparr>"

definition e_receiveClientReq :: "state \<Rightarrow> apiID \<Rightarrow> requestInfo \<Rightarrow> bool"
where
"e_receiveClientReq s aID reqInfo \<equiv>
 \<not> aID \<in>\<in> pendingCApiReqs s \<and> admin s \<in>\<in> userIDs s"

(* Connect a client that had made a registration request.
connectClient s uID p aID cp does the following: The user uID (the admin)
picks up an api id aID from the list of pending requests and registers it as a client.
At the same time, it issues a password cp for the client, stores it and sends it to aID.
*)

definition connectClient :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> (apiID \<times> password) \<times> state"
where
"connectClient s uID p aID cp \<equiv>
 ((aID, cp),
  s \<lparr>clientApiIDs := (aID # clientApiIDs s),
     clientPass := (clientPass s) (aID := cp),
     pendingCApiReqs := remove1 aID (pendingCApiReqs s),
     cApiReq := (cApiReq s)(aID := emptyRequestInfo)\<rparr>
 )"

definition e_connectClient :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> bool"
where
"e_connectClient s uID p aID cp \<equiv>
 IDsOK s [uID] [] [] [] \<and> pass s uID = p \<and>
 uID = admin s \<and>
 aID \<in>\<in> pendingCApiReqs s \<and> \<not> aID \<in>\<in> clientApiIDs s"

(* Connect server api
connectServer s aID sp does the following: receives the password sp issued
by the potential server aID and stores it. It will be used for communicating with that server.
Of course, this action only succeeds if a request to aID had really been posted (which was
recorded in pendingSApiReqs).
*)
definition connectServer :: "state \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> state"
where
"connectServer s aID sp \<equiv>
 s \<lparr>serverApiIDs := (aID # serverApiIDs s),
    serverPass := (serverPass s) (aID := sp),
    pendingSApiReqs := remove1 aID (pendingSApiReqs s),
    sApiReq := (sApiReq s)(aID := emptyRequestInfo)\<rparr>"

definition e_connectServer :: "state \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> bool"
where
"e_connectServer s aID sp \<equiv>
 aID \<in>\<in> pendingSApiReqs s \<and> \<not> aID \<in>\<in> serverApiIDs s"

(* The next 2 actions represent server-client communication (always from server to client):
-- The server sends a post via sendPost
-- The client receives it via receivePost
Note that, since only the server sends messages to the client, it is the server who authenticates itself.
 *)

(* Send a post and its owner's ID (as well as the server credentials for communicating with that
client) to a client api. Also, recall that the post has now been shared with that client.  *)
definition sendPost ::
"state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> postID \<Rightarrow> (apiID \<times> password \<times> postID \<times> post \<times> userID \<times> vis) \<times> state"
where
"sendPost s uID p aID pID \<equiv>
 ((aID, clientPass s aID, pID, post s pID, owner s pID, vis s pID),
  s\<lparr>sharedWith := (sharedWith s) (pID := insert2 aID True (sharedWith s pID))\<rparr>)"

definition e_sendPost :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> postID \<Rightarrow> bool"
where
"e_sendPost s uID p aID pID \<equiv>
 IDsOK s [uID] [pID] [] [aID] \<and> pass s uID = p \<and>
 uID = admin s \<and> aID \<in>\<in> clientApiIDs s"

(* Receive a post and its owner's ID (as well as the server credentials) from a server api. *)
definition receivePost :: "state \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> post \<Rightarrow> userID \<Rightarrow> vis \<Rightarrow> state"
where
"receivePost s aID sp pID pst uID vs \<equiv>
 let opIDs = outerPostIDs s in
 s \<lparr>outerPostIDs := opIDs (aID :=  List.insert pID (opIDs aID)),
    outerPost := fun_upd2 (outerPost s) aID pID pst,
    outerOwner := fun_upd2 (outerOwner s) aID pID uID,
    outerVis := fun_upd2 (outerVis s) aID pID vs\<rparr>"

definition e_receivePost :: "state \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> postID \<Rightarrow> post \<Rightarrow> userID \<Rightarrow> vis \<Rightarrow> bool"
where
"e_receivePost s aID sp pID nt uID vs \<equiv>
 IDsOK s [] [] [(aID,[])] [] \<and> serverPass s aID = sp"


(* Create outer friend; unlike inner friendship, outer friendship is not necessarily symmetric.
It is always established from a user of a server to a user of a client, the former giving
unilateral access to the latter at his friend-only posts. These unilateral friendship permissions
are stored on the client.*)

(* sendCreateOFriend s uID p aID uID' means: User uID (of current api), with password p,
  sends an I-set-you-as-my-friend note to the presumptive user uID' on client api aID.
  The request uses the server credentials for the given client, as customary. *)
definition sendCreateOFriend ::
  "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> userID \<Rightarrow> (apiID \<times> password \<times> userID \<times> userID) \<times> state"
where
"sendCreateOFriend s uID p aID uID' \<equiv>
 let ofr = sentOuterFriendIDs s in
 ((aID, clientPass s aID, uID, uID'),
  s \<lparr>sentOuterFriendIDs := ofr (uID := ofr uID @ [(aID,uID')])\<rparr>)"

(* Note that the server (who issues the note) cannot check if uID' is a valid user on the client.
This will be checked on the client api only.*)
definition e_sendCreateOFriend :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> userID \<Rightarrow> bool"
where
"e_sendCreateOFriend s uID p caID uID' \<equiv>
 IDsOK s [uID] [] [] [caID] \<and> pass s uID = p \<and>
 \<not> (caID,uID') \<in>\<in> sentOuterFriendIDs s uID"

(* receiveCreateOFriend s sp saID uID uID' means: The current api receives, from
 one of its registered server apis aAID with password sp, an I-set-you-as-my-friend
 note from aAID's presumptive user uID to the current api's user uID'. The effect
 is that the current api will mark (saID,uID) in the list of outer friends of uID'
 (hence will allow uID' access to friend-only outer posts from uID). *)

definition receiveCreateOFriend :: "state \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> userID \<Rightarrow> state"
where
"receiveCreateOFriend s saID sp uID uID' \<equiv>
 let ofr = recvOuterFriendIDs s in
 s \<lparr>recvOuterFriendIDs := ofr (uID' := ofr uID' @ [(saID,uID)])\<rparr>"

definition e_receiveCreateOFriend :: "state \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> userID \<Rightarrow> bool"
where
"e_receiveCreateOFriend s saID sp uID uID' \<equiv>
 IDsOK s [] [] [(saID,[])] [] \<and> serverPass s saID = sp \<and>
 \<not> (saID,uID) \<in>\<in> recvOuterFriendIDs s uID'"


(* Deletion of outer friends *)

definition sendDeleteOFriend ::
  "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> userID \<Rightarrow> (apiID \<times> password \<times> userID \<times> userID) \<times> state"
where
"sendDeleteOFriend s uID p aID uID' \<equiv>
 let ofr = sentOuterFriendIDs s in
 ((aID, clientPass s aID, uID, uID'),
  s \<lparr>sentOuterFriendIDs := ofr (uID := remove1 (aID,uID') (ofr uID))\<rparr>)"

definition e_sendDeleteOFriend :: "state \<Rightarrow> userID \<Rightarrow> password \<Rightarrow> apiID \<Rightarrow> userID \<Rightarrow> bool"
where
"e_sendDeleteOFriend s uID p caID uID' \<equiv>
 IDsOK s [uID] [] [] [caID] \<and> pass s uID = p \<and>
 (caID,uID') \<in>\<in> sentOuterFriendIDs s uID"

definition receiveDeleteOFriend :: "state \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> userID \<Rightarrow> state"
where
"receiveDeleteOFriend s saID sp uID uID' \<equiv>
 let ofr = recvOuterFriendIDs s in
 s \<lparr>recvOuterFriendIDs := ofr (uID' := remove1 (saID,uID) (ofr uID'))\<rparr>"

definition e_receiveDeleteOFriend :: "state \<Rightarrow> apiID \<Rightarrow> password \<Rightarrow> userID \<Rightarrow> userID \<Rightarrow> bool"
where
"e_receiveDeleteOFriend s saID sp uID uID' \<equiv>
 IDsOK s [] [] [(saID,[])] [] \<and> serverPass s saID = sp \<and>
 (saID,uID) \<in>\<in> recvOuterFriendIDs s uID'"




subsection \<open>The step function\<close>

datatype out =
  (* Outputs for creation and update actions, as well as for other actions with errors: *)
  outOK | outErr |
  (* Outputs for reading actions: *)
  outBool bool| outName name |
  outPost post | outVis vis |
  outReq requestInfo |
  (* Outputs for listing actions: *)
  outUID "userID" | outUIDL "userID list" |
  outAIDL "apiID list"  |  outAIDBL "(apiID \<times> bool) list"  |
  outUIDPIDL "(userID \<times> postID)list" | outAIDPIDL "(apiID \<times> postID)list" |
  outAIDUIDL "(apiID \<times> userID) list" |
  (* Outputs specific to communication actions: *)
  O_sendServerReq "apiID \<times> requestInfo" | O_connectClient "apiID \<times> password" |
  O_sendPost "apiID \<times> password \<times> postID \<times> post \<times> userID \<times> vis" |
  O_sendCreateOFriend "apiID \<times> password \<times> userID \<times> userID" |
  O_sendDeleteOFriend "apiID \<times> password \<times> userID \<times> userID"


(* The content from outAIDPIDTT outputs: *)
fun from_O_sendPost where
 "from_O_sendPost (O_sendPost antt) = antt"
|"from_O_sendPost _ = undefined"


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
  cNUReq userID requestInfo
 |cUser userID password userID password
 |cPost userID password postID
 |cFriendReq userID password userID requestInfo
 |cFriend userID password userID

lemmas c_defs =
e_createNUReq_def createNUReq_def
e_createUser_def createUser_def
e_createPost_def createPost_def
e_createFriendReq_def createFriendReq_def
e_createFriend_def createFriend_def

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
"cStep s (cPost uID p pID) =
 (if e_createPost s uID p pID
    then (outOK, createPost s uID p pID)
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

fun cUserOfA :: "cActt \<Rightarrow> userID" where
 "cUserOfA (cNUReq uID req) = uID"
|"cUserOfA (cUser uID p uID' p') = uID"
|"cUserOfA (cPost uID p pID) = uID"
|"cUserOfA (cFriendReq uID p uID' req) = uID"
|"cUserOfA (cFriend uID p uID') = uID"

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
  isuUser: uUser userID password password name inform
 |isuPost: uPost userID password postID post
 |isuVisPost: uVisPost userID password postID vis

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

 |rOwnerPost userID password postID
 |rVisPost userID password postID

 |rOPost userID password apiID postID

 |rOwnerOPost userID password apiID postID
 |rVisOPost userID password apiID postID

 |rFriendReqToMe userID password userID
 |rFriendReqFromMe userID password userID
 |rSApiReq userID password apiID
 |rCApiReq userID password apiID

lemmas r_defs =
 readNUReq_def e_readNUReq_def
 readUser_def e_readUser_def
 readAmIAdmin_def e_readAmIAdmin_def

 readPost_def e_readPost_def

 readOwnerPost_def e_readOwnerPost_def
 readVisPost_def e_readVisPost_def

 readOPost_def e_readOPost_def

 readOwnerOPost_def e_readOwnerOPost_def
 readVisOPost_def e_readVisOPost_def

 readFriendReqToMe_def e_readFriendReqToMe_def
 readFriendReqFromMe_def e_readFriendReqFromMe_def
 readSApiReq_def e_readSApiReq_def
 readCApiReq_def e_readCApiReq_def

fun rObs :: "state \<Rightarrow> rActt \<Rightarrow> out" where
"rObs s (rNUReq uID p uID') =
 (if e_readNUReq s uID p uID' then outReq (readNUReq s uID p uID') else outErr)"
|
"rObs s (rUser uID p uID') =
 (if e_readUser s uID p uID' then outName (readUser s uID p uID') else outErr)"
|
"rObs s (rAmIAdmin uID p) =
 (if e_readAmIAdmin s uID p then outBool (readAmIAdmin s uID p) else outErr)"
|
"rObs s (rPost uID p pID) =
 (if e_readPost s uID p pID then outPost (readPost s uID p pID) else outErr)"
|
"rObs s (rOwnerPost uID p pID) =
 (if e_readOwnerPost s uID p pID then outUID (readOwnerPost s uID p pID) else outErr)"
|
"rObs s (rVisPost uID p pID) =
 (if e_readVisPost s uID p pID then outVis (readVisPost s uID p pID) else outErr)"
|
"rObs s (rOPost uID p aID pID) =
 (if e_readOPost s uID p aID pID then outPost (readOPost s uID p aID pID) else outErr)"
|
"rObs s (rOwnerOPost uID p aID pID) =
 (if e_readOwnerOPost s uID p aID pID then outUID (readOwnerOPost s uID p aID pID) else outErr)"
|
"rObs s (rVisOPost uID p aID pID) =
 (if e_readVisOPost s uID p aID pID then outVis (readVisOPost s uID p aID pID) else outErr)"
|

"rObs s (rFriendReqToMe uID p uID') =
 (if e_readFriendReqToMe s uID p uID' then outReq (readFriendReqToMe s uID p uID') else outErr)"
|
"rObs s (rFriendReqFromMe uID p uID') =
 (if e_readFriendReqFromMe s uID p uID' then outReq (readFriendReqFromMe s uID p uID') else outErr)"
|
"rObs s (rSApiReq uID p aID) =
 (if e_readSApiReq s uID p aID then outReq (readSApiReq s uID p aID) else outErr)"
|
"rObs s (rCApiReq uID p aID) =
 (if e_readCApiReq s uID p aID then outReq (readCApiReq s uID p aID) else outErr)"


fun rUserOfA :: "rActt \<Rightarrow> userID" where
 "rUserOfA (rNUReq uID p uID') = uID"
|"rUserOfA (rUser uID p uID') = uID"
|"rUserOfA (rAmIAdmin uID p) = uID"

|"rUserOfA (rPost uID p pID) = uID"
|"rUserOfA (rOwnerPost uID p pID) = uID"
|"rUserOfA (rVisPost uID p pID) = uID"

|"rUserOfA (rOPost uID p aID pID) = uID"
|"rUserOfA (rOwnerOPost uID p aID pID) = uID"
|"rUserOfA (rVisOPost uID p aID pID) = uID"

|"rUserOfA (rFriendReqToMe uID p uID') = uID"
|"rUserOfA (rFriendReqFromMe uID p uID') = uID"
|"rUserOfA (rSApiReq uID p aID) = uID"
|"rUserOfA (rCApiReq uID p aID) = uID"


(* Listing actions *)
datatype lActt =
  lPendingUReqs userID password
 |lAllUsers userID password
 |lFriends userID password userID
 |lSentOuterFriends userID password userID
 |lRecvOuterFriends userID password
 |lInnerPosts userID password
 |lOuterPosts userID password
 |lClientsPost userID password postID
 |lPendingSApiReqs userID password
 |lServerAPIs userID password
 |lPendingCApiReqs userID password
 |lClientAPIs userID password

lemmas l_defs =
 listPendingUReqs_def e_listPendingUReqs_def
 listAllUsers_def e_listAllUsers_def
 listFriends_def e_listFriends_def
 listSentOuterFriends_def e_listSentOuterFriends_def
 listRecvOuterFriends_def e_listRecvOuterFriends_def
 listInnerPosts_def e_listInnerPosts_def
 listOuterPosts_def e_listOuterPosts_def
 listClientsPost_def e_listClientsPost_def
 listPendingSApiReqs_def e_listPendingSApiReqs_def
 listServerAPIs_def e_listServerAPIs_def
 listPendingCApiReqs_def e_listPendingCApiReqs_def
 listClientAPIs_def e_listClientAPIs_def


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
"lObs s (lSentOuterFriends uID p uID') =
 (if e_listSentOuterFriends s uID p uID' then outAIDUIDL (listSentOuterFriends s uID p uID') else outErr)"
|
"lObs s (lRecvOuterFriends uID p) =
 (if e_listRecvOuterFriends s uID p then outAIDUIDL (listRecvOuterFriends s uID p) else outErr)"
|
"lObs s (lInnerPosts uID p) =
 (if e_listInnerPosts s uID p then outUIDPIDL (listInnerPosts s uID p) else outErr)"
|
"lObs s (lOuterPosts uID p) =
 (if e_listOuterPosts s uID p then outAIDPIDL (listOuterPosts s uID p) else outErr)"
|
"lObs s (lClientsPost uID p pID) =
 (if e_listClientsPost s uID p pID then outAIDBL (listClientsPost s uID p pID) else outErr)"
|
"lObs s (lPendingSApiReqs uID p) =
 (if e_listPendingSApiReqs s uID p then outAIDL (listPendingSApiReqs s uID p) else outErr)"
|
"lObs s (lServerAPIs uID p) =
 (if e_listServerAPIs s uID p then outAIDL (listServerAPIs s uID p) else outErr)"
|
"lObs s (lClientAPIs uID p) =
 (if e_listClientAPIs s uID p then outAIDL (listClientAPIs s uID p) else outErr)"
|
"lObs s (lPendingCApiReqs uID p) =
 (if e_listPendingCApiReqs s uID p then outAIDL (listPendingCApiReqs s uID p) else outErr)"

fun lUserOfA :: "lActt \<Rightarrow> userID" where
 "lUserOfA (lPendingUReqs uID p) = uID"
|"lUserOfA (lAllUsers uID p) = uID"
|"lUserOfA (lFriends uID p uID') = uID"
|"lUserOfA (lSentOuterFriends uID p uID') = uID"
|"lUserOfA (lRecvOuterFriends uID p) = uID"
|"lUserOfA (lInnerPosts uID p) = uID"
|"lUserOfA (lOuterPosts uID p) = uID"
|"lUserOfA (lClientsPost uID p pID) = uID"
|"lUserOfA (lPendingSApiReqs uID p) = uID"
|"lUserOfA (lServerAPIs uID p) = uID"
|"lUserOfA (lClientAPIs uID p) = uID"
|"lUserOfA (lPendingCApiReqs uID p) = uID"


(* Communication actions *)

datatype comActt =
  comSendServerReq userID password apiID requestInfo
 |comReceiveClientReq apiID requestInfo
 |comConnectClient userID password apiID password
 |comConnectServer apiID password
 |comReceivePost apiID password postID post userID vis
 |comSendPost userID password apiID postID
 |comReceiveCreateOFriend apiID password userID userID
 |comSendCreateOFriend userID password apiID userID
 |comReceiveDeleteOFriend apiID password userID userID
 |comSendDeleteOFriend userID password apiID userID

lemmas com_defs =
 sendServerReq_def e_sendServerReq_def
 receiveClientReq_def e_receiveClientReq_def
 connectClient_def e_connectClient_def
 connectServer_def e_connectServer_def
 receivePost_def e_receivePost_def
 sendPost_def e_sendPost_def
 receiveCreateOFriend_def e_receiveCreateOFriend_def
 sendCreateOFriend_def e_sendCreateOFriend_def
 receiveDeleteOFriend_def e_receiveDeleteOFriend_def
 sendDeleteOFriend_def e_sendDeleteOFriend_def

fun comStep :: "state \<Rightarrow> comActt \<Rightarrow> out \<times> state" where
"comStep s (comSendServerReq uID p aID reqInfo) =
 (if e_sendServerReq s uID p aID reqInfo
    then let (x,s) = sendServerReq s uID p aID reqInfo in (O_sendServerReq x, s)
    else (outErr, s))"
|
"comStep s (comReceiveClientReq aID reqInfo) =
 (if e_receiveClientReq s aID reqInfo then (outOK, receiveClientReq s aID reqInfo) else (outErr, s))"
|
"comStep s (comConnectClient uID p aID cp) =
 (if e_connectClient s uID p aID cp
    then let (aID_cp,s) = connectClient s uID p aID cp in (O_connectClient aID_cp, s)
    else (outErr, s))"
|
"comStep s (comConnectServer aID sp) =
 (if e_connectServer s aID sp then (outOK, connectServer s aID sp) else (outErr, s))"
|
"comStep s (comReceivePost aID sp pID nt uID vs) =
 (if e_receivePost s aID sp pID nt uID vs
    then (outOK, receivePost s aID sp pID nt uID vs)
    else (outErr, s))"
|
"comStep s (comSendPost uID p aID pID) =
 (if e_sendPost s uID p aID pID
    then let (x,s) = sendPost s uID p aID pID in (O_sendPost x, s)
    else (outErr, s))"
|
"comStep s (comReceiveCreateOFriend aID cp uID uID') =
 (if e_receiveCreateOFriend s aID cp uID uID'
    then (outOK, receiveCreateOFriend s aID cp uID uID')
    else (outErr, s))"
|
"comStep s (comSendCreateOFriend uID p aID uID') =
 (if e_sendCreateOFriend s uID p aID uID'
    then let (apuu,s) = sendCreateOFriend s uID p aID uID' in (O_sendCreateOFriend apuu, s)
    else (outErr, s))"
|
"comStep s (comReceiveDeleteOFriend aID cp uID uID') =
 (if e_receiveDeleteOFriend s aID cp uID uID'
    then (outOK, receiveDeleteOFriend s aID cp uID uID')
    else (outErr, s))"
|
"comStep s (comSendDeleteOFriend uID p aID uID') =
 (if e_sendDeleteOFriend s uID p aID uID'
    then let (apuu,s) = sendDeleteOFriend s uID p aID uID' in (O_sendDeleteOFriend apuu, s)
    else (outErr, s))"


fun comUserOfA :: "comActt \<Rightarrow> userID option" where
 "comUserOfA (comSendServerReq uID p aID reqInfo) = Some uID"
|"comUserOfA (comReceiveClientReq aID reqInfo) = None"
|"comUserOfA (comConnectClient uID p aID sp) = Some uID"
|"comUserOfA (comConnectServer aID sp) = None"
|"comUserOfA (comReceivePost aID sp pID nt uID vs) = None"
|"comUserOfA (comSendPost uID p aID pID) = Some uID"
|"comUserOfA (comReceiveCreateOFriend aID cp uID uID') = None"
|"comUserOfA (comSendCreateOFriend uID p aID uID') = Some uID"
|"comUserOfA (comReceiveDeleteOFriend aID cp uID uID') = None"
|"comUserOfA (comSendDeleteOFriend uID p aID uID') = Some uID"

fun comApiOfA :: "comActt \<Rightarrow> apiID" where
 "comApiOfA (comSendServerReq uID p aID reqInfo) = aID"
|"comApiOfA (comReceiveClientReq aID reqInfo) = aID"
|"comApiOfA (comConnectClient uID p aID sp) = aID"
|"comApiOfA (comConnectServer aID sp) = aID"
|"comApiOfA (comReceivePost aID sp pID nt uID vs) = aID"
|"comApiOfA (comSendPost uID p aID pID) = aID"
|"comApiOfA (comReceiveCreateOFriend aID cp uID uID') = aID"
|"comApiOfA (comSendCreateOFriend uID p aID uID') = aID"
|"comApiOfA (comReceiveDeleteOFriend aID cp uID uID') = aID"
|"comApiOfA (comSendDeleteOFriend uID p aID uID') = aID"


(* All actions: *)
datatype act =
  isSact: Sact sActt |
(* 3 kinds of effects: creation, deletion and update *)
  isCact: Cact cActt | isDact: Dact dActt | isUact: Uact uActt |
(* 2 kinds of observations: reading and listing (the latter mainly printing IDs) *)
  isRact: Ract rActt | isLact: Lact lActt |
(* Communications, which can themselves be either effects or ovbservations: *)
  isCOMact: COMact comActt

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
|
"step s (COMact ca) = comStep s ca"

fun userOfA :: "act \<Rightarrow> userID option" where
"userOfA (Sact sa) = Some (sUserOfA sa)"
|
"userOfA (Cact ca) = Some (cUserOfA ca)"
|
"userOfA (Dact da) = Some (dUserOfA da)"
|
"userOfA (Uact ua) = Some (uUserOfA ua)"
|
"userOfA (Ract ra) = Some (rUserOfA ra)"
|
"userOfA (Lact la) = Some (lUserOfA la)"
|
"userOfA (COMact ca) = comUserOfA ca"


interpretation IO_Automaton where
istate = istate and step = step
done


subsection \<open>Code generation\<close>

export_code step istate getFreshPostID in Scala

end
