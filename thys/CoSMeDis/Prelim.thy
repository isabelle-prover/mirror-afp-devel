section \<open>Preliminaries\<close>

theory Prelim
  imports
    "Fresh_Identifiers.Fresh_String"
    "Bounded_Deducibility_Security.Trivia"
begin


subsection \<open>The basic types\<close>

(*  This version of string is needed for code generation: *)
definition "emptyStr = STR ''''"

(* The users of the system: *)


datatype name = Nam String.literal
definition "emptyName \<equiv> Nam emptyStr"
datatype inform = Info String.literal
definition "emptyInfo \<equiv> Info emptyStr"

datatype user = Usr name inform
fun nameUser where "nameUser (Usr name info) = name"
fun infoUser where "infoUser (Usr name info) = info"
definition "emptyUser \<equiv> Usr emptyName emptyInfo"

typedecl raw_data
code_printing type_constructor raw_data \<rightharpoonup> (Scala) "java.io.File"

(* Images (currently, pdf, to be changed): *)
datatype img  = emptyImg | Imag raw_data
(* Visibility outside the current api: either friends-only or public
 (i.e., exportable outside to the other apis): *)
datatype vis = Vsb String.literal
(* Accepted values: friend and public  *)
abbreviation "FriendV \<equiv> Vsb (STR ''friend'')"
(* abbreviation "InternalV \<equiv> Vsb (STR ''internal'')" *)
abbreviation "PublicV \<equiv> Vsb (STR ''public'')"
fun stringOfVis where "stringOfVis (Vsb str) = str"

(* A post consists of a string for title, a string for its text,
  a (possibly empty) image and a visibility specification: *)

datatype title = Tit String.literal
definition "emptyTitle \<equiv> Tit emptyStr"
datatype "text" = Txt String.literal
definition "emptyText \<equiv> Txt emptyStr"

datatype post = Pst title "text" img (* vis *)
(* Getters: *)
fun titlePost where "titlePost (Pst title text img) = title"
fun textPost where "textPost (Pst title text img) = text"
fun imgPost where "imgPost (Pst title text img) = img"
(* fun visPost where "visPost (Pst title text img vis) = vis" *)
(* Setters: *)
fun setTitlePost where "setTitlePost (Pst title text img) title' = Pst title' text img"
fun setTextPost where "setTextPost(Pst title text img) text' = Pst title text' img"
fun setImgPost where "setImgPost (Pst title text img) img' = Pst title text img'"
(* fun setVisPost where "setVisPost (Pst title text img vis) vis' = Pst title text img vis'" *)
(*  *)
definition emptyPost :: post where
"emptyPost \<equiv> Pst emptyTitle emptyText emptyImg" (*  FriendV" *)
(* initially set to the lowest visibility: friend *)

lemma titlePost_emptyPost[simp]: "titlePost emptyPost = emptyTitle"
and textPost_emptyPost[simp]: "textPost emptyPost = emptyText"
and imgPost_emptyPost[simp]: "imgPost emptyPost = emptyImg"
(* and visPost_emptyPost[simp]: "visPost emptyPost = FriendV" *)
unfolding emptyPost_def by simp_all

lemma set_get_post[simp]:
"titlePost (setTitlePost ntc title) = title"
"titlePost (setTextPost ntc text) = titlePost ntc"
"titlePost (setImgPost ntc img) = titlePost ntc"
(* "titlePost (setVisPost ntc vis) = titlePost ntc" *)
(* *)
"textPost (setTitlePost ntc title) = textPost ntc"
"textPost (setTextPost ntc text) = text"
"textPost (setImgPost ntc img) = textPost ntc"
(* "textPost (setVisPost ntc vis) = textPost ntc" *)
(* *)
"imgPost (setTitlePost ntc title) = imgPost ntc"
"imgPost (setTextPost ntc text) = imgPost ntc"
"imgPost (setImgPost ntc img) = img"
(* "imgPost (setVisPost ntc vis) = imgPost ntc" *)
(* *)
(*
"visPost (setTitlePost ntc title) = visPost ntc"
"visPost (setTextPost ntc text) = visPost ntc"
"visPost (setImgPost ntc img) = visPost ntc"
"visPost (setVisPost ntc vis) = vis"
*)
(* *)
by(cases ntc, auto)+

lemma setTextPost_absorb[simp]:
"setTitlePost (setTitlePost pst tit) tit1 = setTitlePost pst tit1"
"setTextPost (setTextPost pst txt) txt1 = setTextPost pst txt1"
"setImgPost (setImgPost pst img) img1 = setImgPost pst img1"
(* "setVisPost (setVisPost pst vis) vis1 = setVisPost pst vis1" *)
by (cases pst, auto)+

datatype password = Psw String.literal
definition "emptyPass \<equiv> Psw emptyStr"

datatype salt = Slt String.literal
definition "emptySalt \<equiv> Slt emptyStr"

(* Information associated to requests for registration: both for users and apis *)
datatype requestInfo = ReqInfo String.literal
definition "emptyRequestInfo \<equiv> ReqInfo emptyStr"


subsection \<open>Identifiers\<close>

datatype apiID = Aid String.literal
datatype userID = Uid String.literal
datatype postID = Pid String.literal

definition "emptyApiID \<equiv> Aid emptyStr"
definition "emptyUserID \<equiv> Uid emptyStr"
definition "emptyPostID \<equiv> Pid emptyStr"

(*  *)
fun apiIDAsStr where "apiIDAsStr (Aid str) = str"

definition "getFreshApiID apiIDs \<equiv> Aid (fresh (set (map apiIDAsStr apiIDs)) (STR ''1''))"

lemma ApiID_apiIDAsStr[simp]: "Aid (apiIDAsStr apiID) = apiID"
by (cases apiID) auto

lemma member_apiIDAsStr_iff[simp]: "str \<in> apiIDAsStr ` apiIDs \<longleftrightarrow> Aid str \<in> apiIDs"
by (metis ApiID_apiIDAsStr image_iff apiIDAsStr.simps)

lemma getFreshApiID: "\<not> getFreshApiID apiIDs \<in>\<in> apiIDs"
using fresh_notIn[of "set (map apiIDAsStr apiIDs)"] unfolding getFreshApiID_def by auto

(*  *)
fun userIDAsStr where "userIDAsStr (Uid str) = str"

definition "getFreshUserID userIDs \<equiv> Uid (fresh (set (map userIDAsStr userIDs)) (STR ''2''))"

lemma UserID_userIDAsStr[simp]: "Uid (userIDAsStr userID) = userID"
by (cases userID) auto

lemma member_userIDAsStr_iff[simp]: "str \<in> userIDAsStr ` (set userIDs) \<longleftrightarrow> Uid str \<in>\<in> userIDs"
by (metis UserID_userIDAsStr image_iff userIDAsStr.simps)

lemma getFreshUserID: "\<not> getFreshUserID userIDs \<in>\<in> userIDs"
using fresh_notIn[of "set (map userIDAsStr userIDs)"] unfolding getFreshUserID_def by auto

(*  *)
fun postIDAsStr where "postIDAsStr (Pid str) = str"

definition "getFreshPostID postIDs \<equiv> Pid (fresh (set (map postIDAsStr postIDs)) (STR ''3''))"

lemma PostID_postIDAsStr[simp]: "Pid (postIDAsStr postID) = postID"
by (cases postID) auto

lemma member_postIDAsStr_iff[simp]: "str \<in> postIDAsStr ` (set postIDs) \<longleftrightarrow> Pid str \<in>\<in> postIDs"
by (metis PostID_postIDAsStr image_iff postIDAsStr.simps)

lemma getFreshPostID: "\<not> getFreshPostID postIDs \<in>\<in> postIDs"
using fresh_notIn[of "set (map postIDAsStr postIDs)"] unfolding getFreshPostID_def by auto

end
