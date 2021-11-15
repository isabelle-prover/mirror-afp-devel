section \<open>Preliminaries\<close>

theory Prelim
  imports
    "Bounded_Deducibility_Security.Compositional_Reasoning"
    "Fresh_Identifiers.Fresh_String"
begin


subsection\<open>The basic types\<close>

definition "emptyStr = STR ''''"

(* The users of the system: *)


datatype name = Nam String.literal
definition "emptyName \<equiv> Nam emptyStr"
datatype inform = Info String.literal
definition "emptyInfo \<equiv> Info emptyStr"

datatype user = Usr (nameUser : name) (infoUser : inform)
definition "emptyUser \<equiv> Usr emptyName emptyInfo"
fun niUser where "niUser (Usr name info) = (name,info)"


typedecl raw_data
code_printing type_constructor raw_data \<rightharpoonup> (Scala) "java.io.File"

(* Images (currently, pdf, to be changed): *)
datatype img  = emptyImg | Imag raw_data
(* Visibility outside the current api: either friends-only or public  *)
datatype vis = Vsb String.literal
(* Accepted values: friend and public  *)
abbreviation "FriendV \<equiv> Vsb (STR ''friend'')"
abbreviation "PublicV \<equiv> Vsb (STR ''public'')"
fun stringOfVis where "stringOfVis (Vsb str) = str"

(* A post consists of a string for title, a string for its text,
  a (possibly empty) image and a visibility specification: *)

datatype title = Tit String.literal
definition "emptyTitle \<equiv> Tit emptyStr"
datatype "text" = Txt String.literal
definition "emptyText \<equiv> Txt emptyStr"

datatype post = Ntc (titlePost : title) (textPost : "text") (imgPost : img)
(* Setters: *)
fun setTitlePost where "setTitlePost (Ntc title text img) title' = Ntc title' text img"
fun setTextPost where "setTextPost(Ntc title text img) text' = Ntc title text' img"
fun setImgPost where "setImgPost (Ntc title text img) img' = Ntc title text img'"
(*  *)
definition emptyPost :: post where
"emptyPost \<equiv> Ntc emptyTitle emptyText emptyImg"
(* initially set to the lowest visibility: friend *)

lemma set_get_post[simp]:
"titlePost (setTitlePost ntc title) = title"
"titlePost (setTextPost ntc text) = titlePost ntc"
"titlePost (setImgPost ntc img) = titlePost ntc"
(* *)
"textPost (setTitlePost ntc title) = textPost ntc"
"textPost (setTextPost ntc text) = text"
"textPost (setImgPost ntc img) = textPost ntc"
(* *)
"imgPost (setTitlePost ntc title) = imgPost ntc"
"imgPost (setTextPost ntc text) = imgPost ntc"
"imgPost (setImgPost ntc img) = img"
by(cases ntc, auto)+

datatype password = Psw String.literal
definition "emptyPass \<equiv> Psw emptyStr"

(* Information associated to requests for registration: both for users and apps *)
datatype req = ReqInfo String.literal
definition "emptyReq \<equiv> ReqInfo emptyStr"


subsection \<open>Identifiers\<close>

datatype userID = Uid String.literal
datatype postID = Nid String.literal

definition "emptyUserID \<equiv> Uid emptyStr"
definition "emptyPostID \<equiv> Nid emptyStr"


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
fun postIDAsStr where "postIDAsStr (Nid str) = str"

definition "getFreshPostID postIDs \<equiv> Nid (fresh (set (map postIDAsStr postIDs)) (STR ''3''))"

lemma PostID_postIDAsStr[simp]: "Nid (postIDAsStr postID) = postID"
by (cases postID) auto

lemma member_postIDAsStr_iff[simp]: "str \<in> postIDAsStr ` (set postIDs) \<longleftrightarrow> Nid str \<in>\<in> postIDs"
by (metis PostID_postIDAsStr image_iff postIDAsStr.simps)

lemma getFreshPostID: "\<not> getFreshPostID postIDs \<in>\<in> postIDs"
using fresh_notIn[of "set (map postIDAsStr postIDs)"] unfolding getFreshPostID_def by auto

end
