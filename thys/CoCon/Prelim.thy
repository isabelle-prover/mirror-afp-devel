(* Preliminaries concerning the involved data types and auxiliary functions  *)
theory Prelim
  imports "Fresh_Identifiers.Fresh_String" "Bounded_Deducibility_Security.Trivia"
begin


subsection \<open>The basic types\<close>

(*  This version of string is needed for code generation: *)
type_synonym string = String.literal
definition "emptyStr = STR ''''"

type_synonym phase = nat

(* Conference phases: no phase, setup, submission, bidding, reviewing, discussion, notification, closed *)
abbreviation "noPH \<equiv> (0::nat)"    abbreviation "setPH \<equiv> Suc noPH"  abbreviation "subPH \<equiv> Suc setPH"
abbreviation "bidPH \<equiv> Suc subPH"  abbreviation "revPH \<equiv> Suc bidPH" abbreviation "disPH \<equiv> Suc revPH"
abbreviation "notifPH \<equiv> Suc disPH"  abbreviation "closedPH \<equiv> Suc notifPH"

fun SucPH where
"SucPH ph = (if ph = closedPH then closedPH else Suc ph)"

(* The users of the system: *)
datatype user = User string string string
fun nameUser where "nameUser (User name info email) = name"
fun infoUser where "infoUser (User name info email) = info"
fun emailUser where "emailUser (User name info email) = email"
definition "emptyUser \<equiv> User emptyStr emptyStr emptyStr"

typedecl raw_data
code_printing type_constructor raw_data \<rightharpoonup> (Scala) "java.io.File"

(* paper content: *)
datatype pcontent = NoPContent | PContent raw_data

datatype score = NoScore | MinusThree | MinusTwo | MinusOne | Zero | One | Two | Three

fun scoreAsInt :: "score \<Rightarrow> int" where
 "scoreAsInt MinusThree = -3"
|"scoreAsInt MinusTwo = -2"
|"scoreAsInt MinusOne = -1"
|"scoreAsInt Zero = 0"
|"scoreAsInt One = 1"
|"scoreAsInt Two = 2"
|"scoreAsInt Three = 3"

datatype exp = NoExp | Zero | One | Two | Three | Four (* expertise *)
(* A review content consists of an expertise, a score and the review text *)
(* review content: *)
type_synonym rcontent = "exp * score * string"
fun scoreOf :: "rcontent \<Rightarrow> score" where "scoreOf (exp,sc,txt) = sc"
(* A review is a list of review contents, with the first (i.e., the head) being the most recent. *)
type_synonym review = "rcontent list"
(* A reviewer may change the expertise, score and the review (multiple times) during the discussion phase,
   but all changes should be transparent, i.e., history of changes should be recorded;
   this is why a review is a list of review contents rather than a single review content.
*)

abbreviation emptyReview :: review where "emptyReview \<equiv> []"
datatype discussion = Dis "string list"
definition "emptyDis \<equiv> Dis []"
datatype decision = NoDecision | Accept | Reject

(* A paper consists of strings for title and abstract,
the paper content, the associated reviews, a discussion and an (updatable) decision.
 *)
datatype paper = Paper string string pcontent "review list" discussion "decision list"

fun titlePaper where "titlePaper (Paper title abstract content reviews dis decs) = title"
fun abstractPaper where "abstractPaper (Paper title abstract content reviews dis decs) = abstract"
fun contentPaper where "contentPaper (Paper title abstract content reviews dis decs) = content"
fun reviewsPaper where "reviewsPaper (Paper title abstract content reviews dis decs) = reviews"
fun disPaper where "disPaper (Paper title abstract content reviews dis decs) = dis"
(* all successive decisions for a paper, listed historically: *)
fun decsPaper where "decsPaper (Paper title abstract content reviews dis decs) = decs"
(* the current decision: *)
fun decPaper where "decPaper pap = hd (decsPaper pap)"



definition emptyPaper :: paper where
"emptyPaper \<equiv> Paper emptyStr emptyStr NoPContent [] emptyDis []"

(* Data (info) associated to a conference: *)
datatype conf = Conf string string
fun nameConf where "nameConf (Conf name info) = name"
fun infoConf where "infoConf (Conf name info) = info"
definition "emptyConf \<equiv> Conf emptyStr emptyStr"

datatype password = Password string
definition "emptyPass \<equiv> Password emptyStr"

datatype preference = NoPref | Want | Would | WouldNot | Conflict


subsection \<open>Conference, user and paper IDs\<close>

datatype userID = UserID string
datatype paperID = PaperID string
datatype confID = ConfID string

definition "emptyUserID \<equiv> UserID emptyStr"
definition "voronkovUserID \<equiv> UserID (STR ''voronkov'')"
definition "emptyPaperID \<equiv> PaperID emptyStr"
definition "emptyConfID \<equiv> ConfID emptyStr"

(* Roles: author, reviewer (owner of the nth review of a paper), program committee (PC) member, chair *)
datatype role = Aut paperID | Rev paperID nat | PC | Chair
fun isRevRole where "isRevRole (Rev _ _ ) = True" | "isRevRole _ = False"

fun isRevRoleFor :: "paperID \<Rightarrow> role \<Rightarrow> bool" where
 "isRevRoleFor papID (Rev papID' n) \<longleftrightarrow> papID = papID'"
|"isRevRoleFor papID _ \<longleftrightarrow> False"

(* *)
fun userIDAsStr where "userIDAsStr (UserID str) = str"

definition "getFreshUserID userIDs \<equiv> UserID (fresh (set (map userIDAsStr userIDs)) (STR ''1''))"

lemma UserID_userIDAsStr[simp]: "UserID (userIDAsStr userID) = userID"
by (cases userID) auto

lemma member_userIDAsStr_iff[simp]: "str \<in> userIDAsStr ` (set userIDs) \<longleftrightarrow> UserID str \<in>\<in> userIDs"
by (metis UserID_userIDAsStr image_iff userIDAsStr.simps)

lemma getFreshUserID: "\<not> getFreshUserID userIDs \<in>\<in> userIDs"
  using fresh_notIn[of "set (map userIDAsStr userIDs)" "STR ''1''"]
  by (auto simp: getFreshUserID_def)

instantiation userID :: linorder
begin
definition le_userID_def: "uid \<le> uid' \<equiv> case (uid,uid') of (UserID str, UserID str') \<Rightarrow> str \<le> str'"
definition lt_userID_def: "uid < uid' \<equiv> case (uid,uid') of (UserID str, UserID str') \<Rightarrow> str < str'"
instance by standard (auto simp: le_userID_def lt_userID_def split: userID.splits)
end

(*  *)
fun paperIDAsStr where "paperIDAsStr (PaperID str) = str"

definition "getFreshPaperID paperIDs \<equiv> PaperID (fresh (set (map paperIDAsStr paperIDs)) (STR ''2''))"

lemma PaperID_paperIDAsStr[simp]: "PaperID (paperIDAsStr paperID) = paperID"
by (cases paperID) auto

lemma member_paperIDAsStr_iff[simp]: "str \<in> paperIDAsStr ` paperIDs \<longleftrightarrow> PaperID str \<in> paperIDs"
by (metis PaperID_paperIDAsStr image_iff paperIDAsStr.simps)

lemma getFreshPaperID: "\<not> getFreshPaperID paperIDs \<in>\<in> paperIDs"
  using fresh_notIn[of "set (map paperIDAsStr paperIDs)" "STR ''2''"]
  by (auto simp: getFreshPaperID_def)

instantiation paperID :: linorder
begin
definition le_paperID_def: "uid \<le> uid' \<equiv> case (uid,uid') of (PaperID str, PaperID str') \<Rightarrow> str \<le> str'"
definition lt_paperID_def: "uid < uid' \<equiv> case (uid,uid') of (PaperID str, PaperID str') \<Rightarrow> str < str'"
instance by standard (auto simp: le_paperID_def lt_paperID_def split: paperID.splits)
end

(*  *)
fun confIDAsStr where "confIDAsStr (ConfID str) = str"

definition "getFreshConfID confIDs \<equiv> ConfID (fresh (set (map confIDAsStr confIDs)) (STR ''2''))"

lemma ConfID_confIDAsStr[simp]: "ConfID (confIDAsStr confID) = confID"
by (cases confID) auto

lemma member_confIDAsStr_iff[simp]: "str \<in> confIDAsStr ` (set confIDs) \<longleftrightarrow> ConfID str \<in>\<in> confIDs"
by (metis ConfID_confIDAsStr image_iff confIDAsStr.simps)

lemma getFreshConfID: "\<not> getFreshConfID confIDs \<in>\<in> confIDs"
  using fresh_notIn[of "set (map confIDAsStr confIDs)" "STR ''2''"]
  by (auto simp: getFreshConfID_def)

instantiation confID :: linorder
begin
definition le_confID_def: "uid \<le> uid' \<equiv> case (uid,uid') of (ConfID str, ConfID str') \<Rightarrow> str \<le> str'"
definition lt_confID_def: "uid < uid' \<equiv> case (uid,uid') of (ConfID str, ConfID str') \<Rightarrow> str < str'"
instance by standard (auto simp: le_confID_def lt_confID_def split: confID.splits)
end


end
