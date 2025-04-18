(*  Title:      POPLmark/POPLmarkRecord.thy
    Author:     Stefan Berghofer, TU Muenchen, 2005
*)

theory POPLmarkRecord
  imports Basis
begin

section \<open>Extending the calculus with records\<close>

text \<open>
\label{sec:record-calculus}
We now describe how the calculus introduced in the previous section can
be extended with records. An important point to note is that many of the
definitions and proofs developed for the simple calculus can be reused.
\<close>


subsection \<open>Types and Terms\<close>

text \<open>
In order to represent records, we also need a type of {\it field names}.
For this purpose, we simply use the type of {\it strings}. We extend the
datatype of types of System \fsub{} by a new constructor \<open>RcdT\<close>
representing record types.
\<close>

type_synonym name = string

datatype type =
    TVar nat
  | Top
  | Fun type type    (infixr \<open>\<rightarrow>\<close> 200)
  | TyAll type type  (\<open>(3\<forall><:_./ _)\<close> [0, 10] 10)
  | RcdT "(name \<times> type) list"

type_synonym fldT = "name \<times> type"
type_synonym rcdT = "(name \<times> type) list"

datatype binding = VarB type | TVarB type

type_synonym env = "binding list"

primrec is_TVarB :: "binding \<Rightarrow> bool"
where
  "is_TVarB (VarB T) = False"
| "is_TVarB (TVarB T) = True"

primrec type_ofB :: "binding \<Rightarrow> type"
where
  "type_ofB (VarB T) = T"
| "type_ofB (TVarB T) = T"

primrec mapB :: "(type \<Rightarrow> type) \<Rightarrow> binding \<Rightarrow> binding"
where
  "mapB f (VarB T) = VarB (f T)"
| "mapB f (TVarB T) = TVarB (f T)"

text \<open>
A record type is essentially an association list, mapping names of record fields
to their types.
The types of bindings and environments remain unchanged. The datatype \<open>trm\<close>
of terms is extended with three new constructors \<open>Rcd\<close>, \<open>Proj\<close>,
and \<open>LET\<close>, denoting construction of a new record, selection of
a specific field of a record (projection), and matching of a record against
a pattern, respectively. A pattern, represented by datatype \<open>pat\<close>,
can be either a variable matching any value of a given type, or a nested
record pattern. Due to the encoding of variables using de Bruijn indices,
a variable pattern only consists of a type.
\<close>

datatype pat = PVar type | PRcd "(name \<times> pat) list"

datatype trm =
    Var nat
  | Abs type trm   (\<open>(3\<lambda>:_./ _)\<close> [0, 10] 10)
  | TAbs type trm  (\<open>(3\<lambda><:_./ _)\<close> [0, 10] 10)
  | App trm trm    (infixl \<open>\<bullet>\<close> 200)
  | TApp trm type  (infixl \<open>\<bullet>\<^sub>\<tau>\<close> 200)
  | Rcd "(name \<times> trm) list"
  | Proj trm name  (\<open>(_.._)\<close> [90, 91] 90)
  | LET pat trm trm (\<open>(LET (_ =/ _)/ IN (_))\<close> 10)

type_synonym fld = "name \<times> trm"
type_synonym rcd = "(name \<times> trm) list"
type_synonym fpat = "name \<times> pat"
type_synonym rpat = "(name \<times> pat) list"

text \<open>
In order to motivate the typing and evaluation rules for the \<open>LET\<close>, it is
important to note that an expression of the form
@{text [display] "LET PRcd [(l\<^sub>1, PVar T\<^sub>1), \<dots>, (l\<^sub>n, PVar T\<^sub>n)] = Rcd [(l\<^sub>1, v\<^sub>1), \<dots>, (l\<^sub>n, v\<^sub>n)] IN t"}
can be treated like a nested abstraction \<open>(\<lambda>:T\<^sub>1. \<dots> \<lambda>:T\<^sub>n. t) \<bullet> v\<^sub>1 \<bullet> \<dots> \<bullet> v\<^sub>n\<close>
\<close>


subsection \<open>Lifting and Substitution\<close>

primrec psize :: "pat \<Rightarrow> nat" (\<open>\<parallel>_\<parallel>\<^sub>p\<close>)
  and rsize :: "rpat \<Rightarrow> nat" (\<open>\<parallel>_\<parallel>\<^sub>r\<close>)
  and fsize :: "fpat \<Rightarrow> nat" (\<open>\<parallel>_\<parallel>\<^sub>f\<close>)
where
  "\<parallel>PVar T\<parallel>\<^sub>p = 1"
| "\<parallel>PRcd fs\<parallel>\<^sub>p = \<parallel>fs\<parallel>\<^sub>r"
| "\<parallel>[]\<parallel>\<^sub>r = 0"
| "\<parallel>f \<Colon> fs\<parallel>\<^sub>r = \<parallel>f\<parallel>\<^sub>f + \<parallel>fs\<parallel>\<^sub>r"
| "\<parallel>(l, p)\<parallel>\<^sub>f = \<parallel>p\<parallel>\<^sub>p"

primrec liftT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type" (\<open>\<up>\<^sub>\<tau>\<close>)
  and liftrT :: "nat \<Rightarrow> nat \<Rightarrow> rcdT \<Rightarrow> rcdT" (\<open>\<up>\<^sub>r\<^sub>\<tau>\<close>)
  and liftfT :: "nat \<Rightarrow> nat \<Rightarrow> fldT \<Rightarrow> fldT" (\<open>\<up>\<^sub>f\<^sub>\<tau>\<close>)
where
  "\<up>\<^sub>\<tau> n k (TVar i) = (if i < k then TVar i else TVar (i + n))"
| "\<up>\<^sub>\<tau> n k Top = Top"
| "\<up>\<^sub>\<tau> n k (T \<rightarrow> U) = \<up>\<^sub>\<tau> n k T \<rightarrow> \<up>\<^sub>\<tau> n k U"
| "\<up>\<^sub>\<tau> n k (\<forall><:T. U) = (\<forall><:\<up>\<^sub>\<tau> n k T. \<up>\<^sub>\<tau> n (k + 1) U)"
| "\<up>\<^sub>\<tau> n k (RcdT fs) = RcdT (\<up>\<^sub>r\<^sub>\<tau> n k fs)"
| "\<up>\<^sub>r\<^sub>\<tau> n k [] = []"
| "\<up>\<^sub>r\<^sub>\<tau> n k (f \<Colon> fs) = \<up>\<^sub>f\<^sub>\<tau> n k f \<Colon> \<up>\<^sub>r\<^sub>\<tau> n k fs"
| "\<up>\<^sub>f\<^sub>\<tau> n k (l, T) = (l, \<up>\<^sub>\<tau> n k T)"

primrec liftp :: "nat \<Rightarrow> nat \<Rightarrow> pat \<Rightarrow> pat" (\<open>\<up>\<^sub>p\<close>)
  and liftrp :: "nat \<Rightarrow> nat \<Rightarrow> rpat \<Rightarrow> rpat" (\<open>\<up>\<^sub>r\<^sub>p\<close>)
  and liftfp :: "nat \<Rightarrow> nat \<Rightarrow> fpat \<Rightarrow> fpat" (\<open>\<up>\<^sub>f\<^sub>p\<close>)
where
  "\<up>\<^sub>p n k (PVar T) = PVar (\<up>\<^sub>\<tau> n k T)"
| "\<up>\<^sub>p n k (PRcd fs) = PRcd (\<up>\<^sub>r\<^sub>p n k fs)"
| "\<up>\<^sub>r\<^sub>p n k [] = []"
| "\<up>\<^sub>r\<^sub>p n k (f \<Colon> fs) = \<up>\<^sub>f\<^sub>p n k f \<Colon> \<up>\<^sub>r\<^sub>p n k fs"
| "\<up>\<^sub>f\<^sub>p n k (l, p) = (l, \<up>\<^sub>p n k p)"

primrec lift :: "nat \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm" (\<open>\<up>\<close>)
  and liftr :: "nat \<Rightarrow> nat \<Rightarrow> rcd \<Rightarrow> rcd" (\<open>\<up>\<^sub>r\<close>)
  and liftf :: "nat \<Rightarrow> nat \<Rightarrow> fld \<Rightarrow> fld" (\<open>\<up>\<^sub>f\<close>)
where
  "\<up> n k (Var i) = (if i < k then Var i else Var (i + n))"
| "\<up> n k (\<lambda>:T. t) = (\<lambda>:\<up>\<^sub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (\<lambda><:T. t) = (\<lambda><:\<up>\<^sub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (s \<bullet> t) = \<up> n k s \<bullet> \<up> n k t"
| "\<up> n k (t \<bullet>\<^sub>\<tau> T) = \<up> n k t \<bullet>\<^sub>\<tau> \<up>\<^sub>\<tau> n k T"
| "\<up> n k (Rcd fs) = Rcd (\<up>\<^sub>r n k fs)"
| "\<up> n k (t..a) = (\<up> n k t)..a"
| "\<up> n k (LET p = t IN u) = (LET \<up>\<^sub>p n k p = \<up> n k t IN \<up> n (k + \<parallel>p\<parallel>\<^sub>p) u)"
| "\<up>\<^sub>r n k [] = []"
| "\<up>\<^sub>r n k (f \<Colon> fs) = \<up>\<^sub>f n k f \<Colon> \<up>\<^sub>r n k fs"
| "\<up>\<^sub>f n k (l, t) = (l, \<up> n k t)"

primrec substTT :: "type \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>\<tau>\<close> [300, 0, 0] 300)
  and substrTT :: "rcdT \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> rcdT"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>r\<^sub>\<tau>\<close> [300, 0, 0] 300)
  and substfTT :: "fldT \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> fldT"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>f\<^sub>\<tau>\<close> [300, 0, 0] 300)
where
  "(TVar i)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> =
     (if k < i then TVar (i - 1) else if i = k then \<up>\<^sub>\<tau> k 0 S else TVar i)"
| "Top[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = Top"
| "(T \<rightarrow> U)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> \<rightarrow> U[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>"
| "(\<forall><:T. U)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = (\<forall><:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. U[k+1 \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>)"
| "(RcdT fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = RcdT (fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>\<tau>)"
| "[][k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>\<tau> = []"
| "(f \<Colon> fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>\<tau> = f[k \<mapsto>\<^sub>\<tau> S]\<^sub>f\<^sub>\<tau> \<Colon> fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>\<tau>"
| "(l, T)[k \<mapsto>\<^sub>\<tau> S]\<^sub>f\<^sub>\<tau> = (l, T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>)"

primrec substpT :: "pat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> pat"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>p\<close> [300, 0, 0] 300)
  and substrpT :: "rpat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> rpat"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>r\<^sub>p\<close> [300, 0, 0] 300)
  and substfpT :: "fpat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> fpat"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>f\<^sub>p\<close> [300, 0, 0] 300)
where
  "(PVar T)[k \<mapsto>\<^sub>\<tau> S]\<^sub>p = PVar (T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>)"
| "(PRcd fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>p = PRcd (fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>p)"
| "[][k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>p = []"
| "(f \<Colon> fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>p = f[k \<mapsto>\<^sub>\<tau> S]\<^sub>f\<^sub>p \<Colon> fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>p"
| "(l, p)[k \<mapsto>\<^sub>\<tau> S]\<^sub>f\<^sub>p = (l, p[k \<mapsto>\<^sub>\<tau> S]\<^sub>p)"

primrec decp :: "nat \<Rightarrow> nat \<Rightarrow> pat \<Rightarrow> pat"  (\<open>\<down>\<^sub>p\<close>)
where
  "\<down>\<^sub>p 0 k p = p"
| "\<down>\<^sub>p (Suc n) k p = \<down>\<^sub>p n k (p[k \<mapsto>\<^sub>\<tau> Top]\<^sub>p)"

text \<open>
In addition to the lifting and substitution functions already needed for the
basic calculus, we also have to define lifting and substitution functions
for patterns, which we denote by @{term "\<up>\<^sub>p n k p"} and @{term "T[k \<mapsto>\<^sub>\<tau> S]\<^sub>p"},
respectively. The extension of the existing lifting and substitution
functions to records is fairly standard.
\<close>

primrec subst :: "trm \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm"  (\<open>_[_ \<mapsto> _]\<close> [300, 0, 0] 300)
  and substr :: "rcd \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> rcd"  (\<open>_[_ \<mapsto> _]\<^sub>r\<close> [300, 0, 0] 300)
  and substf :: "fld \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> fld"  (\<open>_[_ \<mapsto> _]\<^sub>f\<close> [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto> s] =
     (if k < i then Var (i - 1) else if i = k then \<up> k 0 s else Var i)"
| "(t \<bullet> u)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet> u[k \<mapsto> s]"
| "(t \<bullet>\<^sub>\<tau> T)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet>\<^sub>\<tau> T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
| "(\<lambda>:T. t)[k \<mapsto> s] = (\<lambda>:T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>. t[k+1 \<mapsto> s])"
| "(\<lambda><:T. t)[k \<mapsto> s] = (\<lambda><:T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>. t[k+1 \<mapsto> s])"
| "(Rcd fs)[k \<mapsto> s] = Rcd (fs[k \<mapsto> s]\<^sub>r)"
| "(t..a)[k \<mapsto> s] = (t[k \<mapsto> s])..a"
| "(LET p = t IN u)[k \<mapsto> s] = (LET \<down>\<^sub>p 1 k p = t[k \<mapsto> s] IN u[k + \<parallel>p\<parallel>\<^sub>p \<mapsto> s])"
| "[][k \<mapsto> s]\<^sub>r = []"
| "(f \<Colon> fs)[k \<mapsto> s]\<^sub>r = f[k \<mapsto> s]\<^sub>f \<Colon> fs[k \<mapsto> s]\<^sub>r"
| "(l, t)[k \<mapsto> s]\<^sub>f = (l, t[k \<mapsto> s])"

text \<open>
Note that the substitution function on terms is defined simultaneously
with a substitution function @{term "fs[k \<mapsto> s]\<^sub>r"} on records (i.e.\ lists
of fields), and a substitution function @{term "f[k \<mapsto> s]\<^sub>f"} on fields.
To avoid conflicts with locally bound variables, we have to add an offset
@{term "\<parallel>p\<parallel>\<^sub>p"} to @{term k} when performing substitution in the body of
the \<open>LET\<close> binder, where @{term "\<parallel>p\<parallel>\<^sub>p"} is the number of variables
in the pattern @{term p}.
\<close>

primrec substT :: "trm \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> trm"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<close> [300, 0, 0] 300)
  and substrT :: "rcd \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> rcd"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>r\<close> [300, 0, 0] 300)
  and substfT :: "fld \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> fld"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>f\<close> [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto>\<^sub>\<tau> S] = (if k < i then Var (i - 1) else Var i)"
| "(t \<bullet> u)[k \<mapsto>\<^sub>\<tau> S] = t[k \<mapsto>\<^sub>\<tau> S] \<bullet> u[k \<mapsto>\<^sub>\<tau> S]"
| "(t \<bullet>\<^sub>\<tau> T)[k \<mapsto>\<^sub>\<tau> S] = t[k \<mapsto>\<^sub>\<tau> S] \<bullet>\<^sub>\<tau> T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>"
| "(\<lambda>:T. t)[k \<mapsto>\<^sub>\<tau> S] = (\<lambda>:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. t[k+1 \<mapsto>\<^sub>\<tau> S])"
| "(\<lambda><:T. t)[k \<mapsto>\<^sub>\<tau> S] = (\<lambda><:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. t[k+1 \<mapsto>\<^sub>\<tau> S])"
| "(Rcd fs)[k \<mapsto>\<^sub>\<tau> S] = Rcd (fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r)"
| "(t..a)[k \<mapsto>\<^sub>\<tau> S] = (t[k \<mapsto>\<^sub>\<tau> S])..a"
| "(LET p = t IN u)[k \<mapsto>\<^sub>\<tau> S] =
     (LET p[k \<mapsto>\<^sub>\<tau> S]\<^sub>p = t[k \<mapsto>\<^sub>\<tau> S] IN u[k + \<parallel>p\<parallel>\<^sub>p \<mapsto>\<^sub>\<tau> S])"
| "[][k \<mapsto>\<^sub>\<tau> S]\<^sub>r = []"
| "(f \<Colon> fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>r = f[k \<mapsto>\<^sub>\<tau> S]\<^sub>f \<Colon> fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r"
| "(l, t)[k \<mapsto>\<^sub>\<tau> S]\<^sub>f = (l, t[k \<mapsto>\<^sub>\<tau> S])"

primrec liftE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env" (\<open>\<up>\<^sub>e\<close>)
where
  "\<up>\<^sub>e n k [] = []"
| "\<up>\<^sub>e n k (B \<Colon> \<Gamma>) = mapB (\<up>\<^sub>\<tau> n (k + \<parallel>\<Gamma>\<parallel>)) B \<Colon> \<up>\<^sub>e n k \<Gamma>"

primrec substE :: "env \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> env"  (\<open>_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>e\<close> [300, 0, 0] 300)
where
  "[][k \<mapsto>\<^sub>\<tau> T]\<^sub>e = []"
| "(B \<Colon> \<Gamma>)[k \<mapsto>\<^sub>\<tau> T]\<^sub>e = mapB (\<lambda>U. U[k + \<parallel>\<Gamma>\<parallel> \<mapsto>\<^sub>\<tau> T]\<^sub>\<tau>) B \<Colon> \<Gamma>[k \<mapsto>\<^sub>\<tau> T]\<^sub>e"

text \<open>
For the formalization of the reduction
rules for \<open>LET\<close>, we need a function \mbox{\<open>t[k \<mapsto>\<^sub>s us]\<close>}
for simultaneously substituting terms @{term us} for variables with
consecutive indices:
\<close>

primrec substs :: "trm \<Rightarrow> nat \<Rightarrow> trm list \<Rightarrow> trm"  (\<open>_[_ \<mapsto>\<^sub>s _]\<close> [300, 0, 0] 300)
where
  "t[k \<mapsto>\<^sub>s []] = t"
| "t[k \<mapsto>\<^sub>s u \<Colon> us] = t[k + \<parallel>us\<parallel> \<mapsto> u][k \<mapsto>\<^sub>s us]"

primrec decT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  (\<open>\<down>\<^sub>\<tau>\<close>)
where
  "\<down>\<^sub>\<tau> 0 k T = T"
| "\<down>\<^sub>\<tau> (Suc n) k T = \<down>\<^sub>\<tau> n k (T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>)"

primrec decE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env"  (\<open>\<down>\<^sub>e\<close>)
where
  "\<down>\<^sub>e 0 k \<Gamma> = \<Gamma>"
| "\<down>\<^sub>e (Suc n) k \<Gamma> = \<down>\<^sub>e n k (\<Gamma>[k \<mapsto>\<^sub>\<tau> Top]\<^sub>e)"

primrec decrT :: "nat \<Rightarrow> nat \<Rightarrow> rcdT \<Rightarrow> rcdT"  (\<open>\<down>\<^sub>r\<^sub>\<tau>\<close>)
where
  "\<down>\<^sub>r\<^sub>\<tau> 0 k fTs = fTs"
| "\<down>\<^sub>r\<^sub>\<tau> (Suc n) k fTs = \<down>\<^sub>r\<^sub>\<tau> n k (fTs[k \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>)"

text \<open>
The lemmas about substitution and lifting are very similar to those needed
for the simple calculus without records, with the difference that most
of them have to be proved simultaneously with a suitable property for
records.
\<close>

lemma liftE_length [simp]: "\<parallel>\<up>\<^sub>e n k \<Gamma>\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma substE_length [simp]: "\<parallel>\<Gamma>[k \<mapsto>\<^sub>\<tau> U]\<^sub>e\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma liftE_nth [simp]:
  "(\<up>\<^sub>e n k \<Gamma>)\<langle>i\<rangle> = map_option (mapB (\<up>\<^sub>\<tau> n (k + \<parallel>\<Gamma>\<parallel> - i - 1))) (\<Gamma>\<langle>i\<rangle>)"
  by (induct \<Gamma> arbitrary: i) (auto split: nat.splits)

lemma substE_nth [simp]:
  "(\<Gamma>[0 \<mapsto>\<^sub>\<tau> T]\<^sub>e)\<langle>i\<rangle> = map_option (mapB (\<lambda>U. U[\<parallel>\<Gamma>\<parallel> - i - 1 \<mapsto>\<^sub>\<tau> T]\<^sub>\<tau>)) (\<Gamma>\<langle>i\<rangle>)"
  by (induct \<Gamma> arbitrary: i) (auto split: nat.splits)

lemma liftT_liftT [simp]:
  "i \<le> j \<Longrightarrow> j \<le> i + m \<Longrightarrow> \<up>\<^sub>\<tau> n j (\<up>\<^sub>\<tau> m i T) = \<up>\<^sub>\<tau> (m + n) i T"
  "i \<le> j \<Longrightarrow> j \<le> i + m \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n j (\<up>\<^sub>r\<^sub>\<tau> m i rT) = \<up>\<^sub>r\<^sub>\<tau> (m + n) i rT"
  "i \<le> j \<Longrightarrow> j \<le> i + m \<Longrightarrow> \<up>\<^sub>f\<^sub>\<tau> n j (\<up>\<^sub>f\<^sub>\<tau> m i fT) = \<up>\<^sub>f\<^sub>\<tau> (m + n) i fT"
  by (induct T and rT and fT arbitrary: i j m n and i j m n and i j m n
    rule: liftT.induct liftrT.induct liftfT.induct) simp_all

lemma liftT_liftT' [simp]:
  "i + m \<le> j \<Longrightarrow> \<up>\<^sub>\<tau> n j (\<up>\<^sub>\<tau> m i T) = \<up>\<^sub>\<tau> m i (\<up>\<^sub>\<tau> n (j - m) T)"
  "i + m \<le> j \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n j (\<up>\<^sub>r\<^sub>\<tau> m i rT) = \<up>\<^sub>r\<^sub>\<tau> m i (\<up>\<^sub>r\<^sub>\<tau> n (j - m) rT)"
  "i + m \<le> j \<Longrightarrow> \<up>\<^sub>f\<^sub>\<tau> n j (\<up>\<^sub>f\<^sub>\<tau> m i fT) = \<up>\<^sub>f\<^sub>\<tau> m i (\<up>\<^sub>f\<^sub>\<tau> n (j - m) fT)"
proof (induct T and rT and fT arbitrary: i j m n and i j m n and i j m n
      rule: liftT.induct liftrT.induct liftfT.induct)
qed (auto simp: Suc_diff_le)

lemma lift_size [simp]:
  "size (\<up>\<^sub>\<tau> n k T) = size T"
  "size_list (size_prod (\<lambda>x. 0) size) (\<up>\<^sub>r\<^sub>\<tau> n k rT) = size_list (size_prod (\<lambda>x. 0) size) rT"
  "size_prod (\<lambda>x. 0) size (\<up>\<^sub>f\<^sub>\<tau> n k fT) = size_prod (\<lambda>x. 0) size fT"
  by (induct T and rT and fT arbitrary: k and k and k
    rule: liftT.induct liftrT.induct liftfT.induct) simp_all

lemma liftT0 [simp]:
  "\<up>\<^sub>\<tau> 0 i T = T"
  "\<up>\<^sub>r\<^sub>\<tau> 0 i rT = rT"
  "\<up>\<^sub>f\<^sub>\<tau> 0 i fT = fT"
  by (induct T and rT and fT arbitrary: i and i and i
    rule: liftT.induct liftrT.induct liftfT.induct) simp_all

lemma liftp0 [simp]:
  "\<up>\<^sub>p 0 i p = p"
  "\<up>\<^sub>r\<^sub>p 0 i fs = fs"
  "\<up>\<^sub>f\<^sub>p 0 i f = f"
  by (induct p and fs and f arbitrary: i and i and i
    rule: liftp.induct liftrp.induct liftfp.induct) simp_all

lemma lift0 [simp]:
  "\<up> 0 i t = t"
  "\<up>\<^sub>r 0 i fs = fs"
  "\<up>\<^sub>f 0 i f = f"
  by (induct t and fs and f arbitrary: i and i and i
    rule: lift.induct liftr.induct liftf.induct) simp_all

theorem substT_liftT [simp]:
  "k \<le> k' \<Longrightarrow> k' < k + n \<Longrightarrow> (\<up>\<^sub>\<tau> n k T)[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = \<up>\<^sub>\<tau> (n - 1) k T"
  "k \<le> k' \<Longrightarrow> k' < k + n \<Longrightarrow> (\<up>\<^sub>r\<^sub>\<tau> n k rT)[k' \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau> = \<up>\<^sub>r\<^sub>\<tau> (n - 1) k rT"
  "k \<le> k' \<Longrightarrow> k' < k + n \<Longrightarrow> (\<up>\<^sub>f\<^sub>\<tau> n k fT)[k' \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau> = \<up>\<^sub>f\<^sub>\<tau> (n - 1) k fT"
  by (induct T and rT and fT arbitrary: k k' and k k' and k k'
    rule: liftT.induct liftrT.induct liftfT.induct) simp_all

theorem liftT_substT [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>\<tau> n k (T[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) = \<up>\<^sub>\<tau> n k T[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n k (rT[k' \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>) = \<up>\<^sub>r\<^sub>\<tau> n k rT[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>"
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>f\<^sub>\<tau> n k (fT[k' \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau>) = \<up>\<^sub>f\<^sub>\<tau> n k fT[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau>"
  by (induct T and rT and fT arbitrary: k k' and k k' and k k'
    rule: liftT.induct liftrT.induct liftfT.induct) auto

theorem liftT_substT' [simp]:
  "k' < k \<Longrightarrow>
     \<up>\<^sub>\<tau> n k (T[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) = \<up>\<^sub>\<tau> n (k + 1) T[k' \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n (k - k') U]\<^sub>\<tau>"
  "k' < k \<Longrightarrow>
     \<up>\<^sub>r\<^sub>\<tau> n k (rT[k' \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>) = \<up>\<^sub>r\<^sub>\<tau> n (k + 1) rT[k' \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n (k - k') U]\<^sub>r\<^sub>\<tau>"
  "k' < k \<Longrightarrow>
     \<up>\<^sub>f\<^sub>\<tau> n k (fT[k' \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau>) = \<up>\<^sub>f\<^sub>\<tau> n (k + 1) fT[k' \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n (k - k') U]\<^sub>f\<^sub>\<tau>"
proof (induct T and rT and fT arbitrary: k k' and k k' and k k'
        rule: liftT.induct liftrT.induct liftfT.induct)
qed auto

lemma liftT_substT_Top [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>\<tau> n k' (T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>) = \<up>\<^sub>\<tau> n (Suc k') T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n k' (rT[k \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>) = \<up>\<^sub>r\<^sub>\<tau> n (Suc k') rT[k \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>"
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>f\<^sub>\<tau> n k' (fT[k \<mapsto>\<^sub>\<tau> Top]\<^sub>f\<^sub>\<tau>) = \<up>\<^sub>f\<^sub>\<tau> n (Suc k') fT[k \<mapsto>\<^sub>\<tau> Top]\<^sub>f\<^sub>\<tau>"
proof (induct T and rT and fT arbitrary: k k' and k k' and k k'
    rule: liftT.induct liftrT.induct liftfT.induct)
qed auto

theorem liftE_substE [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>e n k (\<Gamma>[k' \<mapsto>\<^sub>\<tau> U]\<^sub>e) = \<up>\<^sub>e n k \<Gamma>[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>e"
proof (induct \<Gamma>)
  case Nil
  then show ?case
    by auto
next
  case (Cons a \<Gamma>)
  then show ?case
    by (cases a) (simp_all add: ac_simps)
qed

lemma liftT_decT [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>\<tau> n k' (\<down>\<^sub>\<tau> m k T) = \<down>\<^sub>\<tau> m k (\<up>\<^sub>\<tau> n (m + k') T)"
  by (induct m arbitrary: T) simp_all

lemma liftT_substT_strange:
  "\<up>\<^sub>\<tau> n k T[n + k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = \<up>\<^sub>\<tau> n (Suc k) T[k \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n 0 U]\<^sub>\<tau>"
  "\<up>\<^sub>r\<^sub>\<tau> n k rT[n + k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau> = \<up>\<^sub>r\<^sub>\<tau> n (Suc k) rT[k \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n 0 U]\<^sub>r\<^sub>\<tau>"
  "\<up>\<^sub>f\<^sub>\<tau> n k fT[n + k \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau> = \<up>\<^sub>f\<^sub>\<tau> n (Suc k) fT[k \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n 0 U]\<^sub>f\<^sub>\<tau>"
proof (induct T and rT and fT arbitrary: n k and n k and n k
    rule: liftT.induct liftrT.induct liftfT.induct)
  case (TyAll x1 x2)
  then show ?case
    by (metis add.commute add_Suc liftT.simps(4) plus_1_eq_Suc substTT.simps(4))
qed auto

lemma liftp_liftp [simp]:
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>p n' k' (\<up>\<^sub>p n k p) = \<up>\<^sub>p (n + n') k p"
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>r\<^sub>p n' k' (\<up>\<^sub>r\<^sub>p n k rp) = \<up>\<^sub>r\<^sub>p (n + n') k rp"
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>f\<^sub>p n' k' (\<up>\<^sub>f\<^sub>p n k fp) = \<up>\<^sub>f\<^sub>p (n + n') k fp"
  by (induct p and rp and fp arbitrary: k k' and k k' and k k'
    rule: liftp.induct liftrp.induct liftfp.induct) simp_all

lemma liftp_psize[simp]:
  "\<parallel>\<up>\<^sub>p n k p\<parallel>\<^sub>p = \<parallel>p\<parallel>\<^sub>p"
  "\<parallel>\<up>\<^sub>r\<^sub>p n k fs\<parallel>\<^sub>r = \<parallel>fs\<parallel>\<^sub>r"
  "\<parallel>\<up>\<^sub>f\<^sub>p n k f\<parallel>\<^sub>f = \<parallel>f\<parallel>\<^sub>f"
  by (induct p and fs and f rule: liftp.induct liftrp.induct liftfp.induct) simp_all

lemma lift_lift [simp]:
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up> n' k' (\<up> n k t) = \<up> (n + n') k t"
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>r n' k' (\<up>\<^sub>r n k fs) = \<up>\<^sub>r (n + n') k fs"
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>f n' k' (\<up>\<^sub>f n k f) = \<up>\<^sub>f (n + n') k f"
 by (induct t and fs and f arbitrary: k k' and k k' and k k'
   rule: lift.induct liftr.induct liftf.induct) simp_all

lemma liftE_liftE [simp]:
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>e n' k' (\<up>\<^sub>e n k \<Gamma>) = \<up>\<^sub>e (n + n') k \<Gamma>"
proof (induct \<Gamma> arbitrary: k k')
  case Nil
  then show ?case by auto
next
  case (Cons a \<Gamma>)
  then show ?case
    by (cases a) auto
qed

lemma liftE_liftE' [simp]:
  "i + m \<le> j \<Longrightarrow> \<up>\<^sub>e n j (\<up>\<^sub>e m i \<Gamma>) = \<up>\<^sub>e m i (\<up>\<^sub>e n (j - m) \<Gamma>)"
proof (induct \<Gamma> arbitrary: i j m n)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Gamma>)
  then show ?case
    by (cases a) auto
qed

lemma substT_substT:
  "i \<le> j \<Longrightarrow>
     T[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>\<tau> = T[i \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>[j \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>"
  "i \<le> j \<Longrightarrow>
     rT[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>r\<^sub>\<tau>[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>r\<^sub>\<tau> = rT[i \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>[j \<mapsto>\<^sub>\<tau> V]\<^sub>r\<^sub>\<tau>"
  "i \<le> j \<Longrightarrow>
     fT[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>f\<^sub>\<tau>[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>f\<^sub>\<tau> = fT[i \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau>[j \<mapsto>\<^sub>\<tau> V]\<^sub>f\<^sub>\<tau>"
proof (induct T and rT and fT arbitrary: i j U V and i j U V and i j U V
    rule: liftT.induct liftrT.induct liftfT.induct)
  case (TyAll x1 x2)
  then show ?case
    by (metis Suc_eq_plus1 diff_Suc_Suc not_less_eq_eq substTT.simps(4))
qed auto

lemma substT_decT [simp]:
  "k \<le> j \<Longrightarrow> (\<down>\<^sub>\<tau> i k T)[j \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = \<down>\<^sub>\<tau> i k (T[i + j \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>)"
  by (induct i arbitrary: T j) (simp_all add: substT_substT [symmetric])

lemma substT_decT' [simp]:
  "i \<le> j \<Longrightarrow> \<down>\<^sub>\<tau> k (Suc j) T[i \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau> = \<down>\<^sub>\<tau> k j (T[i \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>)"
  by (induct k arbitrary: i j T) (simp_all add: substT_substT [of _ _ _ _ Top, simplified])

lemma substE_substE:
  "i \<le> j \<Longrightarrow> \<Gamma>[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>e[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>e = \<Gamma>[i \<mapsto>\<^sub>\<tau> U]\<^sub>e[j \<mapsto>\<^sub>\<tau> V]\<^sub>e"
proof (induct \<Gamma>)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Gamma>)
  then show ?case
    by (cases a) (simp_all add: substT_substT [symmetric])
qed

lemma substT_decE [simp]:
  "i \<le> j \<Longrightarrow> \<down>\<^sub>e k (Suc j) \<Gamma>[i \<mapsto>\<^sub>\<tau> Top]\<^sub>e = \<down>\<^sub>e k j (\<Gamma>[i \<mapsto>\<^sub>\<tau> Top]\<^sub>e)"
  by (induct k arbitrary: i j \<Gamma>) (simp_all add: substE_substE [of _ _ _ _ Top, simplified])

lemma liftE_app [simp]: "\<up>\<^sub>e n k (\<Gamma> @ \<Delta>) = \<up>\<^sub>e n (k + \<parallel>\<Delta>\<parallel>) \<Gamma> @ \<up>\<^sub>e n k \<Delta>"
  by (induct \<Gamma> arbitrary: k) (simp_all add: ac_simps)

lemma substE_app [simp]:
  "(\<Gamma> @ \<Delta>)[k \<mapsto>\<^sub>\<tau> T]\<^sub>e = \<Gamma>[k + \<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> T]\<^sub>e @ \<Delta>[k \<mapsto>\<^sub>\<tau> T]\<^sub>e"
  by (induct \<Gamma>) (simp_all add: ac_simps)

lemma substs_app [simp]: "t[k \<mapsto>\<^sub>s ts @ us] = t[k + \<parallel>us\<parallel> \<mapsto>\<^sub>s ts][k \<mapsto>\<^sub>s us]"
  by (induct ts arbitrary: t k) (simp_all add: ac_simps)

theorem decE_Nil [simp]: "\<down>\<^sub>e n k [] = []"
  by (induct n) simp_all

theorem decE_Cons [simp]:
  "\<down>\<^sub>e n k (B \<Colon> \<Gamma>) = mapB (\<down>\<^sub>\<tau> n (k + \<parallel>\<Gamma>\<parallel>)) B \<Colon> \<down>\<^sub>e n k \<Gamma>"
  by (induct n arbitrary: B \<Gamma>; case_tac B; force)

theorem decE_app [simp]:
  "\<down>\<^sub>e n k (\<Gamma> @ \<Delta>) = \<down>\<^sub>e n (k + \<parallel>\<Delta>\<parallel>) \<Gamma> @ \<down>\<^sub>e n k \<Delta>"
  by (induct n arbitrary: \<Gamma> \<Delta>) simp_all

theorem decT_liftT [simp]:
  "k \<le> k' \<Longrightarrow> k' + m \<le> k + n \<Longrightarrow> \<down>\<^sub>\<tau> m k' (\<up>\<^sub>\<tau> n k \<Gamma>) = \<up>\<^sub>\<tau> (n - m) k \<Gamma>"
  by (induct m arbitrary: n) auto

theorem decE_liftE [simp]:
  "k \<le> k' \<Longrightarrow> k' + m \<le> k + n \<Longrightarrow> \<down>\<^sub>e m k' (\<up>\<^sub>e n k \<Gamma>) = \<up>\<^sub>e (n - m) k \<Gamma>"
proof (induct \<Gamma> arbitrary: k k')
  case Nil
  then show ?case by auto
next
  case (Cons a \<Gamma>)
  then show ?case 
    by (cases a) auto
qed

theorem liftE0 [simp]: "\<up>\<^sub>e 0 k \<Gamma> = \<Gamma>"
proof (induct \<Gamma>)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Gamma>)
  then show ?case 
    by (cases a) auto
qed

lemma decT_decT [simp]: "\<down>\<^sub>\<tau> n k (\<down>\<^sub>\<tau> n' (k + n) T) = \<down>\<^sub>\<tau> (n + n') k T"
  by (induct n arbitrary: k T) simp_all

lemma decE_decE [simp]: "\<down>\<^sub>e n k (\<down>\<^sub>e n' (k + n) \<Gamma>) = \<down>\<^sub>e (n + n') k \<Gamma>"
  by (induct n arbitrary: k \<Gamma>) simp_all

lemma decE_length [simp]: "\<parallel>\<down>\<^sub>e n k \<Gamma>\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma liftrT_assoc_None [simp]: "(\<up>\<^sub>r\<^sub>\<tau> n k fs\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma liftrT_assoc_Some: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>T\<rfloor> \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n k fs\<langle>l\<rangle>\<^sub>? = \<lfloor>\<up>\<^sub>\<tau> n k T\<rfloor>"
  by (induct fs rule: list.induct) auto

lemma liftrp_assoc_None [simp]: "(\<up>\<^sub>r\<^sub>p n k fps\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fps\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fps rule: list.induct) auto

lemma liftr_assoc_None [simp]: "(\<up>\<^sub>r n k fs\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma unique_liftrT [simp]: "unique (\<up>\<^sub>r\<^sub>\<tau> n k fs) = unique fs"
  by (induct fs rule: list.induct) auto

lemma substrTT_assoc_None [simp]: "(fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>\<langle>a\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>a\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma substrTT_assoc_Some [simp]:
  "fs\<langle>a\<rangle>\<^sub>? = \<lfloor>T\<rfloor> \<Longrightarrow> fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>\<langle>a\<rangle>\<^sub>? = \<lfloor>T[k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>\<rfloor>"
  by (induct fs rule: list.induct) auto

lemma substrT_assoc_None [simp]: "(fs[k \<mapsto>\<^sub>\<tau> P]\<^sub>r\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma substrp_assoc_None [simp]: "(fps[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>p\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fps\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fps rule: list.induct) auto

lemma substr_assoc_None [simp]: "(fs[k \<mapsto> u]\<^sub>r\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma unique_substrT [simp]: "unique (fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>) = unique fs"
  by (induct fs rule: list.induct) auto

lemma liftrT_set: "(a, T) \<in> set fs \<Longrightarrow> (a, \<up>\<^sub>\<tau> n k T) \<in> set (\<up>\<^sub>r\<^sub>\<tau> n k fs)"
  by (induct fs rule: list.induct) auto

lemma liftrT_setD:
  "(a, T) \<in> set (\<up>\<^sub>r\<^sub>\<tau> n k fs) \<Longrightarrow> \<exists>T'. (a, T') \<in> set fs \<and> T = \<up>\<^sub>\<tau> n k T'"
  by (induct fs rule: list.induct) auto

lemma substrT_set: "(a, T) \<in> set fs \<Longrightarrow> (a, T[k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) \<in> set (fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>)"
  by (induct fs rule: list.induct) auto

lemma substrT_setD:
  "(a, T) \<in> set (fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>) \<Longrightarrow> \<exists>T'. (a, T') \<in> set fs \<and> T = T'[k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  by (induct fs rule: list.induct) auto


subsection \<open>Well-formedness\<close>

text \<open>
The definition of well-formedness is extended with a rule stating that a
record type @{term "RcdT fs"} is well-formed, if for all fields @{term "(l, T)"}
contained in the list @{term fs}, the type @{term T} is well-formed, and
all labels @{term l} in @{term fs} are {\it unique}.
\<close>

inductive
  well_formed :: "env \<Rightarrow> type \<Rightarrow> bool"  (\<open>_ \<turnstile>\<^sub>w\<^sub>f _\<close> [50, 50] 50)
where
  wf_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i"
| wf_Top: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f Top"
| wf_arrow: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<rightarrow> U"
| wf_all: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f (\<forall><:T. U)"
| wf_RcdT: "unique fs \<Longrightarrow> \<forall>(l, T)\<in>set fs. \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs"

inductive
  well_formedE :: "env \<Rightarrow> bool"  (\<open>_ \<turnstile>\<^sub>w\<^sub>f\<close> [50] 50)
  and well_formedB :: "env \<Rightarrow> binding \<Rightarrow> bool"  (\<open>_ \<turnstile>\<^sub>w\<^sub>f\<^sub>B _\<close> [50, 50] 50)
where
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<equiv> \<Gamma> \<turnstile>\<^sub>w\<^sub>f type_ofB B"
| wf_Nil: "[] \<turnstile>\<^sub>w\<^sub>f"
| wf_Cons: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"

inductive_cases well_formed_cases:
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f Top"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<rightarrow> U"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f (\<forall><:T. U)"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f (RcdT fTs)"

inductive_cases well_formedE_cases:
  "B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"

lemma wf_TVarB: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  by (rule wf_Cons) simp_all

lemma wf_VarB: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> VarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  by (rule wf_Cons) simp_all

lemma map_is_TVarb:
  "map is_TVarB \<Gamma>' = map is_TVarB \<Gamma> \<Longrightarrow>
    \<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<exists>T. \<Gamma>'\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor>"
proof (induct \<Gamma> arbitrary: \<Gamma>' T i)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Gamma>)
  then have "\<And>z . \<lbrakk>is_TVarB z\<rbrakk> \<Longrightarrow> \<exists>T. z = TVarB T"
    by (metis binding.exhaust is_TVarB.simps(1))
  with Cons show ?case by (auto split: nat.split_asm)
qed

lemma wf_equallength:
  assumes H: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
  shows "map is_TVarB \<Gamma>' = map is_TVarB \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>w\<^sub>f T" using H
proof (induct arbitrary: \<Gamma>')
  case (wf_TVar \<Gamma> i T)
  then show ?case
    using map_is_TVarb well_formed.wf_TVar by blast
next
  case (wf_RcdT fs \<Gamma>)
  then show ?case
    by (simp add: split_beta well_formed.wf_RcdT)
qed (fastforce intro: well_formed.intros)+

lemma wfE_replace:
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B' \<Longrightarrow> is_TVarB B' = is_TVarB B \<Longrightarrow>
     \<Delta> @ B' \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
proof (induct \<Delta>)
  case Nil
  then show ?case
    by (metis append_Nil well_formedE_cases wf_Cons)
next
  case (Cons a \<Delta>)
  have "a \<Colon> \<Delta> @ B' \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  proof (rule wf_Cons)
    have \<section>: "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f" "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B a"
      using Cons.prems(1) well_formedE_cases by auto
    with Cons.prems wf_equallength show "\<Delta> @ B' \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B a"
      by auto
    show "\<Delta> @ B' \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
      by (simp add: "\<section>" Cons)
  qed
  with Cons well_formedE_cases show ?case by auto
qed

lemma wf_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
  shows "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T"
  using H
proof (induct "\<Delta> @ \<Gamma>" T arbitrary: \<Delta>)
  case (wf_TVar i T)
  show ?case
  proof (cases "i < \<parallel>\<Delta>\<parallel>")
    case True
    with wf_TVar show ?thesis
      by (force intro: well_formed.wf_TVar)
  next
    case False
    then have "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)"
      using Suc_diff_le leI by blast
    with wf_TVar show ?thesis
      by (force intro: well_formed.wf_TVar)
  qed
next
  case (wf_RcdT fs)
  then show ?case
    by (fastforce dest: liftrT_setD intro: well_formed.wf_RcdT)
qed (fastforce intro: well_formed.intros)+

lemma wf_weaken': "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
proof (induct \<Delta>)
  case Nil
  then show ?case
    by simp
next
  case (Cons a \<Delta>)
  with wf_weaken [of "[]"]  show ?case
    by fastforce
qed

lemma wfE_weaken: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow> \<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
proof (induct \<Delta>)
  case Nil
  then show ?case
    by (simp add: wf_Cons)
next
  case (Cons a \<Delta>)
  show ?case
  proof (cases a)
    case (VarB x1)
    with Cons have "VarB (\<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> x1) \<Colon> \<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
      by (metis append_Cons type_ofB.simps(1) well_formedE_cases wf_Cons wf_weaken)
    with VarB show ?thesis 
      by simp
  next
    case (TVarB x2)
    with Cons have "TVarB (\<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> x2) \<Colon> \<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
      by (metis append_Cons type_ofB.simps(2) well_formedE_cases wf_Cons wf_weaken)
    with TVarB show ?thesis
      by simp
  qed
qed

lemma wf_liftB:
  assumes H: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  shows "\<Gamma>\<langle>i\<rangle> = \<lfloor>VarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc i) 0 T"
  using H
proof (induct arbitrary: i)
  case wf_Nil
  then show ?case
    by simp
next
  case (wf_Cons \<Gamma> B i)
  show ?case
  proof -
    have "VarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc 0) 0 T" if "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
      by (metis append_self_conv2 liftE.simps(1) list.size(3) wf_weaken that)
    moreover have "B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc (Suc k)) 0 T" if "\<Gamma>\<langle>k\<rangle> = \<lfloor>VarB T\<rfloor>" for k
      using that 
      by (metis One_nat_def Suc_eq_plus1 append_self_conv2 less_eq_nat.simps(1)
          liftE.simps(1) liftT_liftT(1) list.size(3) wf_Cons.hyps(3) wf_weaken)
    ultimately show ?thesis
      using wf_Cons by (auto split: nat.split_asm)
  qed
qed

theorem wf_subst:
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  "\<forall>(l, T) \<in> set (rT::rcdT). \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow>
     \<forall>(l, T) \<in> set rT. \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f snd (fT::fldT) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow>
     \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f snd fT[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
proof (induct T and rT and fT arbitrary: \<Delta> and \<Delta> and \<Delta>
    rule: liftT.induct liftrT.induct liftfT.induct)
  case (TVar i \<Delta>)
  show ?case
  proof (cases "i \<le> \<parallel>\<Delta>\<parallel>")
    case True
    with TVar.prems have "\<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 U"
      by (metis substE_length wf_weaken')
    with TVar True show ?thesis
      by (auto elim!: well_formed_cases simp add: wf_TVar split: nat.split_asm)
  next
    case False
    then have "\<parallel>\<Delta>\<parallel> \<le> i - 1"
      by simp
    with TVar False show ?thesis
      by (auto elim!: well_formed_cases simp: wf_TVar split: nat_diff_split_asm nat.split_asm)
  qed
next
  case Top
  then show ?case
    by (simp add: wf_Top)
next
  case (Fun x1 x2)
  then show ?case
    by (metis substTT.simps(3) well_formed_cases(3) wf_arrow)
next
  case (TyAll type1 type2 \<Delta>)
  then have "(TVarB type1 \<Colon> \<Delta>)[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f type2[\<parallel>TVarB type1 \<Colon> \<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
    by (metis append_Cons well_formed_cases(4))
  with TyAll show ?case
    using wf_all by (force simp: elim!: well_formed_cases)
next
  case (RcdT x)
  then show ?case
    by (force simp: intro!: wf_RcdT dest: substrT_setD elim: well_formed_cases)
qed (auto simp: split_beta)

theorem wf_dec: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
proof (induct \<Delta> arbitrary: T)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Delta>)
  with wf_subst(1) [of "[]"] wf_Top show ?case
    by force
qed

theorem wfE_subst: "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
proof (induct \<Delta>)
  case Nil
  then show ?case
    using well_formedE_cases by auto
next
  case (Cons a \<Delta>)
  show ?case
  proof (cases a)
    case (VarB x)
    with Cons have "VarB (x[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) \<Colon> \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
      by (metis append_Cons type_ofB.simps(1) well_formedE_cases wf_VarB wf_subst(1))
    then show ?thesis
      using VarB by force
  next
    case (TVarB x)
    with Cons have "TVarB (x[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) \<Colon> \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
      by (metis append_Cons type_ofB.simps(2) well_formedE_cases wf_TVarB wf_subst(1))
    with TVarB show ?thesis
      by simp
  qed
qed
 
subsection \<open>Subtyping\<close>

text \<open>
The definition of the subtyping judgement is extended with a rule \<open>SA_Rcd\<close> stating
that a record type @{term "RcdT fs"} is a subtype of @{term "RcdT fs'"}, if
for all fields \mbox{@{term "(l, T)"}} contained in @{term fs'}, there exists a
corresponding field @{term "(l, S)"} such that @{term S} is a subtype of @{term T}.
If the list @{term fs'} is empty, \<open>SA_Rcd\<close> can appear as a leaf in
the derivation tree of the subtyping judgement. Therefore, the introduction
rule needs an additional premise @{term "\<Gamma> \<turnstile>\<^sub>w\<^sub>f"} to make sure that only
subtyping judgements with well-formed contexts are derivable. Moreover,
since @{term fs} can contain additional fields not present in @{term fs'},
we also have to require that the type @{term "RcdT fs"} is well-formed.
In order to ensure that the type @{term "RcdT fs'"} is well-formed, too,
we only have to require that labels in @{term fs'} are unique, since,
by induction on the subtyping derivation, all types contained in @{term fs'}
are already well-formed.
\<close>

inductive
  subtyping :: "env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool"  (\<open>_ /\<turnstile> _ <: _\<close> [50, 50, 50] 50)
where
  SA_Top: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f S \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_refl_TVar: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: TVar i"
| SA_trans_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB U\<rfloor> \<Longrightarrow>
    \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc i) 0 U <: T \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: T"
| SA_arrow: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_all: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow>
    \<Gamma> \<turnstile> (\<forall><:S\<^sub>1. S\<^sub>2) <: (\<forall><:T\<^sub>1. T\<^sub>2)"
| SA_Rcd: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs \<Longrightarrow> unique fs' \<Longrightarrow>
    \<forall>(l, T)\<in>set fs'. \<exists>S. (l, S)\<in>set fs \<and> \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> RcdT fs <: RcdT fs'"

lemma wf_subtype_env:
  assumes PQ: "\<Gamma> \<turnstile> P <: Q"
  shows "\<Gamma> \<turnstile>\<^sub>w\<^sub>f" using PQ
  by induct assumption+

lemma wf_subtype:
  assumes PQ: "\<Gamma> \<turnstile> P <: Q"
  shows "\<Gamma> \<turnstile>\<^sub>w\<^sub>f P \<and> \<Gamma> \<turnstile>\<^sub>w\<^sub>f Q" using PQ
  by induct (auto intro: well_formed.intros elim!: wf_equallength)

lemma wf_subtypeE:
  assumes H: "\<Gamma> \<turnstile> T <: U"
  and H': "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> P"
  shows "P"
  using H H' wf_subtype wf_subtype_env by force

lemma subtype_refl: \<comment> \<open>A.1\<close>
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile> T <: T"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<forall>(l::name, T)\<in>set fTs. \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<longrightarrow> \<Gamma> \<turnstile> T <: T"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f snd (fT::fldT) \<Longrightarrow> \<Gamma> \<turnstile> snd fT <: snd fT"
  by (induct T and fTs and fT arbitrary: \<Gamma> and \<Gamma> and \<Gamma>
    rule: liftT.induct liftrT.induct liftfT.induct,
    simp_all add: split_paired_all, simp_all)
    (blast intro: subtyping.intros wf_Nil wf_TVarB elim: well_formed_cases)+

lemma subtype_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile> P <: Q"
  and wf: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B"
  shows "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> P <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> Q" using H
proof (induct "\<Delta> @ \<Gamma>" P Q arbitrary: \<Delta>)
  case SA_Top
  with wf show ?case
    by (auto intro: subtyping.SA_Top wfE_weaken wf_weaken)
next
  case SA_refl_TVar
  with wf show ?case
    by (auto intro!: subtyping.SA_refl_TVar wfE_weaken dest: wf_weaken)
next
  case (SA_trans_TVar i U T)
  thus ?case
  proof (cases "i < \<parallel>\<Delta>\<parallel>")
    case True
    with SA_trans_TVar
    have "(\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma>)\<langle>i\<rangle> = \<lfloor>TVarB (\<up>\<^sub>\<tau> 1 (\<parallel>\<Delta>\<parallel> - Suc i) U)\<rfloor>"
      by simp
    moreover from True SA_trans_TVar
    have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>
      \<up>\<^sub>\<tau> (Suc i) 0 (\<up>\<^sub>\<tau> 1 (\<parallel>\<Delta>\<parallel> - Suc i) U) <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by simp
    ultimately have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> TVar i <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by (rule subtyping.SA_trans_TVar)
    with True show ?thesis by simp
  next
    case False
    then have "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)" by arith
    with False SA_trans_TVar have "(\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma>)\<langle>Suc i\<rangle> = \<lfloor>TVarB U\<rfloor>"
      by simp
    moreover from False SA_trans_TVar
    have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc (Suc i)) 0 U <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by simp
    ultimately have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> TVar (Suc i) <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by (rule subtyping.SA_trans_TVar)
    with False show ?thesis by simp
  qed
next
  case SA_arrow
  thus ?case by simp (iprover intro: subtyping.SA_arrow)
next
  case (SA_all T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
  with SA_all(4) [of "TVarB T\<^sub>1 \<Colon> \<Delta>"]
  show ?case by simp (iprover intro: subtyping.SA_all)
next
  case (SA_Rcd fs fs')
  with wf have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f" by simp (rule wfE_weaken)
  moreover from \<open>\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs\<close>
  have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> (RcdT fs)"
    by (rule wf_weaken)
  hence "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs)" by simp
  moreover from SA_Rcd have "unique (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs')" by simp
  moreover have "\<forall>(l, T)\<in>set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs').
    \<exists>S. (l, S)\<in>set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs) \<and> \<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> S <: T"
  proof (rule ballpI)
    fix l T
    assume "(l, T) \<in> set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs')"
    then obtain T' where "(l, T') \<in> set fs'" and T: "T = \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T'"
      by (blast dest: liftrT_setD)
    with SA_Rcd obtain S where
      lS: "(l, S) \<in> set fs"
      and ST: "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> S <: \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> (T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>)"
      by fastforce
    with T have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> S <: \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T'"
      by simp
    moreover from lS have "(l, \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> S) \<in> set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs)"
      by (rule liftrT_set)
    moreover note T
    ultimately show "\<exists>S. (l, S)\<in>set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs) \<and> \<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> S <: T"
      by auto
  qed
  ultimately have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> RcdT (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs) <: RcdT (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs')"
    by (rule subtyping.SA_Rcd)
  thus ?case by simp
qed

lemma subtype_weaken': \<comment> \<open>A.2\<close>
  "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 P <: \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 Q"
proof (induct \<Delta>)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a \<Delta>)
  then have "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B a" "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
    using well_formedE_cases by auto
  with Cons show ?case
    using subtype_weaken [where B="a" and \<Gamma>="\<Delta> @ \<Gamma>"]
    by (metis Suc_eq_plus1 append_Cons append_Nil bot_nat_0.extremum length_Cons
        liftE.simps(1) liftT_liftT(1) list.size(3))
qed

lemma fieldT_size [simp]:
  "(a, T) \<in> set fs \<Longrightarrow> size T < Suc (size_list (size_prod (\<lambda>x. 0) size) fs)"
  by (induct fs arbitrary: a T rule: list.induct) fastforce+

lemma subtype_trans: \<comment> \<open>A.3\<close>
  "\<Gamma> \<turnstile> S <: Q \<Longrightarrow> \<Gamma> \<turnstile> Q <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> M <: N \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
     \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> M <: N"
  using wf_measure_size
proof (induct Q arbitrary: \<Gamma> S T \<Delta> P M N rule: wf_induct_rule)
  case (less Q)
  {
    fix \<Gamma> S T Q'
    assume "\<Gamma> \<turnstile> S <: Q'"
    then have "\<Gamma> \<turnstile> Q' <: T \<Longrightarrow> size Q = size Q' \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
    proof (induct arbitrary: T)
      case SA_Top
      from SA_Top(3) show ?case
        by cases (auto intro: subtyping.SA_Top SA_Top)
    next
      case SA_refl_TVar show ?case by fact
    next
      case SA_trans_TVar
      thus ?case by (auto intro: subtyping.SA_trans_TVar)
    next
      case (SA_arrow \<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
      note SA_arrow' = SA_arrow
      from SA_arrow(5) show ?case
      proof cases
        case SA_Top
        with SA_arrow show ?thesis
          by (auto intro: subtyping.SA_Top wf_arrow elim: wf_subtypeE)
      next
        case (SA_arrow T\<^sub>1' T\<^sub>2')
        from SA_arrow SA_arrow' have "\<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1' \<rightarrow> T\<^sub>2'"
          by (auto intro!: subtyping.SA_arrow intro: less(1) [of "T\<^sub>1"] less(1) [of "T\<^sub>2"])
        with SA_arrow show ?thesis by simp
      qed
    next
      case (SA_all \<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
      note SA_all' = SA_all
      from SA_all(5) show ?case
      proof cases
        case SA_Top
        with SA_all show ?thesis by (auto intro!:
          subtyping.SA_Top wf_all intro: wf_equallength elim: wf_subtypeE)
      next
        case (SA_all T\<^sub>1' T\<^sub>2')
        from SA_all SA_all' have "\<Gamma> \<turnstile> T\<^sub>1' <: S\<^sub>1"
          by - (rule less(1), simp_all)
        moreover from SA_all SA_all' have "TVarB T\<^sub>1' \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2"
          by - (rule less(2) [of _ "[]", simplified], simp_all)
        with SA_all SA_all' have "TVarB T\<^sub>1' \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2'"
          by - (rule less(1), simp_all)
        ultimately have "\<Gamma> \<turnstile> (\<forall><:S\<^sub>1. S\<^sub>2) <: (\<forall><:T\<^sub>1'. T\<^sub>2')"
          by (rule subtyping.SA_all)
        with SA_all show ?thesis by simp
      qed
    next
      case (SA_Rcd \<Gamma> fs\<^sub>1 fs\<^sub>2)
      note SA_Rcd' = SA_Rcd
      from SA_Rcd(5) show ?case
      proof cases
        case SA_Top
        with SA_Rcd show ?thesis by (auto intro!: subtyping.SA_Top)
      next
        case (SA_Rcd fs\<^sub>2')
        note \<open>\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<close>
        moreover note \<open>\<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs\<^sub>1\<close>
        moreover note \<open>unique fs\<^sub>2'\<close>
        moreover have "\<forall>(l, T)\<in>set fs\<^sub>2'. \<exists>S. (l, S)\<in>set fs\<^sub>1 \<and> \<Gamma> \<turnstile> S <: T"
        proof (rule ballpI)
          fix l T
          assume lT: "(l, T) \<in> set fs\<^sub>2'"
          with SA_Rcd obtain U where
            fs2: "(l, U) \<in> set fs\<^sub>2" and UT: "\<Gamma> \<turnstile> U <: T" by blast
          with SA_Rcd SA_Rcd' obtain S where
            fs1: "(l, S) \<in> set fs\<^sub>1" and SU: "\<Gamma> \<turnstile> S <: U" by blast
          from SA_Rcd SA_Rcd' fs2 have "(U, Q) \<in> measure size" by simp
          hence "\<Gamma> \<turnstile> S <: T" using SU UT by (rule less(1))
          with fs1 show "\<exists>S. (l, S)\<in>set fs\<^sub>1 \<and> \<Gamma> \<turnstile> S <: T" by blast
        qed
        ultimately have "\<Gamma> \<turnstile> RcdT fs\<^sub>1 <: RcdT fs\<^sub>2'" by (rule subtyping.SA_Rcd)
        with SA_Rcd show ?thesis by simp
      qed
    qed
  }
  note tr = this
  {
    case 1
    thus ?case using refl by (rule tr)
  next
    case 2
    from 2(1) show "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> M <: N"
    proof (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" M N arbitrary: \<Delta>)
      case SA_Top
      with 2 show ?case by (auto intro!: subtyping.SA_Top
        intro: wf_equallength wfE_replace elim!: wf_subtypeE)
    next
      case SA_refl_TVar
      with 2 show ?case by (auto intro!: subtyping.SA_refl_TVar
        intro: wf_equallength wfE_replace elim!: wf_subtypeE)
    next
      case (SA_trans_TVar i U T)
      show ?case
      proof (cases "i < \<parallel>\<Delta>\<parallel>")
        case True
        with SA_trans_TVar show ?thesis
          by (auto intro!: subtyping.SA_trans_TVar)
      next
        case False
        note False' = False
        show ?thesis
        proof (cases "i = \<parallel>\<Delta>\<parallel>")
          case True
          from SA_trans_TVar have "(\<Delta> @ [TVarB P]) @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
            by (auto intro: wfE_replace elim!: wf_subtypeE)
          with \<open>\<Gamma> \<turnstile> P <: Q\<close>
          have "(\<Delta> @ [TVarB P]) @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta> @ [TVarB P]\<parallel> 0 P <: \<up>\<^sub>\<tau> \<parallel>\<Delta> @ [TVarB P]\<parallel> 0 Q"
            by (rule subtype_weaken')
          with SA_trans_TVar True False have "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc \<parallel>\<Delta>\<parallel>) 0 P <: T"
            by - (rule tr, simp+)
          with True and False and SA_trans_TVar show ?thesis
            by (auto intro!: subtyping.SA_trans_TVar)
        next
          case False
          with False' have "i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel> - 1)" by arith
          with False False' SA_trans_TVar show ?thesis
            by - (rule subtyping.SA_trans_TVar, simp+)
        qed
      qed
    next
      case SA_arrow
      thus ?case by (auto intro!: subtyping.SA_arrow)
    next
      case (SA_all T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
      thus ?case by (auto intro: subtyping.SA_all
        SA_all(4) [of "TVarB T\<^sub>1 \<Colon> \<Delta>", simplified])
    next
      case (SA_Rcd fs fs')
      from \<open>\<Gamma> \<turnstile> P <: Q\<close> have "\<Gamma> \<turnstile>\<^sub>w\<^sub>f P" by (rule wf_subtypeE)
      with SA_Rcd have "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
        by - (rule wfE_replace, simp+)
      moreover from SA_Rcd have "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs" by simp
      hence "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs" by (rule wf_equallength) simp_all
      moreover note \<open>unique fs'\<close>
      moreover from SA_Rcd
      have "\<forall>(l, T)\<in>set fs'. \<exists>S. (l, S)\<in>set fs \<and> \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> S <: T"
        by blast
      ultimately show ?case by (rule subtyping.SA_Rcd)
    qed
  }
qed

lemma substT_subtype: \<comment> \<open>A.10\<close>
  assumes H: "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> S <: T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau> <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
  using H
proof (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" S T arbitrary: \<Delta>)
  case (SA_Top S)
  then show ?case
    by (simp add: subtyping.SA_Top wfE_subst wf_subst(1) wf_subtype)
next
  case (SA_refl_TVar i)
  then show ?case
    by (meson subtype_refl(1) wfE_subst wf_subst(1) wf_subtypeE)
next
  case (SA_trans_TVar i U T \<Delta>)
  have "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 P <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
    if "i = \<parallel>\<Delta>\<parallel>"
  proof -
    have "\<lbrakk>\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 U <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>; 
     \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e\<parallel> 0 P <: \<up>\<^sub>\<tau> \<parallel>\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e\<parallel> 0 U\<rbrakk>
    \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 P <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
      by (metis substE_length subtype_trans(1))
    then show ?thesis
      using SA_trans_TVar that wf_subtype_env
      by (fastforce dest: subtype_weaken' [where \<Gamma>=\<Gamma> and \<Delta>="\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e"])
  qed
  moreover have "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> TVar (i - Suc 0) <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
    if "\<parallel>\<Delta>\<parallel> < i"
  proof (intro subtyping.SA_trans_TVar)
    show "(\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma>)\<langle>i - Suc 0\<rangle> = \<lfloor>TVarB U\<rfloor>"
      using SA_trans_TVar that
      by (auto split: nat.split_asm nat_diff_split)
  next
    show "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc (i - Suc 0)) 0 U <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
      using SA_trans_TVar that by fastforce
  qed
  moreover have "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> TVar i <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
    if "\<parallel>\<Delta>\<parallel> > i"
  proof (intro subtyping.SA_trans_TVar)
    show "(\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma>)\<langle>i\<rangle> = \<lfloor>TVarB (U[\<parallel>\<Delta>\<parallel> - Suc i \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>)\<rfloor>"
      using that SA_trans_TVar by (simp split: nat.split_asm nat_diff_split)
  next
    show "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc i) 0 (U[\<parallel>\<Delta>\<parallel> - Suc i \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>) <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
      using SA_trans_TVar 
      by (metis Suc_leI zero_le le_add_diff_inverse2 liftT_substT(1) that)
  qed
  ultimately show ?case
    by auto
next
  case (SA_arrow T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
  then show ?case
    by (simp add: subtyping.SA_arrow)
next
  case (SA_all T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
  then show ?case
    by (simp add: subtyping.SA_all)
next
  case (SA_Rcd fs fs')
  have "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
    using SA_Rcd wfE_subst by (meson wf_subtypeE)
  moreover have "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT (fs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>r\<^sub>\<tau>)"
    using SA_Rcd.hyps(2) SA_Rcd.prems wf_subst(1) wf_subtype by fastforce
  moreover have "unique (fs'[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>r\<^sub>\<tau>)"
    using SA_Rcd.hyps(3) by auto
  moreover have "\<forall>(l, T) \<in> set (fs'[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>r\<^sub>\<tau>). \<exists>S. (l, S) \<in> set (fs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>r\<^sub>\<tau>) \<and> \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> S <: T"
    using SA_Rcd by (smt (verit) ballpI case_prodD substrT_set substrT_setD)
  ultimately show ?case
    by (simp add: subtyping.SA_Rcd)
qed

lemma subst_subtype:
  assumes H: "\<Delta> @ VarB V \<Colon> \<Gamma> \<turnstile> T <: U"
  shows "\<down>\<^sub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T <: \<down>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> U"
  using H
proof (induct "\<Delta> @ VarB V \<Colon> \<Gamma>" T U arbitrary: \<Delta>)
  case (SA_Top S)
  then show ?case
    by (simp add: subtyping.SA_Top wfE_subst wf_Top wf_subst(1))
next
  case (SA_refl_TVar i)
  then show ?case
    by (metis One_nat_def decE.simps decT.simps subtype_refl(1) wfE_subst
        wf_Top wf_subst(1))
next
  case (SA_trans_TVar i U T)
  then have *: "\<parallel>\<Delta>\<parallel> > i
    \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma> 
        \<turnstile> \<up>\<^sub>\<tau> (Suc i) 0 (U[\<parallel>\<Delta>\<parallel> - Suc i \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>) <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
    by (metis One_nat_def Suc_leI bot_nat_0.extremum decE.simps(1,2) decT.simps(1,2)
        le_add_diff_inverse2 liftT_substT(1))
  show ?case
    using SA_trans_TVar
    by (auto simp add: * split: nat_diff_split intro!: subtyping.SA_trans_TVar)
next
  case (SA_arrow T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
  then show ?case
    by (simp add: subtyping.SA_arrow)
next
  case (SA_all T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
  then show ?case
    by (simp add: subtyping.SA_all)
next
  case (SA_Rcd fs fs')
  have "\<Delta>[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
    using SA_Rcd.hyps(1) wfE_subst wf_Top by auto
  moreover have "\<Delta>[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT (fs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>)"
    using SA_Rcd.hyps(2) wf_Top wf_subst(1) by fastforce
  moreover have "unique (fs'[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>)"
    by (simp add: SA_Rcd.hyps)
  moreover have "\<forall>(l, T) \<in>set (fs'[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>). \<exists>S. (l, S) \<in> set (fs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>) \<and> \<Delta>[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma> \<turnstile> S <: T"
    using SA_Rcd
    by (smt (verit) One_nat_def ballpI case_prodD decE.simps(1,2) decT.simps(1,2)
        substrT_set substrT_setD)
  ultimately show ?case
    by (simp add: subtyping.SA_Rcd)
qed


subsection \<open>Typing\<close>

text \<open>
In the formalization of the type checking rule for the \<open>LET\<close> binder,
we use an additional judgement \<open>\<turnstile> p : T \<Rightarrow> \<Delta>\<close> for checking whether a
given pattern @{term p} is compatible with the type @{term T} of an object that
is to be matched against this pattern. The judgement will be defined simultaneously
with a judgement \mbox{\<open>\<turnstile> ps [:] Ts \<Rightarrow> \<Delta>\<close>} for type checking field patterns.
Apart from checking the type, the judgement also returns a list of bindings @{term \<Delta>},
which can be thought of as a ``flattened'' list of types of the variables occurring
in the pattern. Since typing environments are extended ``to the left'', the bindings
in @{term \<Delta>} appear in reverse order.
\<close>

inductive
  ptyping :: "pat \<Rightarrow> type \<Rightarrow> env \<Rightarrow> bool"  (\<open>\<turnstile> _ : _ \<Rightarrow> _\<close> [50, 50, 50] 50)
  and ptypings :: "rpat \<Rightarrow> rcdT \<Rightarrow> env \<Rightarrow> bool"  (\<open>\<turnstile> _ [:] _ \<Rightarrow> _\<close> [50, 50, 50] 50)
where
  P_Var: "\<turnstile> PVar T : T \<Rightarrow> [VarB T]"
| P_Rcd: "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> PRcd fps : RcdT fTs \<Rightarrow> \<Delta>"
| P_Nil: "\<turnstile> [] [:] [] \<Rightarrow> []"
| P_Cons: "\<turnstile> p : T \<Rightarrow> \<Delta>\<^sub>1 \<Longrightarrow> \<turnstile> fps [:] fTs \<Rightarrow> \<Delta>\<^sub>2 \<Longrightarrow> fps\<langle>l\<rangle>\<^sub>? = \<bottom> \<Longrightarrow>
    \<turnstile> ((l, p) \<Colon> fps) [:] ((l, T) \<Colon> fTs) \<Rightarrow> \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2 @ \<Delta>\<^sub>1"

text \<open>
The definition of the typing judgement for terms is extended with the rules \<open>T_Let\<close>,
@{term "T_Rcd"}, and @{term "T_Proj"} for pattern matching, record construction and
field selection, respectively. The above typing judgement for patterns is used in
the rule \<open>T_Let\<close>. The typing judgement for terms is defined simultaneously
with a typing judgement \<open>\<Gamma> \<turnstile> fs [:] fTs\<close> for record fields.
\<close>

inductive
  typing :: "env \<Rightarrow> trm \<Rightarrow> type \<Rightarrow> bool"  (\<open>_ \<turnstile> _ : _\<close> [50, 50, 50] 50)
  and typings :: "env \<Rightarrow> rcd \<Rightarrow> rcdT \<Rightarrow> bool"  (\<open>_ \<turnstile> _ [:] _\<close> [50, 50, 50] 50)
where
  T_Var: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma>\<langle>i\<rangle> = \<lfloor>VarB U\<rfloor> \<Longrightarrow> T = \<up>\<^sub>\<tau> (Suc i) 0 U \<Longrightarrow> \<Gamma> \<turnstile> Var i : T"
| T_Abs: "VarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda>:T\<^sub>1. t\<^sub>2) : T\<^sub>1 \<rightarrow> \<down>\<^sub>\<tau> 1 0 T\<^sub>2"
| T_App: "\<Gamma> \<turnstile> t\<^sub>1 : T\<^sub>1\<^sub>1 \<rightarrow> T\<^sub>1\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>1 \<bullet> t\<^sub>2 : T\<^sub>1\<^sub>2"
| T_TAbs: "TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda><:T\<^sub>1. t\<^sub>2) : (\<forall><:T\<^sub>1. T\<^sub>2)"
| T_TApp: "\<Gamma> \<turnstile> t\<^sub>1 : (\<forall><:T\<^sub>1\<^sub>1. T\<^sub>1\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>1\<^sub>1 \<Longrightarrow>
    \<Gamma> \<turnstile> t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 : T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>"
| T_Sub: "\<Gamma> \<turnstile> t : S \<Longrightarrow> \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> t : T"
| T_Let: "\<Gamma> \<turnstile> t\<^sub>1 : T\<^sub>1 \<Longrightarrow> \<turnstile> p : T\<^sub>1 \<Rightarrow> \<Delta> \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow>
    \<Gamma> \<turnstile> (LET p = t\<^sub>1 IN t\<^sub>2) : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T\<^sub>2"
| T_Rcd: "\<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile> Rcd fs : RcdT fTs"
| T_Proj: "\<Gamma> \<turnstile> t : RcdT fTs \<Longrightarrow> fTs\<langle>l\<rangle>\<^sub>? = \<lfloor>T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile> t..l : T"
| T_Nil: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile> [] [:] []"
| T_Cons: "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> fs\<langle>l\<rangle>\<^sub>? = \<bottom> \<Longrightarrow>
    \<Gamma> \<turnstile> (l, t) \<Colon> fs [:] (l, T) \<Colon> fTs"

theorem wf_typeE1:
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  "\<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  by (induct set: typing typings) (blast elim: well_formedE_cases)+

theorem wf_typeE2:
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
  "\<Gamma>' \<turnstile> fs [:] fTs \<Longrightarrow> (\<forall>(l, T) \<in> set fTs. \<Gamma>' \<turnstile>\<^sub>w\<^sub>f T) \<and>
     unique fTs \<and> (\<forall>l. (fs\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fTs\<langle>l\<rangle>\<^sub>? = \<bottom>))"
proof (induct set: typing typings)
  case (T_Abs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  have "\<parallel>[]\<parallel> = 0" and "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T\<^sub>1"
    using T_Abs.hyps(1) well_formedE_cases wf_typeE1(1) by fastforce+
  then show ?case
    by (metis One_nat_def T_Abs.hyps(2) append_Cons append_Nil length_Cons wf_arrow wf_dec)
next
  case (T_App \<Gamma> t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 t\<^sub>2)
  then show ?case
    using well_formed_cases(3) by blast
next
  case (T_TAbs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  then show ?case
    by (metis type_ofB.simps(2) well_formedE_cases wf_all wf_typeE1(1))
next
  case (T_TApp \<Gamma> t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2)
  then show ?case
    by (metis append_Nil length_0_conv substE_length well_formed_cases(4)
        wf_subst(1) wf_subtype)
next
  case (T_Proj \<Gamma> t fTs l T)
  then show ?case
    by (metis assoc_set snd_eqD split_beta well_formed_cases(5))
qed (auto simp: wf_subtype wf_dec wf_RcdT wf_liftB)

lemmas ptyping_induct = ptyping_ptypings.inducts(1)
  [of _ _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names P_Var P_Rcd]

lemmas ptypings_induct = ptyping_ptypings.inducts(2)
  [of _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names P_Nil P_Cons]

lemmas typing_induct = typing_typings.inducts(1)
  [of _ _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names T_Var T_Abs T_App T_TAbs T_TApp T_Sub T_Let T_Rcd T_Proj]

lemmas typings_induct = typing_typings.inducts(2)
  [of _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names T_Nil T_Cons]

lemma narrow_type: \<comment> \<open>A.7\<close>
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> t : T \<Longrightarrow>
     \<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> t : T"
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> ts [:] Ts \<Longrightarrow>
     \<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> ts [:] Ts"
proof (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" t T and "\<Delta> @ TVarB Q \<Colon> \<Gamma>" ts Ts
      arbitrary: \<Delta> and \<Delta> set: typing typings)
  case (T_Var i U T)
  show ?case 
  proof (intro typing_typings.T_Var)
    show "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
      using T_Var by (elim wfE_replace wf_subtypeE; simp)
    show "(\<Delta> @ TVarB P \<Colon> \<Gamma>)\<langle>i\<rangle> = \<lfloor>VarB U\<rfloor>"
      using T_Var by (cases "i < \<parallel>\<Delta>\<parallel>") (auto split: nat.splits)
  next
    show "T = \<up>\<^sub>\<tau> (Suc i) 0 U"
      using T_Var.hyps(3) by blast
  qed
next
  case (T_Abs T\<^sub>1 t\<^sub>2 T\<^sub>2)
  then show ?case
    using typing_typings.T_Abs by force
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2)
  then show ?case
    using subtype_trans(2) typing_typings.T_TApp by blast
next
  case (T_Sub t S T)
  then show ?case
    using subtype_trans(2) typing_typings.T_Sub by blast
next
  case T_Nil
  then show ?case
    by (metis is_TVarB.simps(2) type_ofB.simps(2) typing_typings.T_Nil wfE_replace
        wf_subtypeE)
qed (auto simp: typing_typings.intros)

lemma typings_setD:
  assumes H: "\<Gamma> \<turnstile> fs [:] fTs"
  shows "(l, T) \<in> set fTs \<Longrightarrow> \<exists>t. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>t\<rfloor> \<and> \<Gamma> \<turnstile> t : T"
  using H
  by (induct arbitrary: l T rule: typings_induct) fastforce+

lemma subtype_refl':
  assumes t: "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> T <: T"
  using subtype_refl(1) t wf_typeE1(1) wf_typeE2(1) by force

lemma Abs_type: \<comment> \<open>A.13(1)\<close>
  assumes H: "\<Gamma> \<turnstile> (\<lambda>:S. s) : T"
  shows "\<Gamma> \<turnstile> T <: U \<rightarrow> U' \<Longrightarrow>
    (\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> VarB S \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
      \<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 0 S' <: U' \<Longrightarrow> P) \<Longrightarrow> P"
  using H
proof (induct \<Gamma> "\<lambda>:S. s" T arbitrary: U U' S s P)
  case (T_Abs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>\<Gamma> \<turnstile> T\<^sub>1 \<rightarrow> \<down>\<^sub>\<tau> 1 0 T\<^sub>2 <: U \<rightarrow> U'\<close>
  obtain ty1: "\<Gamma> \<turnstile> U <: T\<^sub>1" and ty2: "\<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 0 T\<^sub>2 <: U'"
    by cases simp_all
  from ty1 \<open>VarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close> ty2
  show ?case by (rule T_Abs)
next
  case (T_Sub \<Gamma> S' T)
  from \<open>\<Gamma> \<turnstile> S' <: T\<close> and \<open>\<Gamma> \<turnstile> T <: U \<rightarrow> U'\<close>
  have "\<Gamma> \<turnstile> S' <: U \<rightarrow> U'" by (rule subtype_trans(1))
  then show ?case
    using T_Sub.hyps(2) T_Sub.prems(2) by blast
qed

lemma Abs_type':
  assumes "\<Gamma> \<turnstile> (\<lambda>:S. s) : U \<rightarrow> U'"
  and "\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> VarB S \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow> \<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 0 S' <: U' \<Longrightarrow> P"
  shows "P"
  using Abs_type assms subtype_refl' by blast

lemma TAbs_type: \<comment> \<open>A.13(2)\<close>
  assumes H: "\<Gamma> \<turnstile> (\<lambda><:S. s) : T"
  shows "\<Gamma> \<turnstile> T <: (\<forall><:U. U') \<Longrightarrow>
    (\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> TVarB U \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
      TVarB U \<Colon> \<Gamma> \<turnstile> S' <: U' \<Longrightarrow> P) \<Longrightarrow> P"
  using H
proof (induct \<Gamma> "\<lambda><:S. s" T arbitrary: U U' S s P)
  case (T_TAbs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>\<Gamma> \<turnstile> (\<forall><:T\<^sub>1. T\<^sub>2) <: (\<forall><:U. U')\<close>
  obtain ty1: "\<Gamma> \<turnstile> U <: T\<^sub>1" and ty2: "TVarB U \<Colon> \<Gamma> \<turnstile> T\<^sub>2 <: U'"
    by cases simp_all
  from \<open>TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close>
  have "TVarB U \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2" using ty1
    by (rule narrow_type [of "[]", simplified])
  then show ?case
    using T_TAbs ty1 ty2 by blast
next
  case (T_Sub \<Gamma> S' T)
  from \<open>\<Gamma> \<turnstile> S' <: T\<close> and \<open>\<Gamma> \<turnstile> T <: (\<forall><:U. U')\<close>
  have "\<Gamma> \<turnstile> S' <: (\<forall><:U. U')" by (rule subtype_trans(1))
  with T_Sub show ?case
    by metis
qed

lemma TAbs_type':
  assumes "\<Gamma> \<turnstile> (\<lambda><:S. s) : (\<forall><:U. U')"
  and "\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> TVarB U \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow> TVarB U \<Colon> \<Gamma> \<turnstile> S' <: U' \<Longrightarrow> P"
  shows "P"
  using assms TAbs_type subtype_refl' by blast

text \<open>
In the proof of the preservation theorem, the following elimination rule
for typing judgements on record types will be useful:
\<close>


lemma Rcd_type1: \<comment> \<open>A.13(3)\<close>
  assumes "\<Gamma> \<turnstile> t : T"
  shows "t = Rcd fs \<Longrightarrow> \<Gamma> \<turnstile> T <: RcdT fTs \<Longrightarrow>
     \<forall>(l, U) \<in> set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> \<Gamma> \<turnstile> u : U"
  using assms
proof (induct arbitrary: fs fTs rule: typing_induct)
  case (T_Sub \<Gamma> t S T)
  then show ?case
    using subtype_trans(1) by blast
next
  case (T_Rcd \<Gamma> gs gTs)
  then show ?case
    by (force dest: typings_setD intro: T_Sub elim: subtyping.cases)
qed blast+

lemma Rcd_type1':
  assumes H: "\<Gamma> \<turnstile> Rcd fs : RcdT fTs"
  shows "\<forall>(l, U) \<in> set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> \<Gamma> \<turnstile> u : U"
  using H refl subtype_refl' [OF H]
  by (rule Rcd_type1)

text \<open>
Intuitively, this means that for a record @{term "Rcd fs"} of type @{term "RcdT fTs"},
each field with name @{term l} associated with a type @{term U} in @{term "fTs"}
must correspond to a field in @{term fs} with value @{term u}, where @{term u} has
type @{term U}. Thanks to the subsumption rule \<open>T_Sub\<close>, the typing judgement
for terms is not sensitive to the order of record fields. For example,
@{term [display] "\<Gamma> \<turnstile> Rcd [(l\<^sub>1, t\<^sub>1), (l\<^sub>2, t\<^sub>2), (l\<^sub>3, t\<^sub>3)] : RcdT [(l\<^sub>2, T\<^sub>2), (l\<^sub>1, T\<^sub>1)]"}
provided that \<open>\<Gamma> \<turnstile> t\<^sub>i : T\<^sub>i\<close>. Note however that this does not imply
@{term [display] "\<Gamma> \<turnstile> [(l\<^sub>1, t\<^sub>1), (l\<^sub>2, t\<^sub>2), (l\<^sub>3, t\<^sub>3)] [:] [(l\<^sub>2, T\<^sub>2), (l\<^sub>1, T\<^sub>1)]"}
In order for this statement to hold, we need to remove the field @{term "l\<^sub>3"}
and exchange the order of the fields @{term "l\<^sub>1"} and @{term "l\<^sub>2"}. This gives rise
to the following variant of the above elimination rule:
\<close>

lemma Rcd_type2_aux:
  "\<lbrakk>\<Gamma> \<turnstile> T <: RcdT fTs; \<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> \<Gamma> \<turnstile> u : U\<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs [:] fTs"
proof (induct fTs rule: list.induct)
  case Nil
  then show ?case
    using T_Nil wf_subtypeE by force
next
  case (Cons p list)
  have "\<Gamma> \<turnstile> (a, the (fs\<langle>a\<rangle>\<^sub>?)) \<Colon> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) list [:] (a, b) \<Colon> list"
    if "p = (a, b)"
    for a b
  proof (rule T_Cons)
    show "\<Gamma> \<turnstile> the (fs\<langle>a\<rangle>\<^sub>?) : b"
      using Cons.prems(2) that by auto
    have "\<Gamma> \<turnstile> RcdT ((a, b) \<Colon> list) <: RcdT list"
    proof (intro SA_Rcd)
      show "\<Gamma> \<turnstile>\<^sub>w\<^sub>f"
        using Cons.prems(1) wf_subtypeE by blast
      have *: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT (p \<Colon> list)"
        using Cons.prems(1) wf_subtypeE by blast
      with that show "\<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT ((a, b) \<Colon> list)"
        by auto
      show "unique list"
        using * well_formed_cases(5) by fastforce
      show "\<forall>(l, T)\<in>set list. \<exists>S. (l, S) \<in> set ((a, b) \<Colon> list) \<and> \<Gamma> \<turnstile> S <: T"
        using Cons.prems(2) subtype_refl' by fastforce
    qed 
    with Cons
    show "\<Gamma> \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) list [:] list"
      by (metis (no_types, lifting) list.set_intros(2) subtype_trans(1) that)
    then show "map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) list\<langle>a\<rangle>\<^sub>? = \<bottom>"
      using Cons.prems(1) that well_formed_cases(5) wf_subtype by fastforce
  qed
  then show ?case
    by (auto split: prod.splits)
qed

lemma Rcd_type2:
  "\<Gamma> \<turnstile> Rcd fs : T \<Longrightarrow> \<Gamma> \<turnstile> T <: RcdT fTs \<Longrightarrow>
     \<Gamma> \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs [:] fTs"
  by (simp add: Rcd_type1 Rcd_type2_aux)

lemma Rcd_type2':
  assumes H: "\<Gamma> \<turnstile> Rcd fs : RcdT fTs"
  shows "\<Gamma> \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs [:] fTs"
  using H subtype_refl' [OF H]
  by (rule Rcd_type2)

lemma T_eq: "\<Gamma> \<turnstile> t : T \<Longrightarrow> T = T' \<Longrightarrow> \<Gamma> \<turnstile> t : T'" by simp

lemma ptyping_length [simp]:
  "\<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<parallel>p\<parallel>\<^sub>p = \<parallel>\<Delta>\<parallel>"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<parallel>fps\<parallel>\<^sub>r = \<parallel>\<Delta>\<parallel>"
  by (induct set: ptyping ptypings) simp_all

lemma lift_ptyping:
  "\<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> \<up>\<^sub>p n k p : \<up>\<^sub>\<tau> n k T \<Rightarrow> \<up>\<^sub>e n k \<Delta>"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> \<up>\<^sub>r\<^sub>p n k fps [:] \<up>\<^sub>r\<^sub>\<tau> n k fTs \<Rightarrow> \<up>\<^sub>e n k \<Delta>"
proof (induct set: ptyping ptypings)
  case P_Nil
  then show ?case
    by (simp add: ptyping_ptypings.P_Nil)
next
  case (P_Cons p T \<Delta>\<^sub>1 fps fTs \<Delta>\<^sub>2 l)
  then show ?case
    using P_Cons.hyps(2) ptyping_ptypings.P_Cons by fastforce
qed (auto simp: ptyping.simps)

lemma type_weaken:
  "\<Delta> @ \<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow>
     \<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up> 1 \<parallel>\<Delta>\<parallel> t : \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
  "\<Delta> @ \<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow>
     \<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>r 1 \<parallel>\<Delta>\<parallel> fs [:] \<up>\<^sub>r\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> fTs"
proof (induct "\<Delta> @ \<Gamma>" t T and "\<Delta> @ \<Gamma>" fs fTs arbitrary: \<Delta> and \<Delta> set: typing typings)
  case (T_Var i U T \<Delta>)
  show ?case 
  proof -
    have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> Var i : \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T"
      if "i < \<parallel>\<Delta>\<parallel>"
      using that T_Var by (force simp: typing_typings.T_Var wfE_weaken)
    moreover have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> Var (Suc i) : \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T"
      if "\<not> i < \<parallel>\<Delta>\<parallel>"
    proof (intro typing_typings.T_Var)
      have *: "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)"
        using that by simp
      show "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
        by (simp add: T_Var wfE_weaken)
      show "(\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma>)\<langle>Suc i\<rangle> = \<lfloor>VarB U\<rfloor>"
        using T_Var that by (simp add: * split: nat.splits)
      show "\<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T = \<up>\<^sub>\<tau> (Suc (Suc i)) 0 U"
        using T_Var.hyps(3) that by fastforce
    qed
    ultimately show ?thesis
      by auto
  qed
next
  case (T_Abs T\<^sub>1 t\<^sub>2 T\<^sub>2)
  then show ?case
    using typing_typings.T_Abs by force
next
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 t\<^sub>2)
  then show ?case
    by (simp add: typing_typings.T_App)
next
  case (T_TAbs T\<^sub>1 t\<^sub>2 T\<^sub>2)
  then show ?case
    by (simp add: typing_typings.T_TAbs)
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2)
  have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T\<^sub>2 <: \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T\<^sub>1\<^sub>1"
    using subtype_weaken by (simp add: T_TApp)
  moreover have "\<up>\<^sub>\<tau> (Suc 0) (Suc \<parallel>\<Delta>\<parallel>) T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T\<^sub>2]\<^sub>\<tau> = \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> (T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>)"
    by (metis Suc_eq_plus1 add.commute diff_zero le_eq_less_or_eq liftT_substT'(1)
        liftT_substT(1) liftT_substT_strange(1) not_gr_zero)
  ultimately show ?case
    using T_TApp
    by (metis Suc_eq_plus1 add.commute add.right_neutral
        lift.simps(5) liftT.simps(4) typing_typings.T_TApp)
next
  case (T_Sub t S T)
  then show ?case
    using subtype_weaken typing_typings.T_Sub by blast
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 \<Delta>')
  then have "\<up>\<^sub>e (Suc 0) \<parallel>\<Delta>'\<parallel> \<Delta> @ \<up>\<^sub>e (Suc 0) 0 \<Delta>' @ B \<Colon> \<Gamma> \<turnstile> \<up> (Suc 0) (\<parallel>\<Delta>\<parallel> + \<parallel>\<Delta>'\<parallel>) t\<^sub>2 : \<up>\<^sub>\<tau> (Suc 0) (\<parallel>\<Delta>\<parallel> + \<parallel>\<Delta>'\<parallel>) T\<^sub>2"
    by simp
  with T_Let 
  have "\<up>\<^sub>e (Suc 0) 0 \<Delta>' @ B \<Colon> \<Gamma>
          \<turnstile> (LET \<up>\<^sub>p (Suc 0) \<parallel>\<Delta>'\<parallel> p = \<up> (Suc 0) \<parallel>\<Delta>'\<parallel> t\<^sub>1 IN \<up> (Suc 0) (\<parallel>\<Delta>'\<parallel> + \<parallel>\<Delta>\<parallel>) t\<^sub>2) : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 (\<up>\<^sub>\<tau> (Suc 0) (\<parallel>\<Delta>\<parallel> + \<parallel>\<Delta>'\<parallel>) T\<^sub>2)"
    by (metis add.commute liftE_length lift_ptyping(1) nat_1 nat_one_as_int
        typing_typings.T_Let)
  with T_Let show ?case
    by (simp add: ac_simps)
next
  case (T_Rcd fs fTs)
  then show ?case
    by (simp add: typing_typings.T_Rcd)
next
  case (T_Proj t fTs l T)
  then show ?case
    by (simp add: liftrT_assoc_Some typing_typings.T_Proj)
next
  case T_Nil
  then show ?case
    by (simp add: typing_typings.T_Nil wfE_weaken)
next
  case (T_Cons t T fs fTs l)
  then show ?case
    by (simp add: typing_typings.T_Cons)
qed

lemma type_weaken': \<comment> \<open>A.5(6)\<close>
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> \<up> \<parallel>\<Delta>\<parallel> 0 t : \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
proof (induct \<Delta>)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Delta>)
  then have "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B a" "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
    by (auto elim: well_formedE_cases)
  with Cons type_weaken(1)[of "[]", where B=a] show ?case
    by (metis Suc_eq_plus1 append_Cons append_Nil le_add1 le_refl length_Cons
        liftE.simps(1) liftT_liftT(1) lift_lift(1) list.size(3))
qed

text \<open>
The substitution lemmas are now proved by mutual induction on the derivations of
the typing derivations for terms and lists of fields.
\<close>

lemma subst_ptyping:
  "\<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> p[k \<mapsto>\<^sub>\<tau> U]\<^sub>p : T[k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> \<Rightarrow> \<Delta>[k \<mapsto>\<^sub>\<tau> U]\<^sub>e"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> fps[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>p [:] fTs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau> \<Rightarrow> \<Delta>[k \<mapsto>\<^sub>\<tau> U]\<^sub>e"
proof (induct set: ptyping ptypings)
  case (P_Var T)
  then show ?case
    by (simp add: ptyping.simps)
next
  case (P_Rcd fps fTs \<Delta>)
  then show ?case
    by (simp add: ptyping_ptypings.P_Rcd)
next
  case P_Nil
  then show ?case
    by (simp add: ptyping_ptypings.P_Nil)
next
  case (P_Cons p T \<Delta>\<^sub>1 fps fTs \<Delta>\<^sub>2 l)
  then show ?case
    using ptyping_ptypings.P_Cons by fastforce
qed

theorem subst_type: \<comment> \<open>A.8\<close>
  "\<Delta> @ VarB U \<Colon> \<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile> u : U \<Longrightarrow>
     \<down>\<^sub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> t[\<parallel>\<Delta>\<parallel> \<mapsto> u] : \<down>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
  "\<Delta> @ VarB U \<Colon> \<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile> u : U \<Longrightarrow>
     \<down>\<^sub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> fs[\<parallel>\<Delta>\<parallel> \<mapsto> u]\<^sub>r [:] \<down>\<^sub>r\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> fTs"
proof (induct "\<Delta> @ VarB U \<Colon> \<Gamma>" t T and "\<Delta> @ VarB U \<Colon> \<Gamma>" fs fTs
    arbitrary: \<Delta> and \<Delta> set: typing typings)
  case (T_Var i U' T  \<Delta>')
  show ?case
  proof -
    have "\<Delta>'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma> \<turnstile> \<up> \<parallel>\<Delta>'\<parallel> 0 u : T[\<parallel>\<Delta>'\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
      if "i = \<parallel>\<Delta>'\<parallel>"
      using that T_Var type_weaken' wfE_subst wf_Top by fastforce
    moreover have "\<Delta>'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma> \<turnstile> Var (i - Suc 0) : T[\<parallel>\<Delta>'\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
      if "\<parallel>\<Delta>'\<parallel> < i"
    proof (intro typing_typings.T_Var)
      show "\<Delta>'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
        using T_Var.hyps(1) wfE_subst wf_Top by force
      have "\<parallel>\<Delta>'\<parallel> \<le> i - Suc 0"
        using \<open>\<parallel>\<Delta>'\<parallel> < i\<close> by linarith
      with T_Var that show "(\<Delta>'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma>)\<langle>i - Suc 0\<rangle> = \<lfloor>VarB U'\<rfloor>"
        using Suc_diff_Suc by (fastforce simp: split: nat.split_asm)
      show "T[\<parallel>\<Delta>'\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau> = \<up>\<^sub>\<tau> (Suc (i - Suc 0)) 0 U'"
        using \<open>\<parallel>\<Delta>'\<parallel> < i\<close> T_Var.hyps by auto
    qed
    moreover have "\<Delta>'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma> \<turnstile> Var i : T[\<parallel>\<Delta>'\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
      if "\<parallel>\<Delta>'\<parallel> > i"
    proof (intro typing_typings.T_Var)
      show "\<Delta>'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
        using T_Var wfE_subst wf_Top by blast
      show "T[\<parallel>\<Delta>'\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau> = \<up>\<^sub>\<tau> (Suc i) 0 (U'[\<parallel>\<Delta>'\<parallel> - Suc i \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>)"
        using T_Var by (metis that Suc_leI le0 le_add_diff_inverse2 liftT_substT(1))
    qed (use that T_Var in auto)
    ultimately show ?thesis
      by auto
  qed
next
  case (T_Abs T\<^sub>1 t\<^sub>2 T\<^sub>2)
  then show ?case
    by (simp add: typing_typings.T_Abs [THEN T_eq] flip: substT_substT)
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2)
  then show ?case
    using subst_subtype typing_typings.T_TApp
    apply simp
    by (metis diff_zero le0 substT_substT(1) typing_typings.T_TApp)
next
  case (T_Sub t S T)
  then show ?case
    using subst_subtype typing_typings.T_Sub by blast
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 \<Delta>')
  then show ?case
    apply simp
    by (metis add.commute substE_length subst_ptyping(1) typing_typings.T_Let)
next
  case T_Nil
  then show ?case
    by (simp add: typing_typings.T_Nil wfE_subst wf_Top)
qed (auto simp: typing_typings.intros)

theorem substT_type: \<comment> \<open>A.11\<close>
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
     \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> t[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P] : T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
     \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> fs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>r [:] fTs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>r\<^sub>\<tau>"
proof (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" t T and "\<Delta> @ TVarB Q \<Colon> \<Gamma>" fs fTs
              arbitrary: \<Delta> and \<Delta> set: typing typings)
  case (T_Var i U T \<Delta>)
  show ?case
  proof -
    have "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
      if "\<parallel>\<Delta>\<parallel> < i"
      using that
      by (meson T_Var.hyps(1) T_Var.prems wfE_subst wf_subtypeE)
    moreover have "(\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma>)\<langle>i - Suc 0\<rangle> = \<lfloor>VarB U\<rfloor>"
      if "\<parallel>\<Delta>\<parallel> < i"
      using that T_Var Suc_diff_Suc by (force split: nat.split_asm)
    moreover have "T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau> = \<up>\<^sub>\<tau> (Suc (i - Suc 0)) 0 U"
      if "\<parallel>\<Delta>\<parallel> < i"
      using that T_Var.hyps by fastforce
    moreover have "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> Var i : T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
      if "\<parallel>\<Delta>\<parallel> = i"
      using T_Var that by auto
    moreover have "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> Var i : T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
      if "\<parallel>\<Delta>\<parallel> > i"
    proof -
      have "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>"
        using that by linarith
      then have \<section>: "\<up>\<^sub>\<tau> (Suc i) 0 U[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau> = \<up>\<^sub>\<tau> (Suc i) 0 (U[\<parallel>\<Delta>\<parallel> - Suc i \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>)"
        using that by fastforce
      show ?thesis
      proof (intro typing_typings.T_Var)
        show "\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
          by (meson T_Var.hyps(1) T_Var.prems wfE_subst wf_subtypeE)
        show "(\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma>)\<langle>i\<rangle> = \<lfloor>VarB (U[\<parallel>\<Delta>\<parallel> - Suc i \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>)\<rfloor>"
          using \<section> that T_Var by simp
        show "T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau> = \<up>\<^sub>\<tau> (Suc i) 0 (U[\<parallel>\<Delta>\<parallel> - Suc i \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>)"
          using \<section> T_Var by blast
      qed
    qed
    ultimately show ?thesis
      by (metis One_nat_def linorder_cases substT.simps(1) typing_typings.T_Var)
  qed
next
  case (T_Abs T\<^sub>1 t\<^sub>2 T\<^sub>2)
  then show ?case     
    by (simp add: typing_typings.T_Abs [THEN T_eq] flip: substT_substT)
next
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 t\<^sub>2)
  then show ?case
    using typing_typings.T_App by auto
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2)
  then show ?case
    apply (simp add: )
    by (metis minus_nat.diff_0 substT_substT(1) substT_subtype typing_typings.T_TApp
        zero_le)
next
  case (T_Sub t S T)
  then show ?case
    using substT_subtype typing_typings.T_Sub by blast
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2)
  then show ?case
    apply simp
    by (metis add.commute substE_length subst_ptyping(1) typing_typings.T_Let)
next
  case T_Nil
  then show ?case
    by (simp add: typing_typings.T_Nil wfE_subst wf_subtype)
qed (auto simp: typing_typings.intros)

subsection \<open>Evaluation\<close>

text \<open>
\label{sec:evaluation-rcd}
The definition of canonical values is extended with a clause saying that
a record @{term "Rcd fs"} is a canonical value if all fields contain
canonical values:
\<close>

inductive_set
  "value" :: "trm set"
where
  Abs: "(\<lambda>:T. t) \<in> value"
| TAbs: "(\<lambda><:T. t) \<in> value"
| Rcd: "\<forall>(l, t) \<in> set fs. t \<in> value \<Longrightarrow> Rcd fs \<in> value"

text \<open>
In order to formalize the evaluation rule for \<open>LET\<close>, we introduce another
relation \<open>\<turnstile> p \<rhd> t \<Rightarrow> ts\<close> expressing that a pattern @{term p} matches a
term @{term t}. The relation also yields a list of terms @{term ts} corresponding
to the variables in the pattern. The relation is defined simultaneously with another
relation \<open>\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts\<close> for matching a list of field patterns @{term fps}
against a list of fields @{term fs}:
\<close>

inductive
  match :: "pat \<Rightarrow> trm \<Rightarrow> trm list \<Rightarrow> bool"  (\<open>\<turnstile> _ \<rhd> _ \<Rightarrow> _\<close> [50, 50, 50] 50)
  and matchs :: "rpat \<Rightarrow> rcd \<Rightarrow> trm list \<Rightarrow> bool"  (\<open>\<turnstile> _ [\<rhd>] _ \<Rightarrow> _\<close> [50, 50, 50] 50)
where
  M_PVar: "\<turnstile> PVar T \<rhd> t \<Rightarrow> [t]"
| M_Rcd: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts \<Longrightarrow> \<turnstile> PRcd fps \<rhd> Rcd fs \<Rightarrow> ts"
| M_Nil: "\<turnstile> [] [\<rhd>] fs \<Rightarrow> []"
| M_Cons: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>t\<rfloor> \<Longrightarrow> \<turnstile> p \<rhd> t \<Rightarrow> ts \<Longrightarrow> \<turnstile> fps [\<rhd>] fs \<Rightarrow> us \<Longrightarrow>
    \<turnstile> (l, p) \<Colon> fps [\<rhd>] fs \<Rightarrow> ts @ us"

text \<open>
The rules of the evaluation relation for the calculus with records are as follows:
\<close>

inductive
  eval :: "trm \<Rightarrow> trm \<Rightarrow> bool"  (infixl \<open>\<longmapsto>\<close> 50)
  and evals :: "rcd \<Rightarrow> rcd \<Rightarrow> bool"  (infixl \<open>[\<longmapsto>]\<close> 50)
where
  E_Abs: "v\<^sub>2 \<in> value \<Longrightarrow> (\<lambda>:T\<^sub>1\<^sub>1. t\<^sub>1\<^sub>2) \<bullet> v\<^sub>2 \<longmapsto> t\<^sub>1\<^sub>2[0 \<mapsto> v\<^sub>2]"
| E_TAbs: "(\<lambda><:T\<^sub>1\<^sub>1. t\<^sub>1\<^sub>2) \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]"
| E_App1: "t \<longmapsto> t' \<Longrightarrow> t \<bullet> u \<longmapsto> t' \<bullet> u"
| E_App2: "v \<in> value \<Longrightarrow> t \<longmapsto> t' \<Longrightarrow> v \<bullet> t \<longmapsto> v \<bullet> t'"
| E_TApp: "t \<longmapsto> t' \<Longrightarrow> t \<bullet>\<^sub>\<tau> T \<longmapsto> t' \<bullet>\<^sub>\<tau> T"
| E_LetV: "v \<in> value \<Longrightarrow> \<turnstile> p \<rhd> v \<Rightarrow> ts \<Longrightarrow> (LET p = v IN t) \<longmapsto> t[0 \<mapsto>\<^sub>s ts]"
| E_ProjRcd: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>v\<rfloor> \<Longrightarrow> v \<in> value \<Longrightarrow> Rcd fs..l \<longmapsto> v"
| E_Proj: "t \<longmapsto> t' \<Longrightarrow> t..l \<longmapsto> t'..l"
| E_Rcd: "fs [\<longmapsto>] fs' \<Longrightarrow> Rcd fs \<longmapsto> Rcd fs'"
| E_Let: "t \<longmapsto> t' \<Longrightarrow> (LET p = t IN u) \<longmapsto> (LET p = t' IN u)"
| E_hd: "t \<longmapsto> t' \<Longrightarrow> (l, t) \<Colon> fs [\<longmapsto>] (l, t') \<Colon> fs"
| E_tl: "v \<in> value \<Longrightarrow> fs [\<longmapsto>] fs' \<Longrightarrow> (l, v) \<Colon> fs [\<longmapsto>] (l, v) \<Colon> fs'"

text \<open>
The relation @{term "t \<longmapsto> t'"} is defined simultaneously with
a relation \mbox{@{term "fs [\<longmapsto>] fs'"}} for evaluating record fields.
The ``immediate'' reductions, namely pattern matching and projection,
are described by the rules \<open>E_LetV\<close> and \<open>E_ProjRcd\<close>, respectively,
whereas \<open>E_Proj\<close>, \<open>E_Rcd\<close>, \<open>E_Let\<close>, \<open>E_hd\<close> and
\<open>E_tl\<close> are congruence rules.
\<close>

lemmas matchs_induct = match_matchs.inducts(2)
  [of _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names M_Nil M_Cons]

lemmas evals_induct = eval_evals.inducts(2)
  [of _ _ "\<lambda>x y. True", simplified True_simps, consumes 1,
   case_names E_hd E_tl]

lemma matchs_mono:
  assumes H: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts"
  shows "fps\<langle>l\<rangle>\<^sub>? = \<bottom> \<Longrightarrow> \<turnstile> fps [\<rhd>] (l, t) \<Colon> fs \<Rightarrow> ts"
  using H
proof (induct rule: matchs_induct)
  case (M_Nil fs)
  then show ?case
    by (simp add: match_matchs.M_Nil)
next
  case (M_Cons fs l t p ts fps us)
  then show ?case
    by (metis assoc.simps(2) fstI match_matchs.M_Cons option.distinct(1))
qed

lemma matchs_eq:
  assumes H: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts"
  shows "\<forall>(l, p) \<in> set fps. fs\<langle>l\<rangle>\<^sub>? = fs'\<langle>l\<rangle>\<^sub>? \<Longrightarrow> \<turnstile> fps [\<rhd>] fs' \<Rightarrow> ts"
  using H
proof (induct rule: matchs_induct)
  case (M_Nil fs)
  then show ?case
    using match_matchs.M_Nil by auto
next
  case (M_Cons fs l t p ts fps us)
  then show ?case
    using match_matchs.M_Cons by force
qed

lemma reorder_eq:
  assumes H: "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta>"
  shows "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<Longrightarrow>
         \<forall>(l, p) \<in> set fps. fs\<langle>l\<rangle>\<^sub>? = (map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs)\<langle>l\<rangle>\<^sub>?"
  using H by (induct rule: ptypings_induct) auto

lemma matchs_reorder:
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<Longrightarrow>
    \<turnstile> fps [\<rhd>] fs \<Rightarrow> ts \<Longrightarrow> \<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> ts"
  by (rule matchs_eq [OF _ reorder_eq], assumption+)

lemma matchs_reorder':
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<Longrightarrow>
     \<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> ts \<Longrightarrow> \<turnstile> fps [\<rhd>] fs \<Rightarrow> ts"
  by (rule matchs_eq [OF _ reorder_eq [THEN ball_eq_sym]], assumption+)

theorem matchs_tl:
  assumes H: "\<turnstile> fps [\<rhd>] (l, t) \<Colon> fs \<Rightarrow> ts"
  shows "fps\<langle>l\<rangle>\<^sub>? = \<bottom> \<Longrightarrow> \<turnstile> fps [\<rhd>] fs \<Rightarrow> ts"
  using H
proof (induct fps "(l, t) \<Colon> fs" ts arbitrary: l t fs rule: matchs_induct)
  case M_Nil
  then show ?case
    by (simp add: match_matchs.M_Nil)
next
  case (M_Cons l t p ts fps us)
  then show ?case
    by (metis assoc.simps(2) fst_conv match_matchs.M_Cons not_Some_eq)
qed

theorem match_length:
  "\<turnstile> p \<rhd> t \<Rightarrow> ts \<Longrightarrow> \<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<parallel>ts\<parallel> = \<parallel>\<Delta>\<parallel>"
  "\<turnstile> fps [\<rhd>] ft \<Rightarrow> ts \<Longrightarrow> \<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<parallel>ts\<parallel> = \<parallel>\<Delta>\<parallel>"
  by (induct arbitrary: T \<Delta> and fTs \<Delta> set: match matchs)
    (erule ptyping.cases ptypings.cases, simp+)+

text \<open>
In the proof of the preservation theorem
for the calculus with records, we need the following lemma relating
the matching and typing judgements for patterns,
which means that well-typed matching preserves typing. Although this property
will only be used for @{term "\<Gamma>\<^sub>1 = []"} later, the statement must be proved in
a more general form in order for the induction to go through.
\<close>

theorem match_type: \<comment> \<open>A.17\<close>
  "\<turnstile> p : T\<^sub>1 \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma>\<^sub>2 \<turnstile> t\<^sub>1 : T\<^sub>1 \<Longrightarrow>
     \<Gamma>\<^sub>1 @ \<Delta> @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<turnstile> p \<rhd> t\<^sub>1 \<Rightarrow> ts \<Longrightarrow>
       \<down>\<^sub>e \<parallel>\<Delta>\<parallel> 0 \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> \<mapsto>\<^sub>s ts] : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> \<parallel>\<Gamma>\<^sub>1\<parallel> T\<^sub>2"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma>\<^sub>2 \<turnstile> fs [:] fTs \<Longrightarrow>
     \<Gamma>\<^sub>1 @ \<Delta> @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<turnstile> fps [\<rhd>] fs \<Rightarrow> ts \<Longrightarrow>
       \<down>\<^sub>e \<parallel>\<Delta>\<parallel> 0 \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> \<mapsto>\<^sub>s ts] : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> \<parallel>\<Gamma>\<^sub>1\<parallel> T\<^sub>2"
proof (induct arbitrary: \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 t\<^sub>1 t\<^sub>2 T\<^sub>2 ts and \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 fs t\<^sub>2 T\<^sub>2 ts set: ptyping ptypings)
  case (P_Var T \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 t\<^sub>1 t\<^sub>2 T\<^sub>2 ts)
  from P_Var have "\<Gamma>\<^sub>1[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> \<mapsto> t\<^sub>1] : T\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
    by - (rule subst_type [simplified], simp_all)
  moreover from P_Var(3) have "ts = [t\<^sub>1]" by cases simp_all
  ultimately show ?case by simp
next
  case (P_Rcd fps fTs \<Delta> \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 t\<^sub>1 t\<^sub>2 T\<^sub>2 ts)
  from P_Rcd(5) obtain fs where
    t\<^sub>1: "t\<^sub>1 = Rcd fs" and fps: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts" by cases simp_all
  with P_Rcd have fs: "\<Gamma>\<^sub>2 \<turnstile> Rcd fs : RcdT fTs" by simp
  hence "\<Gamma>\<^sub>2 \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs [:] fTs"
    by (rule Rcd_type2')
  moreover note P_Rcd(4)
  moreover from fs have "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> \<Gamma>\<^sub>2 \<turnstile> u : U"
    by (rule Rcd_type1')
  hence "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor>" by blast
  with P_Rcd(1) have "\<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> ts"
    using fps by (rule matchs_reorder)
  ultimately show ?case by (rule P_Rcd)
next
  case (P_Nil \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 fs t\<^sub>2 T\<^sub>2 ts)
  from P_Nil(3) have "ts = []" by cases simp_all
  with P_Nil show ?case by simp
next
  case (P_Cons p T \<Delta>\<^sub>1 fps fTs \<Delta>\<^sub>2 l \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 fs t\<^sub>2 T\<^sub>2 ts)
  from P_Cons(8) obtain t ts\<^sub>1 ts\<^sub>2 where
    t: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>t\<rfloor>" and p: "\<turnstile> p \<rhd> t \<Rightarrow> ts\<^sub>1" and fps: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts\<^sub>2"
    and ts: "ts = ts\<^sub>1 @ ts\<^sub>2" by cases simp_all
  from P_Cons(6) t fps obtain fs' where
    fps': "\<turnstile> fps [\<rhd>] (l, t) \<Colon> fs' \<Rightarrow> ts\<^sub>2" and tT: "\<Gamma>\<^sub>2 \<turnstile> t : T" and fs': "\<Gamma>\<^sub>2 \<turnstile> fs' [:] fTs"
    and l: "fs'\<langle>l\<rangle>\<^sub>? = \<bottom>" by cases auto
  from P_Cons have "(\<Gamma>\<^sub>1 @ \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2) @ \<Delta>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2 : T\<^sub>2" by simp
  with tT have ts\<^sub>1: "\<down>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 (\<Gamma>\<^sub>1 @ \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2) @ \<Gamma>\<^sub>2 \<turnstile>
    t\<^sub>2[\<parallel>\<Gamma>\<^sub>1 @ \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2\<parallel> \<mapsto>\<^sub>s ts\<^sub>1] : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<^sub>1\<parallel> \<parallel>\<Gamma>\<^sub>1 @ \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2\<parallel> T\<^sub>2"
    using p by (rule P_Cons)
  from fps' P_Cons(5) have "\<turnstile> fps [\<rhd>] fs' \<Rightarrow> ts\<^sub>2" by (rule matchs_tl)
  with fs' ts\<^sub>1 [simplified]
  have "\<down>\<^sub>e \<parallel>\<Delta>\<^sub>2\<parallel> 0 (\<down>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> \<parallel>\<Delta>\<^sub>2\<parallel> \<Gamma>\<^sub>1) @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> + \<parallel>\<Delta>\<^sub>2\<parallel> \<mapsto>\<^sub>s ts\<^sub>1][\<parallel>\<down>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> \<parallel>\<Delta>\<^sub>2\<parallel> \<Gamma>\<^sub>1\<parallel> \<mapsto>\<^sub>s ts\<^sub>2] :
    \<down>\<^sub>\<tau> \<parallel>\<Delta>\<^sub>2\<parallel> \<parallel>\<down>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> \<parallel>\<Delta>\<^sub>2\<parallel> \<Gamma>\<^sub>1\<parallel> (\<down>\<^sub>\<tau> \<parallel>\<Delta>\<^sub>1\<parallel> (\<parallel>\<Gamma>\<^sub>1\<parallel> + \<parallel>\<Delta>\<^sub>2\<parallel>) T\<^sub>2)"
    by (rule P_Cons(4))
  thus ?case by (simp add: decE_decE [of _ 0, simplified]
    match_length(2) [OF fps P_Cons(3)] ts)
qed

lemma evals_labels [simp]:
  assumes H: "fs [\<longmapsto>] fs'"
  shows "(fs\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs'\<langle>l\<rangle>\<^sub>? = \<bottom>)" using H
  by (induct rule: evals_induct) simp_all

theorem preservation: \<comment> \<open>A.20\<close>
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> t \<longmapsto> t' \<Longrightarrow> \<Gamma> \<turnstile> t' : T"
  "\<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> fs [\<longmapsto>] fs' \<Longrightarrow> \<Gamma> \<turnstile> fs' [:] fTs"
proof (induct arbitrary: t' and fs' set: typing typings)
  case (T_Var \<Gamma> i U T t')
  from \<open>Var i \<longmapsto> t'\<close>
  show ?case by cases
next
  case (T_Abs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2 t')
  from \<open>(\<lambda>:T\<^sub>1. t\<^sub>2) \<longmapsto> t'\<close>
  show ?case by cases
next
  case (T_App \<Gamma> t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 t\<^sub>2 t')
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_Abs T\<^sub>1\<^sub>1' t\<^sub>1\<^sub>2)
    with T_App have "\<Gamma> \<turnstile> (\<lambda>:T\<^sub>1\<^sub>1'. t\<^sub>1\<^sub>2) : T\<^sub>1\<^sub>1 \<rightarrow> T\<^sub>1\<^sub>2" by simp
    then obtain S'
      where T\<^sub>1\<^sub>1: "\<Gamma> \<turnstile> T\<^sub>1\<^sub>1 <: T\<^sub>1\<^sub>1'"
      and t\<^sub>1\<^sub>2: "VarB T\<^sub>1\<^sub>1' \<Colon> \<Gamma> \<turnstile> t\<^sub>1\<^sub>2 : S'"
      and S': "\<Gamma> \<turnstile> S'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau> <: T\<^sub>1\<^sub>2" by (rule Abs_type' [simplified]) blast
    from \<open>\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1\<close>
    have "\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1'" using T\<^sub>1\<^sub>1 by (rule T_Sub)
    with t\<^sub>1\<^sub>2 have "\<Gamma> \<turnstile> t\<^sub>1\<^sub>2[0 \<mapsto> t\<^sub>2] : S'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
      by (rule subst_type [where \<Delta>="[]", simplified])
    hence "\<Gamma> \<turnstile> t\<^sub>1\<^sub>2[0 \<mapsto> t\<^sub>2] : T\<^sub>1\<^sub>2" using S' by (rule T_Sub)
    with E_Abs show ?thesis by simp
  next
    case (E_App1 t'')
    from \<open>t\<^sub>1 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : T\<^sub>1\<^sub>1 \<rightarrow> T\<^sub>1\<^sub>2" by (rule T_App)
    hence "\<Gamma> \<turnstile> t'' \<bullet> t\<^sub>2 : T\<^sub>1\<^sub>2" using \<open>\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1\<close>
      by (rule typing_typings.T_App)
    with E_App1 show ?thesis by simp
  next
    case (E_App2 t'')
    from \<open>t\<^sub>2 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : T\<^sub>1\<^sub>1" by (rule T_App)
    with T_App(1) have "\<Gamma> \<turnstile> t\<^sub>1 \<bullet> t'' : T\<^sub>1\<^sub>2"
      by (rule typing_typings.T_App)
    with E_App2 show ?thesis by simp
  qed
next
  case (T_TAbs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2 t')
  from \<open>(\<lambda><:T\<^sub>1. t\<^sub>2) \<longmapsto> t'\<close>
  show ?case by cases
next
  case (T_TApp \<Gamma> t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 t')
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_TAbs T\<^sub>1\<^sub>1' t\<^sub>1\<^sub>2)
    with T_TApp have "\<Gamma> \<turnstile> (\<lambda><:T\<^sub>1\<^sub>1'. t\<^sub>1\<^sub>2) : (\<forall><:T\<^sub>1\<^sub>1. T\<^sub>1\<^sub>2)" by simp
    then obtain S'
      where "TVarB T\<^sub>1\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>1\<^sub>2 : S'"
      and "TVarB T\<^sub>1\<^sub>1 \<Colon> \<Gamma> \<turnstile> S' <: T\<^sub>1\<^sub>2" by (rule TAbs_type') blast
    hence "TVarB T\<^sub>1\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>1\<^sub>2 : T\<^sub>1\<^sub>2" by (rule T_Sub)
    hence "\<Gamma> \<turnstile> t\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2] : T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>" using T_TApp(3)
      by (rule substT_type [where \<Delta>="[]", simplified])
    with E_TAbs show ?thesis by simp
  next
    case (E_TApp t'')
    from \<open>t\<^sub>1 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : (\<forall><:T\<^sub>1\<^sub>1. T\<^sub>1\<^sub>2)" by (rule T_TApp)
    hence "\<Gamma> \<turnstile> t'' \<bullet>\<^sub>\<tau> T\<^sub>2 : T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>" using \<open>\<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>1\<^sub>1\<close>
      by (rule typing_typings.T_TApp)
    with E_TApp show ?thesis by simp
  qed
next
  case (T_Sub \<Gamma> t S T t')
  from \<open>t \<longmapsto> t'\<close>
  have "\<Gamma> \<turnstile> t' : S" by (rule T_Sub)
  then show ?case using \<open>\<Gamma> \<turnstile> S <: T\<close>
    by (rule typing_typings.T_Sub)
next
  case (T_Let \<Gamma> t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 t')
  from \<open>(LET p = t\<^sub>1 IN t\<^sub>2) \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_LetV ts)
    from T_Let (3,1,4) \<open>\<turnstile> p \<rhd> t\<^sub>1 \<Rightarrow> ts\<close>
    have "\<Gamma> \<turnstile> t\<^sub>2[0 \<mapsto>\<^sub>s ts] : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T\<^sub>2"
      by (rule match_type(1) [of _ _ _ _ _ "[]", simplified])
    with E_LetV show ?thesis by simp
  next
    case (E_Let t'')
    from \<open>t\<^sub>1 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : T\<^sub>1" by (rule T_Let)
    hence "\<Gamma> \<turnstile> (LET p = t'' IN t\<^sub>2) : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T\<^sub>2" using T_Let(3,4)
      by (rule typing_typings.T_Let)
    with E_Let show ?thesis by simp
  qed
next
  case (T_Rcd \<Gamma> fs fTs t')
  from \<open>Rcd fs \<longmapsto> t'\<close>
  obtain fs' where t': "t' = Rcd fs'" and fs: "fs [\<longmapsto>] fs'"
    by cases simp_all
  from fs have "\<Gamma> \<turnstile> fs' [:] fTs" by (rule T_Rcd)
  hence "\<Gamma> \<turnstile> Rcd fs' : RcdT fTs" by (rule typing_typings.T_Rcd)
  with t' show ?case by simp
next
  case (T_Proj \<Gamma> t fTs l T t')
  from \<open>t..l \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_ProjRcd fs)
    with T_Proj have "\<Gamma> \<turnstile> Rcd fs : RcdT fTs" by simp
    hence "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> \<Gamma> \<turnstile> u : U"
      by (rule Rcd_type1')
    with E_ProjRcd T_Proj show ?thesis by (fastforce dest: assoc_set)
  next
    case (E_Proj t'')
    from \<open>t \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : RcdT fTs" by (rule T_Proj)
    hence "\<Gamma> \<turnstile> t''..l : T" using T_Proj(3)
      by (rule typing_typings.T_Proj)
    with E_Proj show ?thesis by simp
  qed
next
  case (T_Nil \<Gamma> fs')
  from \<open>[] [\<longmapsto>] fs'\<close>
  show ?case by cases
next
  case (T_Cons \<Gamma> t T fs fTs l fs')
  from \<open>(l, t) \<Colon> fs [\<longmapsto>] fs'\<close>
  show ?case
  proof cases
    case (E_hd t')
    from \<open>t \<longmapsto> t'\<close>
    have "\<Gamma> \<turnstile> t' : T" by (rule T_Cons)
    hence "\<Gamma> \<turnstile> (l, t') \<Colon> fs [:] (l, T) \<Colon> fTs" using T_Cons(3,5)
      by (rule typing_typings.T_Cons)
    with E_hd show ?thesis by simp
  next
    case (E_tl fs'')
    note fs = \<open>fs [\<longmapsto>] fs''\<close>
    note T_Cons(1)
    moreover from fs have "\<Gamma> \<turnstile> fs'' [:] fTs" by (rule T_Cons)
    moreover from fs T_Cons have "fs''\<langle>l\<rangle>\<^sub>? = \<bottom>" by simp
    ultimately have "\<Gamma> \<turnstile> (l, t) \<Colon> fs'' [:] (l, T) \<Colon> fTs"
      by (rule typing_typings.T_Cons)
    with E_tl show ?thesis by simp
  qed
qed

lemma Fun_canonical: \<comment> \<open>A.14(1)\<close>
  assumes ty: "[] \<turnstile> v : T\<^sub>1 \<rightarrow> T\<^sub>2"
  shows "v \<in> value \<Longrightarrow> \<exists>t S. v = (\<lambda>:S. t)" using ty
proof (induct "[]::env" v "T\<^sub>1 \<rightarrow> T\<^sub>2" arbitrary: T\<^sub>1 T\<^sub>2 rule: typing_induct)
  case T_Abs
  show ?case by iprover
next
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 t\<^sub>2 T\<^sub>1 T\<^sub>2)
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 T\<^sub>1 T\<^sub>2')
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_Sub t S T\<^sub>1 T\<^sub>2)
  from \<open>[] \<turnstile> S <: T\<^sub>1 \<rightarrow> T\<^sub>2\<close>
  obtain S\<^sub>1 S\<^sub>2 where S: "S = S\<^sub>1 \<rightarrow> S\<^sub>2"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 T\<^sub>1' T\<^sub>2')
  from \<open>(LET p = t\<^sub>1 IN t\<^sub>2) \<in> value\<close>
  show ?case by cases
next
  case (T_Proj t fTs l T\<^sub>1 T\<^sub>2)
  from \<open>t..l \<in> value\<close>
  show ?case by cases
qed simp_all

lemma TyAll_canonical: \<comment> \<open>A.14(3)\<close>
  assumes ty: "[] \<turnstile> v : (\<forall><:T\<^sub>1. T\<^sub>2)"
  shows "v \<in> value \<Longrightarrow> \<exists>t S. v = (\<lambda><:S. t)" using ty
proof (induct "[]::env" v "\<forall><:T\<^sub>1. T\<^sub>2" arbitrary: T\<^sub>1 T\<^sub>2 rule: typing_induct)
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 t\<^sub>2 T\<^sub>1 T\<^sub>2)
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case T_TAbs
  show ?case by iprover
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 T\<^sub>1 T\<^sub>2')
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_Sub t S T\<^sub>1 T\<^sub>2)
  from \<open>[] \<turnstile> S <: (\<forall><:T\<^sub>1. T\<^sub>2)\<close>
  obtain S\<^sub>1 S\<^sub>2 where S: "S = (\<forall><:S\<^sub>1. S\<^sub>2)"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 T\<^sub>1' T\<^sub>2')
  from \<open>(LET p = t\<^sub>1 IN t\<^sub>2) \<in> value\<close>
  show ?case by cases
next
  case (T_Proj t fTs l T\<^sub>1 T\<^sub>2)
  from \<open>t..l \<in> value\<close>
  show ?case by cases
qed simp_all

text \<open>
Like in the case of the simple calculus,
we also need a canonical values theorem for record types:
\<close>

lemma RcdT_canonical: \<comment> \<open>A.14(2)\<close>
  assumes ty: "[] \<turnstile> v : RcdT fTs"
  shows "v \<in> value \<Longrightarrow>
    \<exists>fs. v = Rcd fs \<and> (\<forall>(l, t) \<in> set fs. t \<in> value)" using ty
proof (induct "[]::env" v "RcdT fTs" arbitrary: fTs rule: typing_induct)
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 t\<^sub>2 fTs)
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 fTs)
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_Sub t S fTs)
  from \<open>[] \<turnstile> S <: RcdT fTs\<close>
  obtain fTs' where S: "S = RcdT fTs'"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 fTs)
  from \<open>(LET p = t\<^sub>1 IN t\<^sub>2) \<in> value\<close>
  show ?case by cases
next
  case (T_Rcd fs fTs)
  from \<open>Rcd fs \<in> value\<close>
  show ?case using T_Rcd by cases simp_all
next
  case (T_Proj t fTs l fTs')
  from \<open>t..l \<in> value\<close>
  show ?case by cases
qed simp_all

theorem reorder_prop:
  "\<forall>(l, t) \<in> set fs. P t \<Longrightarrow> \<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<Longrightarrow>
     \<forall>(l, t) \<in> set (map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs). P t"
proof (induct fs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a fs)
  then show ?case
    by (smt (verit) assoc_set case_prod_unfold imageE list.set_map option.collapse
        option.simps(3))
qed

text \<open>
Another central property needed in the proof of the progress theorem is
that well-typed matching is defined.
This means that if the pattern @{term p} is compatible with the type @{term T} of
the closed term @{term t} that it has to match, then it is always possible to extract a
list of terms @{term ts} corresponding to the variables in @{term p}.
Interestingly, this important property is missing in the description of the
{\sc PoplMark} Challenge \<^cite>\<open>"PoplMark"\<close>.
\<close>

theorem ptyping_match:
  "\<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> [] \<turnstile> t : T \<Longrightarrow> t \<in> value \<Longrightarrow>
    \<exists>ts. \<turnstile> p \<rhd> t \<Rightarrow> ts"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> [] \<turnstile> fs [:] fTs \<Longrightarrow>
    \<forall>(l, t) \<in> set fs. t \<in> value \<Longrightarrow> \<exists>us. \<turnstile> fps [\<rhd>] fs \<Rightarrow> us"
proof (induct arbitrary: t and fs set: ptyping ptypings)
  case (P_Var T t)
  show ?case by (iprover intro: M_PVar)
next
  case (P_Rcd fps fTs \<Delta> t)
  then obtain fs where
    t: "t = Rcd fs" and fs: "\<forall>(l, t) \<in> set fs. t \<in> value"
    by (blast dest: RcdT_canonical)
  with P_Rcd have fs': "[] \<turnstile> Rcd fs : RcdT fTs" by simp
  hence "[] \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs [:] fTs"
    by (rule Rcd_type2')
  moreover from Rcd_type1' [OF fs']
  have assoc: "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor>" by blast
  with fs have "\<forall>(l, t) \<in> set (map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs). t \<in> value"
    by (rule reorder_prop)
  ultimately have "\<exists>us. \<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> us"
    by (rule P_Rcd)
  then obtain us where "\<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> us" ..
  with P_Rcd(1) assoc have "\<turnstile> fps [\<rhd>] fs \<Rightarrow> us" by (rule matchs_reorder')
  hence "\<turnstile> PRcd fps \<rhd> Rcd fs \<Rightarrow> us" by (rule M_Rcd)
  with t show ?case by fastforce
next
  case (P_Nil fs)
  show ?case by (iprover intro: M_Nil)
next
  case (P_Cons p T \<Delta>\<^sub>1 fps fTs \<Delta>\<^sub>2 l fs)
  from \<open>[] \<turnstile> fs [:] (l, T) \<Colon> fTs\<close>
  obtain t fs' where fs: "fs = (l, t) \<Colon> fs'" and t: "[] \<turnstile> t : T"
    and fs': "[] \<turnstile> fs' [:] fTs" by cases auto
  have "((l, t) \<Colon> fs')\<langle>l\<rangle>\<^sub>? = \<lfloor>t\<rfloor>" by simp
  moreover from fs P_Cons have "t \<in> value" by simp
  with t have "\<exists>ts. \<turnstile> p \<rhd> t \<Rightarrow> ts" by (rule P_Cons)
  then obtain ts where "\<turnstile> p \<rhd> t \<Rightarrow> ts" ..
  moreover from P_Cons fs have "\<forall>(l, t)\<in>set fs'. t \<in> value" by auto
  with fs' have "\<exists>us. \<turnstile> fps [\<rhd>] fs' \<Rightarrow> us" by (rule P_Cons)
  then obtain us where "\<turnstile> fps [\<rhd>] fs' \<Rightarrow> us" ..
  hence "\<turnstile> fps [\<rhd>] (l, t) \<Colon> fs' \<Rightarrow> us" using P_Cons(5) by (rule matchs_mono)
  ultimately have "\<turnstile> (l, p) \<Colon> fps [\<rhd>] (l, t) \<Colon> fs' \<Rightarrow> ts @ us"
    by (rule M_Cons)
  with fs show ?case by iprover
qed

theorem progress: \<comment> \<open>A.16\<close>
  "[] \<turnstile> t : T \<Longrightarrow> t \<in> value \<or> (\<exists>t'. t \<longmapsto> t')"
  "[] \<turnstile> fs [:] fTs \<Longrightarrow> (\<forall>(l, t) \<in> set fs. t \<in> value) \<or> (\<exists>fs'. fs [\<longmapsto>] fs')"
proof (induct "[]::env" t T and "[]::env" fs fTs set: typing typings)
  case T_Var
  thus ?case by simp
next
  case T_Abs
  from value.Abs show ?case ..
next
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 t\<^sub>2)
  hence "t\<^sub>1 \<in> value \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume t\<^sub>1_val: "t\<^sub>1 \<in> value"
    with T_App obtain t S where t\<^sub>1: "t\<^sub>1 = (\<lambda>:S. t)"
      by (auto dest!: Fun_canonical)
    from T_App have "t\<^sub>2 \<in> value \<or> (\<exists>t'. t\<^sub>2 \<longmapsto> t')" by simp
    thus ?thesis
    proof
      assume "t\<^sub>2 \<in> value"
      with t\<^sub>1 have "t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t[0 \<mapsto> t\<^sub>2]"
        by simp (rule eval_evals.intros)
      thus ?thesis by iprover
    next
      assume "\<exists>t'. t\<^sub>2 \<longmapsto> t'"
      then obtain t' where "t\<^sub>2 \<longmapsto> t'" by iprover
      with t\<^sub>1_val have "t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t\<^sub>1 \<bullet> t'" by (rule eval_evals.intros)
      thus ?thesis by iprover
    qed
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'"
    then obtain t' where "t\<^sub>1 \<longmapsto> t'" ..
    hence "t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t' \<bullet> t\<^sub>2" by (rule eval_evals.intros)
    thus ?thesis by iprover
  qed
next
  case T_TAbs
  from value.TAbs show ?case ..
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2)
  hence "t\<^sub>1 \<in> value \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume "t\<^sub>1 \<in> value"
    with T_TApp obtain t S where "t\<^sub>1 = (\<lambda><:S. t)"
      by (auto dest!: TyAll_canonical)
    hence "t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]" by simp (rule eval_evals.intros)
    thus ?thesis by iprover
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'"
    then obtain t' where "t\<^sub>1 \<longmapsto> t'" ..
    hence "t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t' \<bullet>\<^sub>\<tau> T\<^sub>2" by (rule eval_evals.intros)
    thus ?thesis by iprover
  qed
next
  case (T_Sub t S T)
  show ?case by (rule T_Sub)
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2)
  hence "t\<^sub>1 \<in> value \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume t\<^sub>1: "t\<^sub>1 \<in> value"
    with T_Let have "\<exists>ts. \<turnstile> p \<rhd> t\<^sub>1 \<Rightarrow> ts"
      by (auto intro: ptyping_match)
    with t\<^sub>1 show ?thesis by (blast intro: eval_evals.intros)
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'"
    thus ?thesis by (blast intro: eval_evals.intros)
  qed
next
  case (T_Rcd fs fTs)
  thus ?case by (blast intro: value.intros eval_evals.intros)
next
  case (T_Proj t fTs l T)
  hence "t \<in> value \<or> (\<exists>t'. t \<longmapsto> t')" by simp
  thus ?case
  proof
    assume tv: "t \<in> value"
    with T_Proj obtain fs where
      t: "t = Rcd fs" and fs: "\<forall>(l, t) \<in> set fs. t \<in> value"
      by (auto dest: RcdT_canonical)
    with T_Proj have "[] \<turnstile> Rcd fs : RcdT fTs" by simp
    hence "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> [] \<turnstile> u : U"
      by (rule Rcd_type1')
    with T_Proj obtain u where u: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor>" by (blast dest: assoc_set)
    with fs have "u \<in> value" by (blast dest: assoc_set)
    with u t show ?case by (blast intro: eval_evals.intros)
  next
    assume "\<exists>t'. t \<longmapsto> t'"
    thus ?case by (blast intro: eval_evals.intros)
  qed
next
  case T_Nil
  show ?case by simp
next
  case (T_Cons t T fs fTs l)
  thus ?case by (auto intro: eval_evals.intros)
qed

end
