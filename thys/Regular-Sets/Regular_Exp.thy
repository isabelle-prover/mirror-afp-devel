(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

header "Regular expressions"

theory Regular_Exp
imports Regular_Set
begin

datatype 'a rexp =
  Zero |
  One |
  Atom 'a |
  Plus "('a rexp)" "('a rexp)" |
  Times "('a rexp)" "('a rexp)" |
  Star "('a rexp)"

primrec lang :: "'a rexp => 'a lang" where
"lang Zero = {}" |
"lang One = {[]}" |
"lang (Atom a) = {[a]}" |
"lang (Plus r s) = (lang r) Un (lang s)" |
"lang (Times r s) = conc (lang r) (lang s)" |
"lang (Star r) = star(lang r)"

primrec atoms :: "'a rexp \<Rightarrow> 'a set" where
"atoms Zero = {}" |
"atoms One = {}" |
"atoms (Atom a) = {a}" |
"atoms (Plus r s) = atoms r \<union> atoms s" |
"atoms (Times r s) = atoms r \<union> atoms s" |
"atoms (Star r) = atoms r"

primrec nullable :: "'a rexp \<Rightarrow> bool" where
"nullable (Zero) = False" |
"nullable (One) = True" |
"nullable (Atom c) = False" |
"nullable (Plus r1 r2) = (nullable r1 \<or> nullable r2)" |
"nullable (Times r1 r2) = (nullable r1 \<and> nullable r2)" |
"nullable (Star r) = True"

lemma nullable_iff: "nullable r \<longleftrightarrow> [] \<in> lang r"
by (induct r) (auto simp add: conc_def split: if_splits)

end
