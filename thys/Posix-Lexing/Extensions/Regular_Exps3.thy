(* Adapted from Tobias Nipkow in order to accommodate 
   bounded regular expressions *)

section "Extended Regular Expressions 3"

theory Regular_Exps3
imports "Regular-Sets.Regular_Set"
begin

datatype (atoms: 'a) rexp =
  is_Zero: Zero |
  is_One: One |
  Atom 'a |
  Plus "('a rexp)" "('a rexp)" |
  Times "('a rexp)" "('a rexp)" |
  Star "('a rexp)" |
  NTimes "('a rexp)" "nat" | (* r{n}    - exactly n-times *)
  Upto "('a rexp)" "nat" |   (* r{..n}  - up to n-times *) 
  From "('a rexp)" "nat" |   (* r{n..}  - from n-times *) 
  Rec string "('a rexp)" |  (* record regular expression *)
  Charset "('a set)"

fun lang :: "'a rexp => 'a lang" where
"lang Zero = {}" |
"lang One = {[]}" |
"lang (Atom a) = {[a]}" |
"lang (Plus r s) = (lang r) Un (lang s)" |
"lang (Times r s) = conc (lang r) (lang s)" |
"lang (Star r) = star(lang r)" |
"lang (NTimes r n) = ((lang r) ^^ n)" | 
"lang (Upto r n) = (\<Union>i \<in> {..n}. (lang r) ^^ i)" |
"lang (From r n) = (\<Union>i \<in> {n..}. (lang r) ^^ i)" |
"lang (Rec l r) = lang r" |
"lang (Charset cs) = {[c] | c . c \<in> cs}"


primrec nullable :: "'a rexp \<Rightarrow> bool" where
"nullable Zero = False" |
"nullable One = True" |
"nullable (Atom c) = False" |
"nullable (Plus r1 r2) = (nullable r1 \<or> nullable r2)" |
"nullable (Times r1 r2) = (nullable r1 \<and> nullable r2)" |
"nullable (Star r) = True" |
"nullable (NTimes r n) = (if n = 0 then True else nullable r)" |
"nullable (Upto r n) = True" |
"nullable (From r n) = (if n = 0 then True else nullable r)" |
"nullable (Rec l r) = nullable r" |
"nullable (Charset cs) = False"

lemma pow_empty_iff:
  shows "[] \<in> (lang r) ^^ n \<longleftrightarrow> (if n = 0 then True else [] \<in> (lang r))"
  by (induct n)(auto)

lemma nullable_iff: 
  shows "nullable r \<longleftrightarrow> [] \<in> lang r"
  by (induct r) (auto simp add: conc_def pow_empty_iff split: if_splits)

end
