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

fun map_rexp :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a rexp \<Rightarrow> 'b rexp" where
"map_rexp f Zero = Zero" |
"map_rexp f One = One" |
"map_rexp f (Atom a) = Atom(f a)" |
"map_rexp f (Plus r s) = Plus (map_rexp f r) (map_rexp f s) " |
"map_rexp f (Times r s) = Times (map_rexp f r) (map_rexp f s) " |
"map_rexp f (Star r) = Star(map_rexp f r)"


lemma nullable_iff: "nullable r \<longleftrightarrow> [] \<in> lang r"
by (induct r) (auto simp add: conc_def split: if_splits)

text{* Composition on rhs usually complicates matters: *}
lemma map_map_rexp:
  "map_rexp f (map_rexp g r) = map_rexp (\<lambda>r. f (g r)) r"
by (induction r) auto

lemma map_rexp_ident[simp]: "map_rexp (\<lambda>x. x) = (\<lambda>r. r)"
by (rule ext, induct_tac r) auto

end
