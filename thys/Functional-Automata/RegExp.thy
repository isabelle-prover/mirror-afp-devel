(*  ID:         $Id: RegExp.thy,v 1.5 2004-08-19 10:54:14 nipkow Exp $
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

header "Regular expressions"

theory RegExp
imports RegSet
begin

datatype 'a rexp = Empty
                 | Atom 'a
                 | Or   "('a rexp)" "('a rexp)"
                 | Conc "('a rexp)" "('a rexp)"
                 | Star "('a rexp)"

consts lang :: "'a rexp => 'a list set"
primrec
"lang Empty = {}"
"lang (Atom a) = {[a]}"
"lang (Or el er) = (lang el) Un (lang er)"
"lang (Conc el er) = RegSet.conc (lang el) (lang er)"
"lang (Star e) = RegSet.star(lang e)"

end
