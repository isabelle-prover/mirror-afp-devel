(*  ID:         $Id: RegExp.thy,v 1.3 2004-04-19 22:30:44 lsf37 Exp $
    Author:     Tobias Nipkow
    License:    LGPL
    Copyright   1998 TUM
*)

header "Regular expressions"

theory RegExp = RegSet:

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
