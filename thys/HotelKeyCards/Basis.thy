(*  Title:      Basis for hotel key card system
    ID:         $Id: Basis.thy,v 1.1 2006-09-06 20:41:24 nipkow Exp $
    Author:     Tobias Nipkow, TU Muenchen
*)

theory Basis
imports Notation
begin

typedecl guest
typedecl key
typedecl room

type_synonym card = "key * key"

end