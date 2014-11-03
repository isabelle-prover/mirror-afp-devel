(*  Title:       Tree Automata
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section "Trees"
theory Tree
imports Main
begin
text_raw {*\label{sec:tree}*}

text {*
  This theory defines trees as nodes with a label and a list of subtrees.
*}

datatype 'l tree = NODE 'l "'l tree list"

datatype_compat tree

end
