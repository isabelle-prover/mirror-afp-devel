(*
Copyright 2009-2014 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
header {* Testing Generator on Examples from AFP-Entry Datatype-Order-Generator *}

theory Show_Examples
imports
  "../Datatype_Order_Generator/Derive_Examples"
  Show_Instances
begin
  
subsection {* Without Nested Recursion *}

(* datatype_new 'a bintree = BEmpty | BNode "'a bintree" 'a "'a bintree" *)

derive "show" bintree

subsection {* Using Other Datatypes *}

(* datatype_new nat_list_list = NNil | CCons "nat list" nat_list_list *)

derive "show" nat_list_list

subsection {* Explicit Mutual Recursion *}

(*
datatype_new
  'a mtree = MEmpty | MNode 'a "'a mtree_list" and
  'a mtree_list = MNil | MCons "'a mtree" "'a mtree_list"
*)

derive "show" mtree

subsection {* Implicit mutual recursion *}

(*  datatype_new 'a tree = Empty | Node 'a "'a tree list"  *)

derive "show" tree

(* datatype_new 'a ttree = TEmpty | TNode 'a "'a ttree list tree" *)

derive "show" ttree

subsection {* Examples from IsaFoR *}

(* datatype_new ('f,'v) "term" = Var 'v | Fun 'f "('f,'v) term list" *)

derive "show" "term"

(*
datatype_new ('f, 'l) lab =
  Lab "('f, 'l) lab" 'l |
  FunLab "('f, 'l) lab" "('f, 'l) lab list" |
  UnLab 'f |
  Sharp "('f, 'l) lab"
*)

derive "show" lab

subsection {* A Complex Datatype *}

(*
datatype_new ('a, 'b) complex = 
  C1 nat "'a ttree" |
  C2 "('a, 'b) complex list tree tree" 'b "('a, 'b) complex" "('a, 'b) complex2 ttree list"
and ('a, 'b) complex2 = D1 "('a, 'b) complex ttree"

datatype_compat complex complex2
*)

derive "show" complex
  
end
