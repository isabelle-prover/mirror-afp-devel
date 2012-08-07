theory Order_Generator_Examples
imports Order_Generator
begin

section Examples

subsection "Register standard existing types"

derive_order "list"
derive_order "sum"
derive_order "prod"

subsection "Without nested recursion"

datatype 'a bintree = BEmpty | BNode "'a bintree" 'a "'a bintree"
derive_order "bintree"

subsection "Using other datatypes"

datatype nat_list_list = NNil | CCons "nat list" nat_list_list
derive_order "nat_list_list"

subsection "Explicit mutual recursion"

datatype 'a mtree = MEmpty | MNode "'a mtree_list"
  and 'a mtree_list = MNil | MCons "'a mtree" "'a mtree_list"
derive_order "mtree"

subsection "Implicit mutual recursion"

datatype 'a tree = Empty | Node "'a tree list"
derive_order "tree"

datatype 'a ttree = TEmpty | TNode "'a ttree list tree"
derive_order "ttree"

subsection "Examples from IsaFoR"

datatype ('f,'v)"term" = Var 'v | Fun 'f "('f,'v)term list"
datatype ('f, 'l) lab =
  Lab "('f, 'l) lab" 'l
| FunLab "('f, 'l) lab" "('f, 'l) lab list"
| UnLab 'f
| Sharp "('f, 'l) lab"
derive_order "term"
derive_order "lab"

subsection "Unsupported datatypes"

text {*
All of the examples can be handled if one occurence of \texttt{list} is dropped.
*}

datatype problem1 = A1 | B1 "problem1 list list list"
(* derive_order "problem1" *)

datatype problem2 = A2 | B2 "problem2 list list" "problem2"
(* derive_order "problem2" *)

datatype problem3 = A3 | B3 "problem3 list" "problem3 list" "problem3 list"
(* derive_order "problem3" *)

end
