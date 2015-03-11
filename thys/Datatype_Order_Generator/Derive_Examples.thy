section Examples

theory Derive_Examples
imports 
  Derive
  "Comparator_Generator/Compare_Order_Instances"
  Rat
begin

subsection "Register standard existing types"

derive (linorder) compare_order rat

subsection "Without nested recursion"

datatype 'a bintree = BEmpty | BNode "'a bintree" 'a "'a bintree"

derive compare_order bintree
derive countable bintree

subsection "Using other datatypes"

datatype nat_list_list = NNil | CCons "nat list" nat_list_list

derive compare_order nat_list_list
derive countable nat_list_list

subsection "Explicit mutual recursion"

datatype
  'a mtree = MEmpty | MNode 'a "'a mtree_list" and
  'a mtree_list = MNil | MCons "'a mtree" "'a mtree_list"

derive compare_order mtree
derive countable mtree

subsection "Implicit mutual recursion"

datatype 'a tree = Empty | Node 'a "'a tree list"
datatype 'a ttree = TEmpty | TNode 'a "'a ttree list tree"

derive compare_order tree ttree
derive countable tree ttree

subsection "Examples from IsaFoR"

datatype ('f,'v) "term" = Var 'v | Fun 'f "('f,'v) term list"
datatype ('f, 'l) lab =
  Lab "('f, 'l) lab" 'l
| FunLab "('f, 'l) lab" "('f, 'l) lab list"
| UnLab 'f
| Sharp "('f, 'l) lab"

derive compare_order "term" lab
derive countable "term" lab

subsection "A complex datatype"
text {*
The following datatype has nested indirect recursion, mutual recursion and
uses other datatypes.
*}

datatype ('a, 'b) complex = 
  C1 nat "'a ttree" |
  C2 "('a, 'b) complex list tree tree" 'b "('a, 'b) complex" "('a, 'b) complex2 ttree list"
and ('a, 'b) complex2 = D1 "('a, 'b) complex ttree"

derive compare_order complex
derive countable complex

end
