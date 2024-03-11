package rbt

import "isabelle/exported/RbtTest"

var T1 = RbtTest.T1()

var LinorderInt = RbtTest.Linorder_integer()
var EqualInt = RbtTest.Equal_integer()

func EmptyTree[a any]() RbtTest.Tree[RbtTest.Prod[a, RbtTest.Color]] {
	return RbtTest.Empty[a]()
}

func JoinAndCheck[a any](a_ RbtTest.Linorder[a], x, y RbtTest.Tree[RbtTest.Prod[a, RbtTest.Color]]) (RbtTest.Tree[RbtTest.Prod[a, RbtTest.Color]], bool) {
	b := RbtTest.Join(x, y)
	ok := RbtTest.Invc(b)
	return b, ok
}

func DelAndCheck[a any](eq RbtTest.Equal[a], lin RbtTest.Linorder[a], list RbtTest.List[a], x RbtTest.Tree[RbtTest.Prod[a, RbtTest.Color]]) (RbtTest.Tree[RbtTest.Prod[a, RbtTest.Color]], bool) {
	b := RbtTest.Delete_list(eq, lin, list, x)
	ok := RbtTest.Invc(b)
	return b, ok
}

func TreeFromList[a any](eq RbtTest.Equal[a], lin RbtTest.Linorder[a], xs RbtTest.List[a]) (RbtTest.Tree[RbtTest.Prod[a, RbtTest.Color]], bool) {
	tree := RbtTest.Tree_from_list(eq, lin, xs)
	ok := RbtTest.Invc(tree)
	return tree, ok
}

func MkList[a any](vec []a) RbtTest.List[a] {
	list := RbtTest.List[a](RbtTest.Nil[a]{})
	for _, v := range vec {
		list = RbtTest.List[a](RbtTest.Cons[a]{v, list})
	}
	return list
}

func TreesEqual[a any](eq RbtTest.Equal[a], x, y RbtTest.Tree[RbtTest.Prod[a, RbtTest.Color]]) bool {
	return RbtTest.Trees_equal(eq, x, y)
}
