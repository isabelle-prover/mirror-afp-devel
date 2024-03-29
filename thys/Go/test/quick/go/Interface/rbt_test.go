package rbt

import (
	"reflect"
	"testing"

	"isabelle/exported/Bigint"
	"isabelle/exported/RbtTest"
)

type RBTBigInt = RbtTest.Prod[Bigint.Int, RbtTest.Color]

func TestTreeFromList(t *testing.T) {
	array := [5]Bigint.Int{Bigint.MkInt("1"), Bigint.MkInt("2"), Bigint.MkInt("3"), Bigint.MkInt("4"), Bigint.MkInt("5")}
	elements := MkList(array[:])

	got, ok := TreeFromList(EqualInt, LinorderInt, elements)
	if !ok {
		t.Fatal("new tree does not satisfy invariant")
	}

	want := RbtTest.Node[RBTBigInt]{
		A: RbtTest.Node[RBTBigInt]{
			A: RbtTest.Node[RBTBigInt]{
				A: RbtTest.Leaf[RBTBigInt]{},
				Aa: RBTBigInt{A: Bigint.MkInt("1"),
					Aa: RbtTest.Black{},
				},
				Ab: RbtTest.Leaf[RBTBigInt]{},
			},
			Aa: RBTBigInt{
				A:  Bigint.MkInt("2"),
				Aa: RbtTest.Red{},
			},
			Ab: RbtTest.Node[RBTBigInt]{
				A: RbtTest.Leaf[RBTBigInt]{},
				Aa: RBTBigInt{A: Bigint.MkInt("3"),
					Aa: RbtTest.Black{}},
				Ab: RbtTest.Leaf[RBTBigInt]{},
			},
		},
		Aa: RBTBigInt{
			A:  Bigint.MkInt("4"),
			Aa: RbtTest.Black{},
		},
		Ab: RbtTest.Node[RBTBigInt]{
			A: RbtTest.Leaf[RBTBigInt]{},
			Aa: RBTBigInt{
				A:  Bigint.MkInt("5"),
				Aa: RbtTest.Black{},
			},
			Ab: RbtTest.Leaf[RBTBigInt]{},
		},
	}

	if !reflect.DeepEqual(got, want) {
		t.Fatalf("got tree does not equal want tree")
	}
}

func TestJoinAndCheck(t *testing.T) {
	list := MkList([]Bigint.Int{Bigint.MkInt("1"), Bigint.MkInt("2"), Bigint.MkInt("3"), Bigint.MkInt("4"), Bigint.MkInt("5")})

	tree, ok := TreeFromList(EqualInt, LinorderInt, list)
	if !ok {
		t.Fatal("new tree does not satisfy invariant")
	}
	_, ok = JoinAndCheck(LinorderInt, tree, tree)
	if !ok {
		t.Fatal("joining trees violated invariant")
	}
}

func TestDelAndCheck(t *testing.T) {
	list := MkList([]Bigint.Int{Bigint.MkInt("1"), Bigint.MkInt("2"), Bigint.MkInt("3"), Bigint.MkInt("4"), Bigint.MkInt("5")})

	tree, ok := TreeFromList(EqualInt, LinorderInt, list)
	if !ok {
		t.Fatal("new tree does not satisfy invariant")
	}
	got, ok := DelAndCheck(EqualInt, LinorderInt, list, tree)
	if !ok {
		t.Fatal("deletion violated invariant")
	}
	want := EmptyTree[Bigint.Int]()
	ok = TreesEqual(EqualInt, got, want)
	if !ok {
		t.Fatal("tree not empty after deletion")
	}
}
