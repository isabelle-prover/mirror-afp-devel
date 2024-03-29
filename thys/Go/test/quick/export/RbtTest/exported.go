package RbtTest

import (
  "isabelle/exported/Bigint"
)

// sum type which can be Red, Black
type Color any;
type Red struct { };
type Black struct { };



func Equal_colora (x0 Color, x1 Color) bool {
  {
    if x0 == (Color(Red{})) {
      if x1 == (Color(Black{})) {
        return false;
      }
    }
  };
  {
    if x0 == (Color(Black{})) {
      if x1 == (Color(Red{})) {
        return false;
      }
    }
  };
  {
    if x0 == (Color(Black{})) {
      if x1 == (Color(Black{})) {
        return true;
      }
    }
  };
  {
    if x0 == (Color(Red{})) {
      if x1 == (Color(Red{})) {
        return true;
      }
    }
  };
  panic("match failed");
}

type Equal[a any] struct {
  Equala func(a, a) bool
}

func Equal_color () Equal[Color] {
  return Equal[Color] {
    Equala: func  (A Color, Aa Color) bool { return Equal_colora(A, Aa); },
  }
}

type Prod[a, b any] struct { A a; Aa b; };
func Pair_dest[a, b any](p Prod[a, b])(a, b) {
  return  p.A, p.Aa;
}

func Eq[a any] (a_ Equal[a], aa a, b a) bool {
  return a_.Equala(aa, b);
}

func Equal_proda[a, b any] (a_ Equal[a], b_ Equal[b], x0 Prod[a, b], x1 Prod[a, b]) bool {
  {
    _ = x0;
    x1b, x2a := Pair_dest(x0);
    _ = x1;
    y1a, y2a := Pair_dest(x1);
    return Eq[a](a_, x1b, y1a) && Eq[b](b_, x2a, y2a);
  };
  panic("match failed");
}

func Equal_prod[a, b any] (a_ Equal[a], b_ Equal[b]) Equal[Prod[a, b]] {
  return Equal[Prod[a, b]] {
    Equala: func  (A Prod[a, b], Aa Prod[a, b]) bool { return Equal_proda[a, b](a_, b_, A, Aa); },
  }
}

func Equal_integer () Equal[Bigint.Int] {
  return Equal[Bigint.Int] {
    Equala: func  (A Bigint.Int, Aa Bigint.Int) bool { return Bigint.Equal( A, Aa); },
  }
}

type Ord[a any] struct {
  Less_eq func(a, a) bool
  Less func(a, a) bool
}

func Ord_integer () Ord[Bigint.Int] {
  return Ord[Bigint.Int] {
    Less_eq: func  (A Bigint.Int, Aa Bigint.Int) bool { return Bigint.Less_eq( A, Aa); },
    Less: func  (A Bigint.Int, Aa Bigint.Int) bool { return Bigint.Less( A, Aa); },
  }
}

type Preorder[a any] struct {
  Ord_preorder Ord[a]
}

type Order[a any] struct {
  Preorder_order Preorder[a]
}

func Preorder_integer () Preorder[Bigint.Int] {
  return Preorder[Bigint.Int] {
    Ord_preorder: Ord_integer(),
  }
}

func Order_integer () Order[Bigint.Int] {
  return Order[Bigint.Int] {
    Preorder_order: Preorder_integer(),
  }
}

type Linorder[a any] struct {
  Order_linorder Order[a]
}

func Linorder_integer () Linorder[Bigint.Int] {
  return Linorder[Bigint.Int] {
    Order_linorder: Order_integer(),
  }
}

// sum type which can be One, Bit0, Bit1
type Num any;
type One struct { };
type Bit0 struct { A Num; };
type Bit1 struct { A Num; };

func Bit0_dest(p Bit0)(Num) {
  return p.A
}
func Bit1_dest(p Bit1)(Num) {
  return p.A
}

// sum type which can be Nil, Cons
type List[a any] any;
type Nil[a any] struct { };
type Cons[a any] struct { A a; Aa List[a]; };

func Cons_dest[a any](p Cons[a])(a, List[a]) {
  return p.A, p.Aa
}

// sum type which can be Leaf, Node
type Tree[a any] any;
type Leaf[a any] struct { };
type Node[a any] struct { A Tree[a]; Aa a; Ab Tree[a]; };

func Node_dest[a any](p Node[a])(Tree[a], a, Tree[a]) {
  return p.A, p.Aa, p.Ab
}

// sum type which can be LT, EQ, GT
type Cmp_val any;
type LT struct { };
type EQ struct { };
type GT struct { };




func Cmp[a any] (a1_ Equal[a], a2_ Linorder[a], x a, y a) Cmp_val {
  target := a2_.Order_linorder.Preorder_order.Ord_preorder.Less(x, y);
  {
    if target == (true) {
      return Cmp_val(LT{});
    }
  };
  {
    if target == (false) {
      targeu := Eq[a](a1_, x, y);
      {
        if targeu == (true) {
          return Cmp_val(EQ{});
        }
      };
      {
        if targeu == (false) {
          return Cmp_val(GT{});
        }
      };
      panic("match failed");
    }
  };
  panic("match failed");
}

func Paint[a any] (c Color, x1 Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  {
    if x1 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      return Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{});
    }
  };
  {
    cb := c;
    q, m := x1.(Node[Prod[a, Color]]);
    if m {
      la, p, ra := Node_dest(q);
      _ = p;
      ab, _ := Pair_dest(p);
      return Tree[Prod[a, Color]](Node[Prod[a, Color]]{la, Prod[a, Color]{ab, cb}, ra});
    }
  };
  panic("match failed");
}

func BaliR[a any] (t1 Tree[Prod[a, Color]], aa a, x2 Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  {
    t1b := t1;
    ac := aa;
    q, m := x2.(Node[Prod[a, Color]]);
    if m {
      t2a, q, p := Node_dest(q);
      _ = q;
      ba, d := Pair_dest(q);
      if d == (Color(Red{})) {
        r, m := p.(Node[Prod[a, Color]]);
        if m {
          t3a, r, t4a := Node_dest(r);
          _ = r;
          ca, e := Pair_dest(r);
          if e == (Color(Red{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Black{})}, t2a}), Prod[a, Color]{ba, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t3a, Prod[a, Color]{ca, Color(Black{})}, t4a})});
          }
        }
      }
    }
  };
  {
    t1b := t1;
    ac := aa;
    q, m := x2.(Node[Prod[a, Color]]);
    if m {
      q, p, d := Node_dest(q);
      if d == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        r, m := q.(Node[Prod[a, Color]]);
        if m {
          t2a, r, t3a := Node_dest(r);
          _ = r;
          ba, e := Pair_dest(r);
          if e == (Color(Red{})) {
            _ = p;
            ca, f := Pair_dest(p);
            if f == (Color(Red{})) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Black{})}, t2a}), Prod[a, Color]{ba, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t3a, Prod[a, Color]{ca, Color(Black{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})})});
            }
          }
        }
      }
    }
  };
  {
    t1b := t1;
    ac := aa;
    q, m := x2.(Node[Prod[a, Color]]);
    if m {
      r, q, p := Node_dest(q);
      s, m := r.(Node[Prod[a, Color]]);
      if m {
        t2a, s, t3a := Node_dest(s);
        _ = s;
        ba, d := Pair_dest(s);
        if d == (Color(Red{})) {
          _ = q;
          ca, e := Pair_dest(q);
          if e == (Color(Red{})) {
            t, m := p.(Node[Prod[a, Color]]);
            if m {
              va, t, vba := Node_dest(t);
              _ = t;
              vca, f := Pair_dest(t);
              if f == (Color(Black{})) {
                return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Black{})}, t2a}), Prod[a, Color]{ba, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t3a, Prod[a, Color]{ca, Color(Black{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba})})});
              }
            }
          }
        }
      }
    }
  };
  {
    t1b := t1;
    ac := aa;
    if x2 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Black{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})});
    }
  };
  {
    t1b := t1;
    ac := aa;
    q, m := x2.(Node[Prod[a, Color]]);
    if m {
      va, p, vba := Node_dest(q);
      _ = p;
      vca, c := Pair_dest(p);
      if c == (Color(Black{})) {
        return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Black{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba})});
      }
    }
  };
  {
    t1b := t1;
    ac := aa;
    q, m := x2.(Node[Prod[a, Color]]);
    if m {
      d, vaa, c := Node_dest(q);
      if d == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) && c == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Black{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), vaa, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})})});
      }
    }
  };
  {
    t1b := t1;
    ac := aa;
    q, m := x2.(Node[Prod[a, Color]]);
    if m {
      p, vaa, c := Node_dest(q);
      if c == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        q, m := p.(Node[Prod[a, Color]]);
        if m {
          vba, q, vda := Node_dest(q);
          _ = q;
          vea, d := Pair_dest(q);
          if d == (Color(Black{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Black{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vba, Prod[a, Color]{vea, Color(Black{})}, vda}), vaa, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})})});
          }
        }
      }
    }
  };
  {
    t1b := t1;
    ac := aa;
    q, m := x2.(Node[Prod[a, Color]]);
    if m {
      c, vaa, p := Node_dest(q);
      if c == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        q, m := p.(Node[Prod[a, Color]]);
        if m {
          vca, q, vea := Node_dest(q);
          _ = q;
          vfa, d := Pair_dest(q);
          if d == (Color(Black{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Black{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), vaa, Tree[Prod[a, Color]](Node[Prod[a, Color]]{vca, Prod[a, Color]{vfa, Color(Black{})}, vea})})});
          }
        }
      }
    }
  };
  {
    t1b := t1;
    ac := aa;
    q, m := x2.(Node[Prod[a, Color]]);
    if m {
      q, vaa, p := Node_dest(q);
      r, m := q.(Node[Prod[a, Color]]);
      if m {
        vba, r, vga := Node_dest(r);
        _ = r;
        vha, c := Pair_dest(r);
        if c == (Color(Black{})) {
          s, m := p.(Node[Prod[a, Color]]);
          if m {
            vca, s, vea := Node_dest(s);
            _ = s;
            vfa, d := Pair_dest(s);
            if d == (Color(Black{})) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Black{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vba, Prod[a, Color]{vha, Color(Black{})}, vga}), vaa, Tree[Prod[a, Color]](Node[Prod[a, Color]]{vca, Prod[a, Color]{vfa, Color(Black{})}, vea})})});
            }
          }
        }
      }
    }
  };
  panic("match failed");
}

func BaldL[a any] (x0 Tree[Prod[a, Color]], b a, t3 Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      t1a, p, t2a := Node_dest(q);
      _ = p;
      ab, c := Pair_dest(p);
      if c == (Color(Red{})) {
        bb := b;
        t3b := t3;
        return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1a, Prod[a, Color]{ab, Color(Black{})}, t2a}), Prod[a, Color]{bb, Color(Red{})}, t3b});
      }
    }
  };
  {
    if x0 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      ab := b;
      q, m := t3.(Node[Prod[a, Color]]);
      if m {
        t2a, p, t3b := Node_dest(q);
        _ = p;
        bb, c := Pair_dest(p);
        if c == (Color(Black{})) {
          return BaliR[a](Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), ab, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t2a, Prod[a, Color]{bb, Color(Red{})}, t3b}));
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      va, p, vba := Node_dest(q);
      _ = p;
      vca, c := Pair_dest(p);
      if c == (Color(Black{})) {
        ab := b;
        q, m := t3.(Node[Prod[a, Color]]);
        if m {
          t2a, q, t3b := Node_dest(q);
          _ = q;
          bb, d := Pair_dest(q);
          if d == (Color(Black{})) {
            return BaliR[a](Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}), ab, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t2a, Prod[a, Color]{bb, Color(Red{})}, t3b}));
          }
        }
      }
    }
  };
  {
    if x0 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      ab := b;
      q, m := t3.(Node[Prod[a, Color]]);
      if m {
        q, p, t4a := Node_dest(q);
        r, m := q.(Node[Prod[a, Color]]);
        if m {
          t2a, r, t3b := Node_dest(r);
          _ = r;
          bb, d := Pair_dest(r);
          if d == (Color(Black{})) {
            _ = p;
            ca, e := Pair_dest(p);
            if e == (Color(Red{})) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ab, Color(Black{})}, t2a}), Prod[a, Color]{bb, Color(Red{})}, BaliR[a](t3b, ca, Paint[a](Color(Red{}), t4a))});
            }
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      va, p, vba := Node_dest(q);
      _ = p;
      vca, d := Pair_dest(p);
      if d == (Color(Black{})) {
        ab := b;
        q, m := t3.(Node[Prod[a, Color]]);
        if m {
          r, q, t4a := Node_dest(q);
          s, m := r.(Node[Prod[a, Color]]);
          if m {
            t2a, s, t3b := Node_dest(s);
            _ = s;
            bb, e := Pair_dest(s);
            if e == (Color(Black{})) {
              _ = q;
              ca, f := Pair_dest(q);
              if f == (Color(Red{})) {
                return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}), Prod[a, Color]{ab, Color(Black{})}, t2a}), Prod[a, Color]{bb, Color(Red{})}, BaliR[a](t3b, ca, Paint[a](Color(Red{}), t4a))});
              }
            }
          }
        }
      }
    }
  };
  {
    if x0 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      ab := b;
      if t3 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ab, Color(Red{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})});
      }
    }
  };
  {
    if x0 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      ab := b;
      q, m := t3.(Node[Prod[a, Color]]);
      if m {
        c, p, vba := Node_dest(q);
        if c == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
          _ = p;
          vca, d := Pair_dest(p);
          if d == (Color(Red{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ab, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{vca, Color(Red{})}, vba})});
          }
        }
      }
    }
  };
  {
    if x0 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      ab := b;
      q, m := t3.(Node[Prod[a, Color]]);
      if m {
        q, p, vba := Node_dest(q);
        r, m := q.(Node[Prod[a, Color]]);
        if m {
          vaa, r, vea := Node_dest(r);
          _ = r;
          vfa, c := Pair_dest(r);
          if c == (Color(Red{})) {
            _ = p;
            vca, d := Pair_dest(p);
            if d == (Color(Red{})) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ab, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vaa, Prod[a, Color]{vfa, Color(Red{})}, vea}), Prod[a, Color]{vca, Color(Red{})}, vba})});
            }
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      va, p, vba := Node_dest(q);
      _ = p;
      vca, c := Pair_dest(p);
      if c == (Color(Black{})) {
        ab := b;
        if t3 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
          return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}), Prod[a, Color]{ab, Color(Red{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})});
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      va, p, vba := Node_dest(q);
      _ = p;
      vca, c := Pair_dest(p);
      if c == (Color(Black{})) {
        ab := b;
        q, m := t3.(Node[Prod[a, Color]]);
        if m {
          d, q, vea := Node_dest(q);
          if d == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
            _ = q;
            vfa, e := Pair_dest(q);
            if e == (Color(Red{})) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}), Prod[a, Color]{ab, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{vfa, Color(Red{})}, vea})});
            }
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      va, p, vba := Node_dest(q);
      _ = p;
      vca, c := Pair_dest(p);
      if c == (Color(Black{})) {
        ab := b;
        q, m := t3.(Node[Prod[a, Color]]);
        if m {
          r, q, vea := Node_dest(q);
          s, m := r.(Node[Prod[a, Color]]);
          if m {
            vda, s, vha := Node_dest(s);
            _ = s;
            via, d := Pair_dest(s);
            if d == (Color(Red{})) {
              _ = q;
              vfa, e := Pair_dest(q);
              if e == (Color(Red{})) {
                return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}), Prod[a, Color]{ab, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vda, Prod[a, Color]{via, Color(Red{})}, vha}), Prod[a, Color]{vfa, Color(Red{})}, vea})});
              }
            }
          }
        }
      }
    }
  };
  panic("match failed");
}

func Join[a any] (x0 Tree[Prod[a, Color]], t Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  {
    if x0 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      tb := t;
      return tb;
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      vc, vaa, vba := Node_dest(q);
      if t == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        return Tree[Prod[a, Color]](Node[Prod[a, Color]]{vc, vaa, vba});
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      t1a, p, t2a := Node_dest(q);
      _ = p;
      ab, d := Pair_dest(p);
      if d == (Color(Red{})) {
        q, m := t.(Node[Prod[a, Color]]);
        if m {
          t3a, q, t4a := Node_dest(q);
          _ = q;
          ca, e := Pair_dest(q);
          if e == (Color(Red{})) {
            target := Join[a](t2a, t3a);
            {
              if target == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
                return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1a, Prod[a, Color]{ab, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ca, Color(Red{})}, t4a})});
              }
            };
            {
              r, m := target.(Node[Prod[a, Color]]);
              if m {
                u2, r, u3 := Node_dest(r);
                _ = r;
                b, f := Pair_dest(r);
                if f == (Color(Red{})) {
                  return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1a, Prod[a, Color]{ab, Color(Red{})}, u2}), Prod[a, Color]{b, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{u3, Prod[a, Color]{ca, Color(Red{})}, t4a})});
                }
              }
            };
            {
              r, m := target.(Node[Prod[a, Color]]);
              if m {
                u2, r, u3 := Node_dest(r);
                _ = r;
                b, f := Pair_dest(r);
                if f == (Color(Black{})) {
                  return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1a, Prod[a, Color]{ab, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{u2, Prod[a, Color]{b, Color(Black{})}, u3}), Prod[a, Color]{ca, Color(Red{})}, t4a})});
                }
              }
            };
            panic("match failed");
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      t1a, p, t2a := Node_dest(q);
      _ = p;
      ab, d := Pair_dest(p);
      if d == (Color(Black{})) {
        q, m := t.(Node[Prod[a, Color]]);
        if m {
          t3a, q, t4a := Node_dest(q);
          _ = q;
          ca, e := Pair_dest(q);
          if e == (Color(Black{})) {
            target := Join[a](t2a, t3a);
            {
              if target == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
                return BaldL[a](t1a, ab, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ca, Color(Black{})}, t4a}));
              }
            };
            {
              r, m := target.(Node[Prod[a, Color]]);
              if m {
                u2, r, u3 := Node_dest(r);
                _ = r;
                b, f := Pair_dest(r);
                if f == (Color(Red{})) {
                  return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1a, Prod[a, Color]{ab, Color(Black{})}, u2}), Prod[a, Color]{b, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{u3, Prod[a, Color]{ca, Color(Black{})}, t4a})});
                }
              }
            };
            {
              r, m := target.(Node[Prod[a, Color]]);
              if m {
                u2, r, u3 := Node_dest(r);
                _ = r;
                b, f := Pair_dest(r);
                if f == (Color(Black{})) {
                  return BaldL[a](t1a, ab, Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{u2, Prod[a, Color]{b, Color(Black{})}, u3}), Prod[a, Color]{ca, Color(Black{})}, t4a}));
                }
              }
            };
            panic("match failed");
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      va, p, vba := Node_dest(q);
      _ = p;
      vca, c := Pair_dest(p);
      if c == (Color(Black{})) {
        q, m := t.(Node[Prod[a, Color]]);
        if m {
          t2a, q, t3a := Node_dest(q);
          _ = q;
          ab, d := Pair_dest(q);
          if d == (Color(Red{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Join[a](Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}), t2a), Prod[a, Color]{ab, Color(Red{})}, t3a});
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      t1a, p, t2a := Node_dest(q);
      _ = p;
      ab, c := Pair_dest(p);
      if c == (Color(Red{})) {
        q, m := t.(Node[Prod[a, Color]]);
        if m {
          va, q, vba := Node_dest(q);
          _ = q;
          vca, d := Pair_dest(q);
          if d == (Color(Black{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1a, Prod[a, Color]{ab, Color(Red{})}, Join[a](t2a, Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}))});
          }
        }
      }
    }
  };
  panic("match failed");
}

func Fold[a, b any] (f func(a) func(b) b, x1 List[a], s b) b {
  {
    fb := f;
    q, m := x1.(Cons[a]);
    if m {
      xa, xsa := Cons_dest(q);
      sb := s;
      return Fold[a, b](fb, xsa, ((fb(xa))(sb)));
    }
  };
  {
    if x1 == (List[a](Nil[a]{})) {
      sb := s;
      return sb;
    }
  };
  panic("match failed");
}

func BaliL[a any] (x0 Tree[Prod[a, Color]], c a, t4 Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      q, p, t3a := Node_dest(q);
      r, m := q.(Node[Prod[a, Color]]);
      if m {
        t1a, r, t2a := Node_dest(r);
        _ = r;
        ab, d := Pair_dest(r);
        if d == (Color(Red{})) {
          _ = p;
          ba, e := Pair_dest(p);
          if e == (Color(Red{})) {
            cb := c;
            t4b := t4;
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1a, Prod[a, Color]{ab, Color(Black{})}, t2a}), Prod[a, Color]{ba, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t3a, Prod[a, Color]{cb, Color(Black{})}, t4b})});
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      d, q, p := Node_dest(q);
      if d == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        _ = q;
        ab, e := Pair_dest(q);
        if e == (Color(Red{})) {
          r, m := p.(Node[Prod[a, Color]]);
          if m {
            t2a, r, t3a := Node_dest(r);
            _ = r;
            ba, f := Pair_dest(r);
            if f == (Color(Red{})) {
              cb := c;
              t4b := t4;
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ab, Color(Black{})}, t2a}), Prod[a, Color]{ba, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t3a, Prod[a, Color]{cb, Color(Black{})}, t4b})});
            }
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      r, q, p := Node_dest(q);
      s, m := r.(Node[Prod[a, Color]]);
      if m {
        va, s, vba := Node_dest(s);
        _ = s;
        vca, d := Pair_dest(s);
        if d == (Color(Black{})) {
          _ = q;
          ab, e := Pair_dest(q);
          if e == (Color(Red{})) {
            t, m := p.(Node[Prod[a, Color]]);
            if m {
              t2a, t, t3a := Node_dest(t);
              _ = t;
              ba, f := Pair_dest(t);
              if f == (Color(Red{})) {
                cb := c;
                t4b := t4;
                return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}), Prod[a, Color]{ab, Color(Black{})}, t2a}), Prod[a, Color]{ba, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t3a, Prod[a, Color]{cb, Color(Black{})}, t4b})});
              }
            }
          }
        }
      }
    }
  };
  {
    if x0 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      ab := c;
      t2a := t4;
      return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ab, Color(Black{})}, t2a});
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      d, p, vba := Node_dest(q);
      if d == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        _ = p;
        va, e := Pair_dest(p);
        if e == (Color(Black{})) {
          ab := c;
          t2a := t4;
          return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{va, Color(Black{})}, vba}), Prod[a, Color]{ab, Color(Black{})}, t2a});
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      e, vaa, d := Node_dest(q);
      if e == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) && d == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        ab := c;
        t2a := t4;
        return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), vaa, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})}), Prod[a, Color]{ab, Color(Black{})}, t2a});
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      d, vaa, p := Node_dest(q);
      if d == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        q, m := p.(Node[Prod[a, Color]]);
        if m {
          vb, q, vda := Node_dest(q);
          _ = q;
          vea, e := Pair_dest(q);
          if e == (Color(Black{})) {
            ab := c;
            t2a := t4;
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), vaa, Tree[Prod[a, Color]](Node[Prod[a, Color]]{vb, Prod[a, Color]{vea, Color(Black{})}, vda})}), Prod[a, Color]{ab, Color(Black{})}, t2a});
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      q, p, vba := Node_dest(q);
      r, m := q.(Node[Prod[a, Color]]);
      if m {
        vca, r, vea := Node_dest(r);
        _ = r;
        vfa, d := Pair_dest(r);
        if d == (Color(Black{})) {
          _ = p;
          va, e := Pair_dest(p);
          if e == (Color(Black{})) {
            ab := c;
            t2a := t4;
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vca, Prod[a, Color]{vfa, Color(Black{})}, vea}), Prod[a, Color]{va, Color(Black{})}, vba}), Prod[a, Color]{ab, Color(Black{})}, t2a});
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      p, vaa, d := Node_dest(q);
      if d == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        q, m := p.(Node[Prod[a, Color]]);
        if m {
          vca, q, vea := Node_dest(q);
          _ = q;
          vfa, e := Pair_dest(q);
          if e == (Color(Black{})) {
            ab := c;
            t2a := t4;
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vca, Prod[a, Color]{vfa, Color(Black{})}, vea}), vaa, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})}), Prod[a, Color]{ab, Color(Black{})}, t2a});
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      q, vaa, p := Node_dest(q);
      r, m := q.(Node[Prod[a, Color]]);
      if m {
        vca, r, vea := Node_dest(r);
        _ = r;
        vfa, d := Pair_dest(r);
        if d == (Color(Black{})) {
          s, m := p.(Node[Prod[a, Color]]);
          if m {
            vb, s, vga := Node_dest(s);
            _ = s;
            vha, e := Pair_dest(s);
            if e == (Color(Black{})) {
              ab := c;
              t2a := t4;
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vca, Prod[a, Color]{vfa, Color(Black{})}, vea}), vaa, Tree[Prod[a, Color]](Node[Prod[a, Color]]{vb, Prod[a, Color]{vha, Color(Black{})}, vga})}), Prod[a, Color]{ab, Color(Black{})}, t2a});
            }
          }
        }
      }
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      va, p, vba := Node_dest(q);
      _ = p;
      vca, d := Pair_dest(p);
      if d == (Color(Black{})) {
        ab := c;
        t2a := t4;
        return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}), Prod[a, Color]{ab, Color(Black{})}, t2a});
      }
    }
  };
  panic("match failed");
}

func BaldR[a any] (t1 Tree[Prod[a, Color]], aa a, x2 Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  {
    t1b := t1;
    ac := aa;
    q, m := x2.(Node[Prod[a, Color]]);
    if m {
      t2a, p, t3a := Node_dest(q);
      _ = p;
      ba, c := Pair_dest(p);
      if c == (Color(Red{})) {
        return Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t2a, Prod[a, Color]{ba, Color(Black{})}, t3a})});
      }
    }
  };
  {
    q, m := t1.(Node[Prod[a, Color]]);
    if m {
      t1b, p, t2a := Node_dest(q);
      _ = p;
      ac, c := Pair_dest(p);
      if c == (Color(Black{})) {
        ba := aa;
        if x2 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
          return BaliL[a](Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Red{})}, t2a}), ba, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}));
        }
      }
    }
  };
  {
    q, m := t1.(Node[Prod[a, Color]]);
    if m {
      t1b, p, t2a := Node_dest(q);
      _ = p;
      ac, c := Pair_dest(p);
      if c == (Color(Black{})) {
        ba := aa;
        q, m := x2.(Node[Prod[a, Color]]);
        if m {
          va, q, vba := Node_dest(q);
          _ = q;
          vca, d := Pair_dest(q);
          if d == (Color(Black{})) {
            return BaliL[a](Tree[Prod[a, Color]](Node[Prod[a, Color]]{t1b, Prod[a, Color]{ac, Color(Red{})}, t2a}), ba, Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba}));
          }
        }
      }
    }
  };
  {
    q, m := t1.(Node[Prod[a, Color]]);
    if m {
      t1b, q, p := Node_dest(q);
      _ = q;
      ac, d := Pair_dest(q);
      if d == (Color(Red{})) {
        r, m := p.(Node[Prod[a, Color]]);
        if m {
          t2a, r, t3a := Node_dest(r);
          _ = r;
          ba, e := Pair_dest(r);
          if e == (Color(Black{})) {
            ca := aa;
            if x2 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{BaliL[a](Paint[a](Color(Red{}), t1b), ac, t2a), Prod[a, Color]{ba, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t3a, Prod[a, Color]{ca, Color(Black{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})})});
            }
          }
        }
      }
    }
  };
  {
    q, m := t1.(Node[Prod[a, Color]]);
    if m {
      t1b, q, p := Node_dest(q);
      _ = q;
      ac, d := Pair_dest(q);
      if d == (Color(Red{})) {
        r, m := p.(Node[Prod[a, Color]]);
        if m {
          t2a, r, t3a := Node_dest(r);
          _ = r;
          ba, e := Pair_dest(r);
          if e == (Color(Black{})) {
            ca := aa;
            s, m := x2.(Node[Prod[a, Color]]);
            if m {
              va, s, vba := Node_dest(s);
              _ = s;
              vca, f := Pair_dest(s);
              if f == (Color(Black{})) {
                return Tree[Prod[a, Color]](Node[Prod[a, Color]]{BaliL[a](Paint[a](Color(Red{}), t1b), ac, t2a), Prod[a, Color]{ba, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{t3a, Prod[a, Color]{ca, Color(Black{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba})})});
              }
            }
          }
        }
      }
    }
  };
  {
    if t1 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      ac := aa;
      if x2 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ac, Color(Red{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})});
      }
    }
  };
  {
    q, m := t1.(Node[Prod[a, Color]]);
    if m {
      va, p, c := Node_dest(q);
      if c == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        _ = p;
        vca, d := Pair_dest(p);
        if d == (Color(Red{})) {
          ac := aa;
          if x2 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Red{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})}), Prod[a, Color]{ac, Color(Red{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})});
          }
        }
      }
    }
  };
  {
    q, m := t1.(Node[Prod[a, Color]]);
    if m {
      vb, q, p := Node_dest(q);
      _ = q;
      vca, c := Pair_dest(q);
      if c == (Color(Red{})) {
        r, m := p.(Node[Prod[a, Color]]);
        if m {
          vaa, r, vea := Node_dest(r);
          _ = r;
          vfa, d := Pair_dest(r);
          if d == (Color(Red{})) {
            ac := aa;
            if x2 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vb, Prod[a, Color]{vca, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{vaa, Prod[a, Color]{vfa, Color(Red{})}, vea})}), Prod[a, Color]{ac, Color(Red{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})});
            }
          }
        }
      }
    }
  };
  {
    if t1 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      ac := aa;
      q, m := x2.(Node[Prod[a, Color]]);
      if m {
        va, p, vba := Node_dest(q);
        _ = p;
        vca, c := Pair_dest(p);
        if c == (Color(Black{})) {
          return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{ac, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{va, Prod[a, Color]{vca, Color(Black{})}, vba})});
        }
      }
    }
  };
  {
    q, m := t1.(Node[Prod[a, Color]]);
    if m {
      vaa, p, c := Node_dest(q);
      if c == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
        _ = p;
        vfa, d := Pair_dest(p);
        if d == (Color(Red{})) {
          ac := aa;
          q, m := x2.(Node[Prod[a, Color]]);
          if m {
            vd, q, vba := Node_dest(q);
            _ = q;
            vca, e := Pair_dest(q);
            if e == (Color(Black{})) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vaa, Prod[a, Color]{vfa, Color(Red{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})}), Prod[a, Color]{ac, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{vd, Prod[a, Color]{vca, Color(Black{})}, vba})});
            }
          }
        }
      }
    }
  };
  {
    q, m := t1.(Node[Prod[a, Color]]);
    if m {
      vaa, q, p := Node_dest(q);
      _ = q;
      vfa, c := Pair_dest(q);
      if c == (Color(Red{})) {
        r, m := p.(Node[Prod[a, Color]]);
        if m {
          vda, r, vha := Node_dest(r);
          _ = r;
          via, d := Pair_dest(r);
          if d == (Color(Red{})) {
            ac := aa;
            s, m := x2.(Node[Prod[a, Color]]);
            if m {
              ve, s, vba := Node_dest(s);
              _ = s;
              vca, e := Pair_dest(s);
              if e == (Color(Black{})) {
                return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Node[Prod[a, Color]]{vaa, Prod[a, Color]{vfa, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{vda, Prod[a, Color]{via, Color(Red{})}, vha})}), Prod[a, Color]{ac, Color(Red{})}, Tree[Prod[a, Color]](Node[Prod[a, Color]]{ve, Prod[a, Color]{vca, Color(Black{})}, vba})});
              }
            }
          }
        }
      }
    }
  };
  panic("match failed");
}

func Equal_tree[a any] (a_ Equal[a], x0 Tree[a], x1 Tree[a]) bool {
  {
    if x0 == (Tree[a](Leaf[a]{})) {
      _, m := x1.(Node[a]);
      if m {
        return false;
      }
    }
  };
  {
    _, m := x0.(Node[a]);
    if m {
      if x1 == (Tree[a](Leaf[a]{})) {
        return false;
      }
    }
  };
  {
    q, m := x0.(Node[a]);
    if m {
      x21a, x22a, x23a := Node_dest(q);
      q, m := x1.(Node[a]);
      if m {
        y21a, y22a, y23a := Node_dest(q);
        return Equal_tree[a](a_, x21a, y21a) && (Eq[a](a_, x22a, y22a) && Equal_tree[a](a_, x23a, y23a));
      }
    }
  };
  {
    if x0 == (Tree[a](Leaf[a]{})) {
      if x1 == (Tree[a](Leaf[a]{})) {
        return true;
      }
    }
  };
  panic("match failed");
}

func Colora[a any] (x0 Tree[Prod[a, Color]]) Color {
  {
    if x0 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      return Color(Black{});
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      _, p, _ := Node_dest(q);
      _ = p;
      _, ca := Pair_dest(p);
      return ca;
    }
  };
  panic("match failed");
}

func Del[a any] (a1_ Equal[a], a2_ Linorder[a], x a, xa1 Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  {
    if xa1 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      return Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{});
    }
  };
  {
    xb := x;
    q, m := xa1.(Node[Prod[a, Color]]);
    if m {
      la, p, ra := Node_dest(q);
      _ = p;
      ab, _ := Pair_dest(p);
      target := Cmp[a](a1_, a2_, xb, ab);
      {
        if target == (Cmp_val(LT{})) {
          targeu := ! Equal_tree[Prod[a, Color]](Equal_prod[a, Color](a1_, Equal_color()), la, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) && Equal_colora(Colora[a](la), Color(Black{}));
          {
            if targeu == (true) {
              return BaldL[a](Del[a](a1_, a2_, xb, la), ab, ra);
            }
          };
          {
            if targeu == (false) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Del[a](a1_, a2_, xb, la), Prod[a, Color]{ab, Color(Red{})}, ra});
            }
          };
          panic("match failed");
        }
      };
      {
        if target == (Cmp_val(EQ{})) {
          return Join[a](la, ra);
        }
      };
      {
        if target == (Cmp_val(GT{})) {
          targeu := ! Equal_tree[Prod[a, Color]](Equal_prod[a, Color](a1_, Equal_color()), ra, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) && Equal_colora(Colora[a](ra), Color(Black{}));
          {
            if targeu == (true) {
              return BaldR[a](la, ab, Del[a](a1_, a2_, xb, ra));
            }
          };
          {
            if targeu == (false) {
              return Tree[Prod[a, Color]](Node[Prod[a, Color]]{la, Prod[a, Color]{ab, Color(Red{})}, Del[a](a1_, a2_, xb, ra)});
            }
          };
          panic("match failed");
        }
      };
      panic("match failed");
    }
  };
  panic("match failed");
}

func Ins[a any] (a1_ Equal[a], a2_ Linorder[a], x a, xa1 Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  {
    xb := x;
    if xa1 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{}), Prod[a, Color]{xb, Color(Red{})}, Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})});
    }
  };
  {
    xb := x;
    q, m := xa1.(Node[Prod[a, Color]]);
    if m {
      la, p, ra := Node_dest(q);
      _ = p;
      ab, c := Pair_dest(p);
      if c == (Color(Black{})) {
        target := Cmp[a](a1_, a2_, xb, ab);
        {
          if target == (Cmp_val(LT{})) {
            return BaliL[a](Ins[a](a1_, a2_, xb, la), ab, ra);
          }
        };
        {
          if target == (Cmp_val(EQ{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{la, Prod[a, Color]{ab, Color(Black{})}, ra});
          }
        };
        {
          if target == (Cmp_val(GT{})) {
            return BaliR[a](la, ab, Ins[a](a1_, a2_, xb, ra));
          }
        };
        panic("match failed");
      }
    }
  };
  {
    xb := x;
    q, m := xa1.(Node[Prod[a, Color]]);
    if m {
      la, p, ra := Node_dest(q);
      _ = p;
      ab, c := Pair_dest(p);
      if c == (Color(Red{})) {
        target := Cmp[a](a1_, a2_, xb, ab);
        {
          if target == (Cmp_val(LT{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{Ins[a](a1_, a2_, xb, la), Prod[a, Color]{ab, Color(Red{})}, ra});
          }
        };
        {
          if target == (Cmp_val(EQ{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{la, Prod[a, Color]{ab, Color(Red{})}, ra});
          }
        };
        {
          if target == (Cmp_val(GT{})) {
            return Tree[Prod[a, Color]](Node[Prod[a, Color]]{la, Prod[a, Color]{ab, Color(Red{})}, Ins[a](a1_, a2_, xb, ra)});
          }
        };
        panic("match failed");
      }
    }
  };
  panic("match failed");
}

func Insert[a any] (a1_ Equal[a], a2_ Linorder[a], x a, t Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  return Paint[a](Color(Black{}), Ins[a](a1_, a2_, x, t));
}

func Empty[a any] () Tree[Prod[a, Color]] {
  return Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{});
}

func T1 () Tree[Prod[Bigint.Int, Color]] {
  return Fold[Bigint.Int, Tree[Prod[Bigint.Int, Color]]](func  (a Bigint.Int) func(Tree[Prod[Bigint.Int, Color]]) Tree[Prod[Bigint.Int, Color]] { return func  (b Tree[Prod[Bigint.Int, Color]]) Tree[Prod[Bigint.Int, Color]] { return Insert[Bigint.Int](Equal_integer(), Linorder_integer(), a, b); }; }, List[Bigint.Int](Cons[Bigint.Int]{Bigint.MkInt("1"), List[Bigint.Int](Cons[Bigint.Int]{Bigint.MkInt("2"), List[Bigint.Int](Cons[Bigint.Int]{Bigint.MkInt("3"), List[Bigint.Int](Cons[Bigint.Int]{Bigint.MkInt("4"), List[Bigint.Int](Cons[Bigint.Int]{Bigint.MkInt("5"), List[Bigint.Int](Nil[Bigint.Int]{})})})})})}), Empty[Bigint.Int]());
}

func Invc[a any] (x0 Tree[Prod[a, Color]]) bool {
  {
    if x0 == (Tree[Prod[a, Color]](Leaf[Prod[a, Color]]{})) {
      return true;
    }
  };
  {
    q, m := x0.(Node[Prod[a, Color]]);
    if m {
      la, p, ra := Node_dest(q);
      _ = p;
      _, ca := Pair_dest(p);
      return (!(Equal_colora(ca, Color(Red{}))) || Equal_colora(Colora[a](la), Color(Black{})) && Equal_colora(Colora[a](ra), Color(Black{}))) && (Invc[a](la) && Invc[a](ra));
    }
  };
  panic("match failed");
}

func Delete_list[a any] (a1_ Equal[a], a2_ Linorder[a], xs List[a], aa Tree[Prod[a, Color]]) Tree[Prod[a, Color]] {
  return Fold[a, Tree[Prod[a, Color]]](func  (ab a) func(Tree[Prod[a, Color]]) Tree[Prod[a, Color]] { return func  (b Tree[Prod[a, Color]]) Tree[Prod[a, Color]] { return Del[a](a1_, a2_, ab, b); }; }, xs, aa);
}

func Trees_equal[a any] (a_ Equal[a], aa Tree[Prod[a, Color]], b Tree[Prod[a, Color]]) bool {
  return Equal_tree[Prod[a, Color]](Equal_prod[a, Color](a_, Equal_color()), aa, b);
}

func Tree_from_list[a any] (a1_ Equal[a], a2_ Linorder[a], xs List[a]) Tree[Prod[a, Color]] {
  return Fold[a, Tree[Prod[a, Color]]](func  (aa a) func(Tree[Prod[a, Color]]) Tree[Prod[a, Color]] { return func  (b Tree[Prod[a, Color]]) Tree[Prod[a, Color]] { return Insert[a](a1_, a2_, aa, b); }; }, xs, Empty[a]());
}
