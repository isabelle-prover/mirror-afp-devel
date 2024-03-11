
package Bigint

import "math/big"

type Int = big.Int;

func MkInt(s string) Int {
  var i Int;
  _, e := i.SetString(s, 10);
  if (e) {
    return i;
  } else {
    panic("invalid integer literal")
  }
}

func Uminus(a Int) Int {
  var b Int
  b.Neg(&a)
  return b
}

func Minus(a, b Int) Int {
  var c Int
  c.Sub(&a, &b)
  return c
}

func Plus(a, b Int) Int {
  var c Int
  c.Add(&a, &b)
  return c
}

func Times (a, b Int) Int {
  var c Int
  c.Mul(&a, &b)
  return c
}

func Divmod_abs(a, b Int) (Int, Int) {
  var div, mod Int
  div.DivMod(&a, &b, &mod)
  div.Abs(&div)
  return div, mod
}

func Equal(a, b Int) bool {
  return a.Cmp(&b) == 0
}

func Less_eq(a, b Int) bool {
  return a.Cmp(&b) != 1
}

func Less(a, b Int) bool {
  return a.Cmp(&b) == -1
}

func Abs(a Int) Int {
  var b Int
  b.Abs(&a)
  return b
}

