theory Go_Setup
  imports "Main"
begin

ML_file \<open>code_go.ML\<close>

code_identifier
  code_module Code_Target_Nat \<rightharpoonup> (Go) Arith
| code_module Code_Target_Int \<rightharpoonup> (Go) Arith
| code_module Code_Numeral \<rightharpoonup> (Go) Arith

code_printing
  constant Code.abort \<rightharpoonup>
    (Go) "panic( _ )"

(* Bools *)
code_printing
  type_constructor bool \<rightharpoonup> (Go) "bool"
| constant "False::bool" \<rightharpoonup> (Go) "false"
| constant "True::bool" \<rightharpoonup> (Go) "true"

code_printing
  constant HOL.Not \<rightharpoonup> (Go) "'! _"
| constant HOL.conj \<rightharpoonup> (Go) infixl 1 "&&"
| constant HOL.disj \<rightharpoonup> (Go) infixl 0 "||"
| constant HOL.implies \<rightharpoonup> (Go) "!('!((_)) || (_))"
| constant "HOL.equal :: bool \<Rightarrow> bool \<Rightarrow> bool" \<rightharpoonup> (Go) infix 4 "=="


(* Strings *)

(* definitions to make these functions available *)
definition "go_private_map_list" where
  "go_private_map_list f a = map f a"
definition "go_private_fold_list" where
  "go_private_fold_list f a b = fold f a b"


code_printing
  type_constructor String.literal \<rightharpoonup> (Go) "string"
| constant "STR ''''" \<rightharpoonup> (Go) "\"\""
| constant "Groups.plus_class.plus :: String.literal \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (Go) infix 6 "+"
| constant "HOL.equal :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool" \<rightharpoonup>
    (Go) infix 4 "=="
| constant "(\<le>) :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool" \<rightharpoonup>
    (Go) infix 4 "<="
| constant "(<) :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool" \<rightharpoonup>
    (Go) infix 4 "<"

setup \<open>
  fold Literal.add_code ["Go"]
\<close>


(* Integers via big/math *)
code_printing
  code_module "Bigint" \<rightharpoonup> (Go) \<open>
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
\<close> for constant "uminus :: integer \<Rightarrow> _" "minus :: integer \<Rightarrow> _" "Code_Numeral.dup" "Code_Numeral.sub"
  "(*) :: integer \<Rightarrow> _" "(+) :: integer \<Rightarrow> _" "Code_Numeral.divmod_abs" "HOL.equal :: integer \<Rightarrow> _"
  "less_eq :: integer \<Rightarrow> _" "less :: integer \<Rightarrow> _" "abs :: integer \<Rightarrow> _"
  "String.literal_of_asciis" "String.asciis_of_literal"
  | type_constructor "integer" \<rightharpoonup> (Go) "Bigint.Int"
  | constant "uminus :: integer \<Rightarrow> integer" \<rightharpoonup> (Go) "Bigint.Uminus( _ )"
  | constant "minus :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup> (Go) "Bigint.Minus( _, _)"
  | constant "Code_Numeral.dup" \<rightharpoonup> (Go) "!(Bigint.MkInt(\"2\") * _)"
  | constant "Code_Numeral.sub" \<rightharpoonup> (Go) "panic(\"sub\")"
  | constant "(+) :: integer \<Rightarrow> _ " \<rightharpoonup> (Go) "Bigint.Plus( _, _)"
  | constant "(*) :: integer \<Rightarrow> _ \<Rightarrow> _ " \<rightharpoonup> (Go) "Bigint.Times( _, _)"
  | constant Code_Numeral.divmod_abs \<rightharpoonup>
     (Go) "func () Prod[Bigint.Int, Bigint.Int] { a, b := Bigint.Divmod'_abs( _, _); return Prod[Bigint.Int, Bigint.Int]{a, b}; }()"
  | constant "HOL.equal :: integer \<Rightarrow> _" \<rightharpoonup> (Go) "Bigint.Equal( _, _)"
  | constant "less_eq :: integer \<Rightarrow> integer \<Rightarrow> bool " \<rightharpoonup> (Go) "Bigint.Less'_eq( _, _)"
  | constant "less :: integer \<Rightarrow> _ " \<rightharpoonup> (Go) "Bigint.Less( _, _)"
  | constant "abs :: integer \<Rightarrow> _" \<rightharpoonup> (Go) "Bigint.Abs( _ )"


code_printing
  constant "0::integer" \<rightharpoonup> (Go) "Bigint.MkInt(\"0\")"
setup \<open>
Numeral.add_code \<^const_name>\<open>Code_Numeral.Pos\<close> I Code_Printer.literal_numeral "Go"
#> Numeral.add_code \<^const_name>\<open>Code_Numeral.Neg\<close> (~) Code_Printer.literal_numeral "Go"
\<close>

end