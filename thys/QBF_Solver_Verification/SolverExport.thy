section \<open>Solver Export\<close>

theory SolverExport
  imports NaiveSolver PCNF SearchSolver Parser
    "HOL-Library.Code_Abstract_Char" "HOL-Library.Code_Target_Numeral" "HOL-Library.RBT_Set"
begin

fun run_naive_solver :: "String.literal \<Rightarrow> bool" where
  "run_naive_solver qdimacs_str = naive_solver (convert (the (parse qdimacs_str)))"

fun run_search_solver :: "String.literal \<Rightarrow> bool" where
  "run_search_solver qdimacs_str = search_solver (the (parse qdimacs_str))"

text \<open>Simple tests.\<close>

value "run_naive_solver (String.implode
''c an extension of the example from the QDIMACS specification
c multiple
c lines
cwith
c comments
p cnf 40 4
e 1 2 3 4 0
a 11 12 13 14 0
e 21 22 23 24 0
-1  2 0
2 -3 -4 0
40 -13 -24 0
12 -23 -24 0
'')"

value "run_search_solver (String.implode
''c an extension of the example from the QDIMACS specification
c multiple
c lines
cwith
c comments
p cnf 40 4
e 1 2 3 4 0
a 11 12 13 14 0
e 21 22 23 24 0
-1  2 0
2 -3 -4 0
40 -13 -24 0
12 -23 -24 0
'')"

value "parse (String.implode
''p cnf 7 12
e 1 2 3 4 5 6 7 0
-3 -1 0
3 1 0
-4 -2 0
4 2 0
-5 -1 -2 0
-5 1 2 0
5 -1 2 0
5 1 -2 0
6 -5 0
-6 5 0
7 0
-7 6 0
'')"

code_printing \<comment> \<open>This fixes an off-by-one error in the OCaml export.\<close>
  code_module "Str_Literal" \<rightharpoonup>
    (OCaml) \<open>module Str_Literal =
struct

let implode f xs =
  let rec length xs = match xs with
      [] -> 0
    | x :: xs -> 1 + length xs in
  let rec nth xs n = match xs with
    (x :: xs) -> if n <= 0 then x else nth xs (n - 1)
  in String.init (length xs) (fun n -> f (nth xs n));;

let explode f s =
  let rec map_range f lo hi =
    if lo >= hi then [] else f lo :: map_range f (lo + 1) hi
  in map_range (fun n -> f (String.get s n)) 0 (String.length s);;

let z_128 = Z.of_int 128;;

let check_ascii (k : Z.t) =
  if Z.leq Z.zero k && Z.lt k z_128
  then k
  else failwith "Non-ASCII character in literal";;

let char_of_ascii k = Char.chr (Z.to_int (check_ascii k));;

let ascii_of_char c = check_ascii (Z.of_int (Char.code c));;

let literal_of_asciis ks = implode char_of_ascii ks;;

let asciis_of_literal s = explode ascii_of_char s;;

end;;\<close> for constant String.literal_of_asciis String.asciis_of_literal

export_code
  run_naive_solver
  in SML file_prefix run_naive_solver

export_code
  run_naive_solver
  in OCaml file_prefix run_naive_solver

export_code
  run_naive_solver
  in Scala file_prefix run_naive_solver

export_code
  run_naive_solver
  in Haskell file_prefix run_naive_solver

export_code
  run_search_solver
  in SML file_prefix run_search_solver

export_code
  run_search_solver
  in OCaml file_prefix run_search_solver

export_code
  run_search_solver
  in Scala file_prefix run_search_solver

export_code
  run_search_solver
  in Haskell file_prefix run_search_solver

end