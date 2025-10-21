signature BEXP_PARSER = sig
    val bexp: string -> (string, int) Formula.bexp Error.res
    val guard: string -> (string, int) Syntax.guard Error.res
    val invariant: string -> (string, int) Syntax.invariant Error.res
    val update:
        string -> string Syntax.update Error.res
    val updates:
        string -> string Syntax.update list Error.res
    val formula:
        string -> (string, int) Syntax.formula Error.res
    val action:
        string -> string Syntax.action Error.res
    val var_bound:
        string -> Syntax.var Error.res

    val clocks: string -> string list Error.res
    val vars: string -> Syntax.var list Error.res
    val broadcast: string -> string Error.res
end


structure BexpParser : BEXP_PARSER = struct
open Syntax
open Symbol

val scan_var = Symbol.only_identifier
val single_c = ScannerCombinator.single_c
val infix_pairc = ScannerCombinator.infix_pairc

(* ********************************************************************** *)
(*                  scanning updates                                      *)
(* ********************************************************************** *)

fun mk_bound name x y =
    if x < y then {lower = x, name = name, upper = y}
    else {lower = y, name = name, upper = x}

val scan_bound =
    $$ "[" |-- (Symbol.strip_whitespace Symbol.integer) --|
       Symbol.strip_whitespace ($$ ":") --
       Symbol.strip_whitespace (Symbol.integer) --| $$ "]"

val scan_var_bound =
    scan_var -- Symbol.strip_whitespace scan_bound
        >> (fn (name,(l, u)) => mk_bound name l u)

(* ********************************************************************** *)
(*                  scanning actions                                      *)
(* ********************************************************************** *)

val scan_var_action = scan_var

fun scan_action' suffix constr =
    scan_var_action --| Scan.$$ suffix >> constr

val scan_action =
              ((scan_action' "?" In) ||
               (scan_action' "!" Out) ||
               (scan_var_action >> Internal))


(* ********************************************************************** *)
(*                  scanning guards and invariants                        *)
(* ********************************************************************** *)
fun scan_pairc_constr p sep = infix_pairc p natural sep
val scan_single = scan_var >> Difference.Single
val scan_diff = infix_pairc scan_var scan_var "-" Difference.Diff

fun scan_constraint_init sep = scan_pairc_constr (scan_diff || scan_single) sep
local
  open Constraint
in
fun scan_lt c =  scan_constraint_init "<" (Lt #> c)
fun scan_le c =  scan_constraint_init "<=" (Le #> c)
fun scan_eq c =  scan_constraint_init "=" (Eq #> c)
fun scan_ge c =  scan_constraint_init ">=" (Ge #> c)
fun scan_gt c =  scan_constraint_init ">" (Gt #> c)
end
fun scan_constraint c =
    (scan_lt c|| scan_le c || scan_eq c || scan_ge c || scan_gt c)

fun scan_constr_invar sep = scan_pairc_constr scan_var sep
val scan_lt_invar = scan_constr_invar "<" (Constraint.Lt #> Invariant.Constr)
val scan_le_invar = scan_constr_invar "<=" (Constraint.Le #> Invariant.Constr)
val scan_invar_constraint = (scan_lt_invar || scan_le_invar)


(* val scan_loc = scan_pairc scan_var scan_var *)
fun scan_parens inner = $$ "(" |-- Symbol.strip_whitespace inner --| $$ ")"

(* Adapted/ ported from Simon Wimmer's parser for the munta-frontend *)
(* ********************************************************************** *)
(*                              Invariants                                *)
(* ********************************************************************** *)

fun scan_bexp_constraints scan_bexp_elem = let
    fun scan_6 xs = (infix_pairc scan_0 scan_6 "&&" Invariant.And || scan_0) xs
    and scan_inner_bexp xs = scan_parens scan_6 xs
    and scan_prefix sep = single_c scan_6 sep
    and scan_0 xs =
        (
          (* scan_prefix "~" Not || *)
          scan_inner_bexp ||
          scan_bexp_elem
        ) xs
in Symbol.strip_whitespace scan_6 end

(* ********************************************************************** *)
(*                              Guards                                    *)
(* ********************************************************************** *)

fun scan_bexp_guards scan_bexp_elem = let
    fun scan_7 xs =
        (
          infix_pairc scan_6 scan_7 "||" Guard.Or ||
          scan_6
        ) xs
    and scan_6 xs = (infix_pairc scan_0 scan_6 "&&" Guard.And || scan_0) xs
    and scan_inner_bexp xs = scan_parens scan_7 xs
    and scan_prefix sep = single_c scan_7 sep
    and scan_0 xs =
        (
          (* XXX: Add not for guards ? *)
          (* scan_prefix "~" Not || *)
          scan_inner_bexp ||
          scan_bexp_elem
        ) xs
in Symbol.strip_whitespace scan_7 end



(* ********************************************************************** *)
(*                        scanning locations                              *)
(* ********************************************************************** *)

val scan_proc = Symbol.identifier
val scan_loc' = Symbol.identifier

val scan_loc = (scan_proc --| $$ "." -- scan_loc')
               >> Formula.Loc


(* ********************************************************************** *)
(*                              Formula                                   *)
(* ********************************************************************** *)

(* Adapted/ ported from Simon Wimmer's parser for the munta-frontend *)
fun scan_formula_pred scan_bexp_elem = let
    fun scan_7 xs =
        (
          infix_pairc scan_6 scan_7 "->" Formula.Impl ||
          infix_pairc scan_6 scan_7 "||" Formula.Or ||
          scan_6
        ) xs
    and scan_6 xs = (infix_pairc scan_0 scan_6 "&&" Formula.And || scan_0) xs
    and scan_inner_bexp xs = scan_parens scan_7 xs
    and scan_prefix sep = single_c scan_0 sep
    and scan_0 xs =
        (
          scan_bexp_elem ||
          scan_inner_bexp ||
          scan_prefix "!" Formula.Not ||
          scan_prefix "~" Formula.Not
        ) xs
in Symbol.strip_whitespace scan_7 end
(*
Maybe : Update for expressions
*)
val update_reset =
    infix_pairc scan_var Symbol.natural ":=" Reset
    || infix_pairc scan_var Symbol.natural "=" Reset
val update_copy =
    infix_pairc scan_var scan_var ":=" Copy
    || infix_pairc scan_var scan_var "=" Copy

val shift_plus = infix_pairc scan_var Symbol.natural "+" id

fun construct_shift (old , (new, inc)) =
    if old = new andalso inc >= 0 then Shift (old, inc)
    else Update (old, new, inc)

val update_shift =
    infix_pairc scan_var shift_plus ":=" construct_shift
    || infix_pairc scan_var shift_plus "=" construct_shift

val scan_update = (update_shift || update_reset || update_copy)

val action =  ParserUtil.safe_default "action" (Internal "") scan_action

val var_bound = ParserUtil.safe_scan "variable bound"  scan_var_bound

val update = ParserUtil.safe_scan "update (probably no whitespace)" scan_update

val bexp = ParserUtil.safe_default "bexp" Formula.True
                           (scan_formula_pred
                                (scan_constraint Formula.Pred || scan_loc))

val guard = ParserUtil.safe_default "guard" Guard.True
                                    (scan_bexp_guards (scan_constraint Guard.Constr))

val invariant =
    ParserUtil.safe_default "invariant" Invariant.True
                            (scan_bexp_constraints scan_invar_constraint)

val scan_bexp_elem = scan_formula_pred
                         (scan_constraint Formula.Pred || scan_loc)


val ex = single_c scan_bexp_elem "E<>" Formula.Ex
val eg = single_c scan_bexp_elem "E[]" Formula.Eg
val ax = single_c scan_bexp_elem "A<>" Formula.Ax
val ag = single_c scan_bexp_elem "A[]" Formula.Ag
val leadsto = infix_pairc scan_bexp_elem scan_bexp_elem "-->"
                               Formula.Leadsto

val scan_formula = (ex || eg || ax || ag || leadsto)

val formula = ParserUtil.safe_default "formula" (Formula.Ex Formula.True)
                                      scan_formula

fun parse_infix_lists err_msg p =
    ParserUtil.safe_scan
        err_msg
        (ScannerCombinator.infix_collection "," p)

fun vars str =
    parse_infix_lists "Variable Declaration" scan_var_bound str

fun clocks str =
    str
    |> parse_infix_lists "Clock Declaration" Symbol.identifier
    |> Either.bindR (fn [] => LangError.no_clocks
                              |> CompilationError.constr_err
                              |> Error.lift_comp_err |
                     clocks => Either.succeed clocks)

fun broadcast str =
    ParserUtil.safe_scan "Broadcast Channel declaration" scan_var str

fun updates str =
    parse_infix_lists "Updates" scan_update str
end
