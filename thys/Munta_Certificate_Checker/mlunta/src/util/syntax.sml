structure Syntax = struct
structure Difference = struct
datatype 'a clock_pair =
             Single of 'a |
             Diff of 'a * 'a

fun to_string e =
    case e of
        Single id => id |
        Diff (x, y) => x ^ " - " ^ y

fun pred_clk_pair comb p c =
    case c of
            Single x => p x |
            Diff (l, r) => comb (p l, p r)

fun exists p = pred_clk_pair (fn (l, r) => l orelse r) p
fun all p = pred_clk_pair (fn (l, r) => l andalso r) p

fun is_diff c =
    case c of
        Single _ => false |
        _ => true

fun is_single c = c |> is_diff |> not
local
  open Either
in

fun check f cc_single cc_diff e =
    case e of
        Single x => f x >>= cc_single |
        Diff (x, y) => (f x <|> f y) >>= cc_diff
end
end

structure Exp = struct
datatype 'a clock_var =
             Cexp of 'a |
             Vexp of 'a

fun is_cexp e =
    case e of
            (Cexp _) => true |
            _ => false

fun is_vexp e = e |> is_cexp |> not

fun the_cexp e =
    case e of
            (Cexp x) => x |
            _ => Exn.error "This is not an cexp"

fun the_vexp e =
    case e of
            (Vexp x) => x |
            _ => Exn.error "This is not an vexp"

fun get_exp exp =
    case exp of
        Cexp e => e |
        Vexp e => e

fun map f e =
    case e of
        Vexp e' => Vexp (f e') |
        Cexp e' => Cexp (f e')

fun join error (e, e') =
    case (e, e') of
        (Cexp e, Cexp e') => Either.succeed (Cexp (e, e')) |
        (Vexp e, Vexp e') => Either.succeed (Vexp (e, e')) |
        (Cexp e, Vexp e') => error e e' |
        (Vexp e, Cexp e') => error e' e

end
structure Constraint = struct
datatype ('a, 'b) constraint =
         Eq of 'a * 'b |
         Le of 'a * 'b |
         Lt of 'a * 'b |
         Ge of 'a * 'b |
         Gt of 'a * 'b

fun is_constr c p =
    case c of
        Eq (x, y) => p x y |
        Le (x, y) => p x y |
        Lt (x, y) => p x y |
        Ge (x, y) => p x y |
        Gt (x, y) => p x y

fun ids c =
    case c of
        Eq (x, _) => x |
        Le (x, _) => x |
        Lt (x, _) => x |
        Ge (x, _) => x |
        Gt (x, _) => x

fun map_ids f c =
    case c of
        Eq (x, m) => Eq (f x, m) |
        Le (x, m) => Le (f x, m) |
        Lt (x, m) => Lt (f x, m) |
        Ge (x, m) => Ge (f x, m) |
        Gt (x, m) => Gt (f x, m)

local
  open Either
in
fun map_either f c =
    case c of
        Eq (x, m) => f x
                     |> mapR ( (fn diff => Eq (diff, m))) |  (* |> mapL failure c *)
        Le (x, m) => f x
                     |> mapR ( (fn diff => Le (diff, m))) |  (* |> mapL failure c *)
        Lt (x, m) => f x
                     |> mapR ( (fn diff => Lt (diff, m))) |  (* |> mapL failure c *)
        Ge (x, m) => f x
                     |> mapR ( (fn diff => Ge (diff, m))) |  (* |> mapL failure c *)
        Gt (x, m) => f x
                     |> mapR ( (fn diff => Gt (diff, m)))

fun check f c =
  case c of
      Eq (x, m) => f x
                   |> mapR (Exp.map (fn diff => Eq (diff, m))) |  (* |> mapL failure c *)
      Le (x, m) => f x
                   |> mapR (Exp.map (fn diff => Le (diff, m))) |  (* |> mapL failure c *)
      Lt (x, m) => f x
                   |> mapR (Exp.map (fn diff => Lt (diff, m))) |  (* |> mapL failure c *)
      Ge (x, m) => f x
                   |> mapR (Exp.map (fn diff => Ge (diff, m))) |  (* |> mapL failure c *)
      Gt (x, m) => f x
                   |> mapR (Exp.map (fn diff => Gt (diff, m)))    (* |> mapL failure c *)
end

fun to_string f e =
    case map_ids f e of
        Eq (x, y) => x ^ " = " ^ (Int.toString y) |
        Le (x, y) => x ^ " <= " ^ (Int.toString y) |
        Lt (x, y) => x ^ " < " ^ (Int.toString y) |
        Ge (x, y) => x ^ " >= " ^ (Int.toString y) |
        Gt (x, y) => x ^ " > " ^ (Int.toString y)
end

structure Invariant = struct
datatype ('a, 'b) conjunction =
         True |
         Constr of ('a, 'b) Constraint.constraint |
         And of ('a, 'b) conjunction * ('a, 'b) conjunction

fun foldl f acc conj =
    case conj of
        True => acc |
        Constr e => f (e, acc) |
        And (l, r) => foldl f (foldl f acc l) r

fun chop e = foldl (op ::) [] e
end

structure Guard = struct
datatype 'a guard =
         True |
         Constr of 'a |
         And of 'a guard * 'a guard |
         Or of 'a guard * 'a guard

fun chop f =
    let
      fun inner f acc g =
          case g of
              True => acc |
              And (l, r) => inner f (inner f acc l) r |
              g => f (g, acc)

    in
      inner f
    end

local
  open Either
in
fun map_either f guard =
          case guard of
              True => succeed True |
              And (l, r) => map_either f l
                            <|> map_either f r
                            |> mapR And |
              Or (l, r) => map_either f l
                           <|> map_either f r
                           |> mapR Or |
              Constr x => f x
                          |> mapR Constr

fun check default disj =
    let
      fun g x = default x >>= disj
      fun inner f guard =
          case guard of
              True => succeed True |
              And (l, r) => inner f l
                            <|> inner f r
                            |> mapR And |
              Or (l, r) => inner g l
                           <|> inner g r
                           |> mapR Or |
              Constr x => f x |> mapR Constr
    in
      inner default
    end
end

fun is_exp p default c =
    case c of
        Constr e => p e |
        _ => default

fun map f e =
    case e of
        True => True |
        And (l, r) => And (map f l, map f r) |
        Or (l, r) => Or (map f l, map f r) |
        Constr a => Constr (f a)

fun decompose_diff c dict =
    case c of
            Difference.Single x => Array.sub (dict, x) |
            Difference.Diff (l, r) => Array.sub (dict, l) - Array.sub (dict, r)

fun decompose_constr c dict =
    case c of
        Constraint.Eq (x, y) => (decompose_diff x dict) = y |
        Constraint.Le (x, y) => (decompose_diff x dict) <= y |
        Constraint.Lt (x, y) => (decompose_diff x dict) < y |
        Constraint.Ge (x, y) => (decompose_diff x dict) >= y |
        Constraint.Gt (x, y) => (decompose_diff x dict) > y

fun data_guard e dict =
    case e of
        True => true |
        And (l, r) => data_guard l dict andalso data_guard r dict |
        Or (l, r) => data_guard l dict orelse data_guard r dict |
        Constr c => decompose_constr c dict

fun get_constraint e =
    case e of
        Constr c => c

fun to_string g =
    let
      fun inner e =
          case e of
              True => "True" |
              And (l, r) => "(" ^ inner l ^ " && " ^ inner r ^ " )" |
              Or (l, r)  => "(" ^ inner l ^ " || " ^ inner r ^ " )" |
              Constr c => c
    in
      inner (map (Constraint.to_string Difference.to_string) g)
    end
end

type var = {name : string, upper : int, lower : int}
type ('a, 'b) invariant =
     ('a, 'b) Invariant.conjunction
type ('a, 'b) guard =
     ('a Difference.clock_pair, 'b) Constraint.constraint Guard.guard
type ('a, 'b) diff_constraint =
     ('a Difference.clock_pair, 'b) Constraint.constraint
type ('a, 'b) constraint = ('a, 'b) Constraint.constraint

type 'a diff = 'a Difference.clock_pair
structure Formula = struct
datatype ('a, 'b) bexp =
         True |
         Not of ('a, 'b) bexp |
         And of ('a, 'b) bexp * ('a, 'b) bexp |
         Or of ('a, 'b) bexp * ('a, 'b) bexp |
         Impl of ('a, 'b) bexp * ('a, 'b) bexp |
         (* Only part of parsing a formular *)
         Loc of 'a * 'a |
         Pred of ('a, 'b) diff_constraint

datatype 'a F =
         Ex of 'a |
         Eg of 'a |
         Ax of 'a |
         Ag of 'a |
         Leadsto of 'a * 'a

fun result f prop =
    case prop of
        Ag res => Ag (f res)
      | Ax res => Ax (f res)
      | Ex res => Ex res
      | Eg res => Eg res
      | _ => undefined ()

(* XXX: Add check *)
fun map f F =
    case F of
            Ex x => Ex (f x) |
            Eg x => Eg (f x) |
            Ax x => Ax (f x) |
            Ag x => Ag (f x) |
            Leadsto (p, q) => Leadsto (f p, f q)

fun the_formula F =
    case F of
        Ex x => x |
        Eg x => x |
        Ax x => x |
        Ag x => x |
        _ => undefined ()

fun p_q F =
    case F of
        Leadsto (p, q) => (p, q) |
        _ => undefined ()

fun conv F =
    case F of
        Ex p => Ex p |
        Eg p => Eg p |
        Ax p => Ax (not o p) |
        Ag p => Ag (not o p) |
        Leadsto (p, q) => Leadsto (p, not o q)
end

type ('a, 'b) formula = ('a, 'b) Formula.bexp Formula.F

datatype 'a action =
         Internal of 'a
         | Out of 'a
         | In of 'a

fun get_label action =
    case action of
        Internal x => x |
        Out x => x |
        In x => x

(* XXX: own structure for updates *)
datatype 'a update =
         Reset of 'a * int |
         Copy of 'a * 'a |
         Shift of 'a * int |
         Update of 'a * 'a * int

fun base upd =
    case upd of
        Update (x, _, _) => x |
        Copy (x, _) => x |
        Shift (x, _) => x |
        Reset (x,_) => x

fun update_ord upds =
    upds |> apply2 base |> int_ord
end

structure Formula = Syntax.Formula
structure BaseTab = Table(type key = int Syntax.update val ord = Syntax.update_ord)
