functor SignedWordDBMEntry(W : SIGNED_WORD)
        : PROTO_ENTRY where type t = W.t =
struct
open W
type t = W.t

val inf = W.maximum
val zero = W.one
val check_neg = W.check_neg

val minimum = W.minimum


fun |~| w = (W.|~| (shiftr 1 w) |> shiftl 1) \/  w |&| W.one

fun add x y =
    let
            fun lsb_set w = w |&| W.one
    in
            case (x == inf, y == inf) of
                (true, _) => inf
              | (_, true) => inf
              | _ => (x |+| y)
                    |+| (W.|~|
                           ((lsb_set x) \/ (lsb_set y)))
    end

fun (x |+| y) = add x y

val (op |<=|) = W.|<=|
val (op |>=|) = W.|>=|
val (op |<|) = W.|<|
val (op |>|) = W.|>|

val min = W.min
val max = W.max
fun max_ceil c c' =
    case (c == inf, c' == inf) of
        (true, _) => c' |
        (_, true) => c |
        _ => max c c'

val (op ==) = W.==



(* Adapted from the Haskell code here: https://stackoverflow.com/a/27581906 *)
(* XXX: Test this is it right? *)
(* XXX: rename to mod_lsb *)
fun mod_lsb b w =
    if b then W.|+| (w, W.one)
    else w |> shiftr 1 |> shiftl 1
    (* let *)
        (*   val pow_two = (W.mod2 w) ==  zero *)
    (*   open W *)
    (* in *)
        (*     case (b, pow_two) of *)
        (*         (true, true) => (w |+| one) *)
        (*       | (false, false) => (w |+| (W.|~| one)) *)
        (*       | (_, _)  => w *)
    (* end *)

(* XXX: Test this is it right? *)
fun not_bound b =
    (W.mod2 b \/ (W.minimum |+| W.one)) |&| b

fun aux_from_int n =
    let
      val entry = W.from_int n
      val neg = W.check_neg entry
      val res = entry |> W.shiftl 1
      val neg_res = W.check_neg res
    in case (neg, neg_res) of
               (true, false) => raise W.Underflow
             | (false, true) => raise W.Overflow
             | _ => res
    end
fun from_int (IntRep.LTE 0) = W.one
  | from_int (IntRep.LT 0) = W.zero
  | from_int (IntRep.LTE n) = mod_lsb true (aux_from_int n)
  | from_int (IntRep.LT n) = aux_from_int n
  | from_int IntRep.Inf = inf

fun =< x = from_int (IntRep.LT x)
fun ==< x = from_int (IntRep.LTE x)

fun cmp x y = if x |<| y then Lt else if x == y then Eq else Gt

fun to_string w =
    let fun aux cmp = "(" ^ (W.shiftr 1 w |> W.to_string) ^ ", " ^ cmp ^ ")" in
      if w == inf then "oo"
      else if w |&| W.one ==  W.zero then aux "<" else aux "<="
    end

end

functor DBMEntryWordFn(structure W : SIGNED_WORD
                       structure B : BINARY where type from = W.t) : DBM_ENTRY =
struct
structure Entry = SignedWordDBMEntry(W)
open Entry
type from = Entry.t
type to = B.to
val serialize = B.serialize
end

structure Entry8Bit = DBMEntryWordFn(structure W = Int8
                                     structure B = SerWord8)
structure Entry32Bit = DBMEntryWordFn(structure W = Int32
                                     structure B = SerWord32)
structure Entry64Bit = DBMEntryWordFn(structure W = Int64
                                     structure B = SerWord64)
