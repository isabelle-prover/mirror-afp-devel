infix 7 |&|
infix 6 \/ |+|
infix 4 == |<| |>| |<=| |>=|

signature SIGNED_WORD =
sig
    type t
    exception Underflow
    exception Overflow
    val zero: t
    val one: t
    val maximum: t
    val minimum: t
    val |~| : t -> t
    val |&| : t * t -> t
    val \/ : t * t -> t
    val neg_mask: t
    val check_neg: t -> bool
    val == : t * t -> bool
    val |<=| : t * t -> bool
    val |<| : t * t -> bool
    val |>=| : t * t -> bool
    val |>| : t * t -> bool

    val mod2: t -> t

    (* Multiple possible versions of adding signed words: *)
    val add: (t -> 'a) ->
             (t -> 'a) ->
             t -> t -> 'a
    (* Exception if Overflow: *)
    val add_ex: t -> t -> t
    (* x |+| y == add_ex x y *)
    val |+| : t * t -> t
    (* NONE if Overflow: *)
    val add_opt: t -> t -> t option

    val shiftl: int -> t -> t
    val shiftr: int -> t -> t
    val max: t -> t -> t
    val min: t -> t -> t
    val from_int: int -> t
    val to_string: t -> string
end



functor SignedWordFn (W : WORD)  : SIGNED_WORD =
struct
type t = W.word

exception Underflow
exception Overflow

val zero = W.fromInt 0

val one = W.fromInt 1

fun shiftl n w = W.<< (w, Word.fromInt n)
fun shiftr n w = W.~>> (w, Word.fromInt n)
val neg_mask = shiftl (W.wordSize - 1) one



val maximum = W.notb neg_mask
val minimum = neg_mask
fun |~| x = W.~ x

fun a |&| b = W.andb (a, b)

fun a \/ b = W.orb (a, b)

fun check_neg x = (x |&| neg_mask) <> zero

fun (x == y) = x = y

fun (x > y) =
    let
        val x_neg = check_neg x
        val y_neg = check_neg y
    in
        case (x_neg, y_neg) of
            (true, true) => W.> (x, y)
          | (false, false) => W.> (x, y)
          | (false, true) => true
          | (true, false) => false
    end

fun (x |>=| y) = if x = y then true else x > y


fun (x |<| y) =
    let
          val x_neg = check_neg x
          val y_neg = check_neg y
    in
        case (x_neg, y_neg) of
            (true, true) => W.< (x, y)
          | (false, false) => W.< (x, y)
          | (false, true) => false
          | (true, false) => true
    end

(* XXX: Test this *)
fun (y |>| x) =
    let
        val x_neg = check_neg x
        val y_neg = check_neg y
    in
        case (x_neg, y_neg) of
            (true, true) => W.< (x, y)
          | (false, false) => W.< (x, y)
          | (false, true) => false
          | (true, false) => true
    end

fun (x |<=| y) = if x == y then true else x |<| y
val mod2 = (curry W.andb) (W.fromInt 1)

(* Rules for Overflow taken from:
   http://sandbox.mc.edu/~bennet/cs110/tc/orules.html *)
(* Find nice bithacks for finding out sign of int *)
fun add overflow return x y =
    let
      val sum = W.+ (x, y)
      val x_neg = neg_mask |&| x
      val y_neg = neg_mask |&| y
      val possible = W.xorb (x_neg, y_neg)
    in
      (* If none has the same sign it cannot be a overflow *)
      if possible = zero then
        (let val sum_neg = neg_mask |&| sum in
           if W.> (W.xorb((x_neg |&| y_neg), sum_neg), zero) then overflow sum
           else return sum end)
      else return sum
    end

val add_opt = add (K NONE) SOME

fun add_ex x y =
    let
      val x_neg = neg_mask |&| x
      val y_neg = neg_mask |&| y
      val possible = W.xorb (x_neg, y_neg)
      val addition = W.+ (x, y)
    in
      (* If none has the same sign it cannot be a overflow *)
      if possible = zero then
        (let val sum_neg = neg_mask |&| addition in
           if W.xorb((x_neg |&| y_neg), sum_neg) = zero then addition
           else raise Overflow end)
      else addition
    end

fun (x |+| y) = add_ex x y

fun from_int' overflow underflow return x =
       let
        val large_x = LargeInt.fromInt x
        val x_neg = Int.sign x = Int.~ 1
        val res = W.fromLargeInt large_x
    val large_res = W.toLargeInt res
        val too_big = LargeInt.> (large_x, W.toLargeInt maximum)
        val max1 = W.+ (maximum, one) |> W.toLargeInt
        val too_small = LargeInt.> (LargeInt.~ large_x, max1)
    in case (x_neg, too_big, too_small) of
           (false, true, _) => overflow x
         | (true, false, true) => underflow x
         | _ => return res
    end

val from_int = from_int' (fn _ => raise Overflow) (fn _ => raise Underflow) id


fun min_max p x y = if p (x, y) then x else y
val min = min_max (fn (x, y) => x |<| y)
val max = min_max (fn (x, y) => x |>| y)
fun to_string x = W.toLargeIntX x |> LargeInt.toString
end

structure Int8 = SignedWordFn(Word8);
structure Int32 = SignedWordFn(Word32);
structure Int64 = SignedWordFn(Word64);
