structure Fun : sig
  val id : 'a -> 'a
end = struct

fun id x = (fn xa => xa) x;

end; (*struct Fun*)

structure HOL : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

end; (*struct HOL*)

structure Orderings : sig
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val max : 'a ord -> 'a -> 'a -> 'a
  val min : 'a ord -> 'a -> 'a -> 'a
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun min A_ a b = (if less_eq A_ a b then a else b);

end; (*struct Orderings*)

structure Arith : sig
  type nat
  val equal_nata : nat -> nat -> bool
  val equal_nat : nat HOL.equal
  type num
  val plus_nat : nat -> nat -> nat
  val one_nat : nat
  val suc : nat -> nat
  val minus_nat : nat -> nat -> nat
  val zero_nat : nat
  val funpow : nat -> ('a -> 'a) -> 'a -> 'a
  val less_nat : nat -> nat -> bool
  val less_eq_nat : nat -> nat -> bool
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat HOL.equal;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int Orderings.ord;

datatype num = One | Bit0 of num | Bit1 of num;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun minus_nat m n =
  Nat (Orderings.max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun funpow n f =
  (if equal_nata n zero_nat then Fun.id
    else f o funpow (minus_nat n one_nat) f);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

end; (*struct Arith*)

structure LTL : sig
  datatype 'a ltln = LTLnTrue | LTLnFalse | LTLnProp of 'a | LTLnNProp of 'a |
    LTLnAnd of 'a ltln * 'a ltln | LTLnOr of 'a ltln * 'a ltln |
    LTLnNext of 'a ltln | LTLnUntil of 'a ltln * 'a ltln |
    LTLnRelease of 'a ltln * 'a ltln
  val equal_ltlna : 'a HOL.equal -> 'a ltln -> 'a ltln -> bool
  val equal_ltln : 'a HOL.equal -> 'a ltln HOL.equal
  datatype 'a ltlc = LTLcTrue | LTLcFalse | LTLcProp of 'a | LTLcNeg of 'a ltlc
    | LTLcAnd of 'a ltlc * 'a ltlc | LTLcOr of 'a ltlc * 'a ltlc |
    LTLcImplies of 'a ltlc * 'a ltlc | LTLcNext of 'a ltlc |
    LTLcFinal of 'a ltlc | LTLcGlobal of 'a ltlc |
    LTLcUntil of 'a ltlc * 'a ltlc | LTLcRelease of 'a ltlc * 'a ltlc
  val lTLcIff : 'a ltlc -> 'a ltlc -> 'a ltlc
  val not_n : 'a ltln -> 'a ltln
  val ltlc_to_ltln : 'a ltlc -> 'a ltln
  val map_ltlc : ('a -> 'b) -> 'a ltlc -> 'b ltlc
  val size_ltln : 'a ltln -> Arith.nat
end = struct

datatype 'a ltln = LTLnTrue | LTLnFalse | LTLnProp of 'a | LTLnNProp of 'a |
  LTLnAnd of 'a ltln * 'a ltln | LTLnOr of 'a ltln * 'a ltln |
  LTLnNext of 'a ltln | LTLnUntil of 'a ltln * 'a ltln |
  LTLnRelease of 'a ltln * 'a ltln;

fun equal_ltlna A_ (LTLnUntil (x81, x82)) (LTLnRelease (x91, x92)) = false
  | equal_ltlna A_ (LTLnRelease (x91, x92)) (LTLnUntil (x81, x82)) = false
  | equal_ltlna A_ (LTLnNext x7) (LTLnRelease (x91, x92)) = false
  | equal_ltlna A_ (LTLnRelease (x91, x92)) (LTLnNext x7) = false
  | equal_ltlna A_ (LTLnNext x7) (LTLnUntil (x81, x82)) = false
  | equal_ltlna A_ (LTLnUntil (x81, x82)) (LTLnNext x7) = false
  | equal_ltlna A_ (LTLnOr (x61, x62)) (LTLnRelease (x91, x92)) = false
  | equal_ltlna A_ (LTLnRelease (x91, x92)) (LTLnOr (x61, x62)) = false
  | equal_ltlna A_ (LTLnOr (x61, x62)) (LTLnUntil (x81, x82)) = false
  | equal_ltlna A_ (LTLnUntil (x81, x82)) (LTLnOr (x61, x62)) = false
  | equal_ltlna A_ (LTLnOr (x61, x62)) (LTLnNext x7) = false
  | equal_ltlna A_ (LTLnNext x7) (LTLnOr (x61, x62)) = false
  | equal_ltlna A_ (LTLnAnd (x51, x52)) (LTLnRelease (x91, x92)) = false
  | equal_ltlna A_ (LTLnRelease (x91, x92)) (LTLnAnd (x51, x52)) = false
  | equal_ltlna A_ (LTLnAnd (x51, x52)) (LTLnUntil (x81, x82)) = false
  | equal_ltlna A_ (LTLnUntil (x81, x82)) (LTLnAnd (x51, x52)) = false
  | equal_ltlna A_ (LTLnAnd (x51, x52)) (LTLnNext x7) = false
  | equal_ltlna A_ (LTLnNext x7) (LTLnAnd (x51, x52)) = false
  | equal_ltlna A_ (LTLnAnd (x51, x52)) (LTLnOr (x61, x62)) = false
  | equal_ltlna A_ (LTLnOr (x61, x62)) (LTLnAnd (x51, x52)) = false
  | equal_ltlna A_ (LTLnNProp x4) (LTLnRelease (x91, x92)) = false
  | equal_ltlna A_ (LTLnRelease (x91, x92)) (LTLnNProp x4) = false
  | equal_ltlna A_ (LTLnNProp x4) (LTLnUntil (x81, x82)) = false
  | equal_ltlna A_ (LTLnUntil (x81, x82)) (LTLnNProp x4) = false
  | equal_ltlna A_ (LTLnNProp x4) (LTLnNext x7) = false
  | equal_ltlna A_ (LTLnNext x7) (LTLnNProp x4) = false
  | equal_ltlna A_ (LTLnNProp x4) (LTLnOr (x61, x62)) = false
  | equal_ltlna A_ (LTLnOr (x61, x62)) (LTLnNProp x4) = false
  | equal_ltlna A_ (LTLnNProp x4) (LTLnAnd (x51, x52)) = false
  | equal_ltlna A_ (LTLnAnd (x51, x52)) (LTLnNProp x4) = false
  | equal_ltlna A_ (LTLnProp x3) (LTLnRelease (x91, x92)) = false
  | equal_ltlna A_ (LTLnRelease (x91, x92)) (LTLnProp x3) = false
  | equal_ltlna A_ (LTLnProp x3) (LTLnUntil (x81, x82)) = false
  | equal_ltlna A_ (LTLnUntil (x81, x82)) (LTLnProp x3) = false
  | equal_ltlna A_ (LTLnProp x3) (LTLnNext x7) = false
  | equal_ltlna A_ (LTLnNext x7) (LTLnProp x3) = false
  | equal_ltlna A_ (LTLnProp x3) (LTLnOr (x61, x62)) = false
  | equal_ltlna A_ (LTLnOr (x61, x62)) (LTLnProp x3) = false
  | equal_ltlna A_ (LTLnProp x3) (LTLnAnd (x51, x52)) = false
  | equal_ltlna A_ (LTLnAnd (x51, x52)) (LTLnProp x3) = false
  | equal_ltlna A_ (LTLnProp x3) (LTLnNProp x4) = false
  | equal_ltlna A_ (LTLnNProp x4) (LTLnProp x3) = false
  | equal_ltlna A_ LTLnFalse (LTLnRelease (x91, x92)) = false
  | equal_ltlna A_ (LTLnRelease (x91, x92)) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnUntil (x81, x82)) = false
  | equal_ltlna A_ (LTLnUntil (x81, x82)) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnNext x7) = false
  | equal_ltlna A_ (LTLnNext x7) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnOr (x61, x62)) = false
  | equal_ltlna A_ (LTLnOr (x61, x62)) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnAnd (x51, x52)) = false
  | equal_ltlna A_ (LTLnAnd (x51, x52)) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnNProp x4) = false
  | equal_ltlna A_ (LTLnNProp x4) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnProp x3) = false
  | equal_ltlna A_ (LTLnProp x3) LTLnFalse = false
  | equal_ltlna A_ LTLnTrue (LTLnRelease (x91, x92)) = false
  | equal_ltlna A_ (LTLnRelease (x91, x92)) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnUntil (x81, x82)) = false
  | equal_ltlna A_ (LTLnUntil (x81, x82)) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnNext x7) = false
  | equal_ltlna A_ (LTLnNext x7) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnOr (x61, x62)) = false
  | equal_ltlna A_ (LTLnOr (x61, x62)) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnAnd (x51, x52)) = false
  | equal_ltlna A_ (LTLnAnd (x51, x52)) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnNProp x4) = false
  | equal_ltlna A_ (LTLnNProp x4) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnProp x3) = false
  | equal_ltlna A_ (LTLnProp x3) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue LTLnFalse = false
  | equal_ltlna A_ LTLnFalse LTLnTrue = false
  | equal_ltlna A_ (LTLnRelease (x91, x92)) (LTLnRelease (y91, y92)) =
    equal_ltlna A_ x91 y91 andalso equal_ltlna A_ x92 y92
  | equal_ltlna A_ (LTLnUntil (x81, x82)) (LTLnUntil (y81, y82)) =
    equal_ltlna A_ x81 y81 andalso equal_ltlna A_ x82 y82
  | equal_ltlna A_ (LTLnNext x7) (LTLnNext y7) = equal_ltlna A_ x7 y7
  | equal_ltlna A_ (LTLnOr (x61, x62)) (LTLnOr (y61, y62)) =
    equal_ltlna A_ x61 y61 andalso equal_ltlna A_ x62 y62
  | equal_ltlna A_ (LTLnAnd (x51, x52)) (LTLnAnd (y51, y52)) =
    equal_ltlna A_ x51 y51 andalso equal_ltlna A_ x52 y52
  | equal_ltlna A_ (LTLnNProp x4) (LTLnNProp y4) = HOL.eq A_ x4 y4
  | equal_ltlna A_ (LTLnProp x3) (LTLnProp y3) = HOL.eq A_ x3 y3
  | equal_ltlna A_ LTLnFalse LTLnFalse = true
  | equal_ltlna A_ LTLnTrue LTLnTrue = true;

fun equal_ltln A_ = {equal = equal_ltlna A_} : 'a ltln HOL.equal;

datatype 'a ltlc = LTLcTrue | LTLcFalse | LTLcProp of 'a | LTLcNeg of 'a ltlc |
  LTLcAnd of 'a ltlc * 'a ltlc | LTLcOr of 'a ltlc * 'a ltlc |
  LTLcImplies of 'a ltlc * 'a ltlc | LTLcNext of 'a ltlc | LTLcFinal of 'a ltlc
  | LTLcGlobal of 'a ltlc | LTLcUntil of 'a ltlc * 'a ltlc |
  LTLcRelease of 'a ltlc * 'a ltlc;

fun lTLcIff phi psi = LTLcAnd (LTLcImplies (phi, psi), LTLcImplies (psi, phi));

fun not_n LTLnTrue = LTLnFalse
  | not_n LTLnFalse = LTLnTrue
  | not_n (LTLnProp a) = LTLnNProp a
  | not_n (LTLnNProp a) = LTLnProp a
  | not_n (LTLnAnd (phi, psi)) = LTLnOr (not_n phi, not_n psi)
  | not_n (LTLnOr (phi, psi)) = LTLnAnd (not_n phi, not_n psi)
  | not_n (LTLnUntil (phi, psi)) = LTLnRelease (not_n phi, not_n psi)
  | not_n (LTLnRelease (phi, psi)) = LTLnUntil (not_n phi, not_n psi)
  | not_n (LTLnNext phi) = LTLnNext (not_n phi);

fun ltlc_to_ltlna false LTLcTrue = LTLnTrue
  | ltlc_to_ltlna false LTLcFalse = LTLnFalse
  | ltlc_to_ltlna false (LTLcProp q) = LTLnProp q
  | ltlc_to_ltlna false (LTLcAnd (phi, psi)) =
    LTLnAnd (ltlc_to_ltlna false phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna false (LTLcOr (phi, psi)) =
    LTLnOr (ltlc_to_ltlna false phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna false (LTLcImplies (phi, psi)) =
    LTLnOr (ltlc_to_ltlna true phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna false (LTLcFinal phi) =
    LTLnUntil (LTLnTrue, ltlc_to_ltlna false phi)
  | ltlc_to_ltlna false (LTLcGlobal phi) =
    LTLnRelease (LTLnFalse, ltlc_to_ltlna false phi)
  | ltlc_to_ltlna false (LTLcUntil (phi, psi)) =
    LTLnUntil (ltlc_to_ltlna false phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna false (LTLcRelease (phi, psi)) =
    LTLnRelease (ltlc_to_ltlna false phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna true LTLcTrue = LTLnFalse
  | ltlc_to_ltlna true LTLcFalse = LTLnTrue
  | ltlc_to_ltlna true (LTLcProp q) = LTLnNProp q
  | ltlc_to_ltlna true (LTLcAnd (nu, mu)) =
    LTLnOr (ltlc_to_ltlna true nu, ltlc_to_ltlna true mu)
  | ltlc_to_ltlna true (LTLcOr (nu, mu)) =
    LTLnAnd (ltlc_to_ltlna true nu, ltlc_to_ltlna true mu)
  | ltlc_to_ltlna true (LTLcImplies (phi, psi)) =
    LTLnAnd (ltlc_to_ltlna false phi, ltlc_to_ltlna true psi)
  | ltlc_to_ltlna true (LTLcFinal phi) =
    LTLnRelease (LTLnFalse, ltlc_to_ltlna true phi)
  | ltlc_to_ltlna true (LTLcGlobal phi) =
    LTLnUntil (LTLnTrue, ltlc_to_ltlna true phi)
  | ltlc_to_ltlna true (LTLcUntil (nu, mu)) =
    LTLnRelease (ltlc_to_ltlna true nu, ltlc_to_ltlna true mu)
  | ltlc_to_ltlna true (LTLcRelease (nu, mu)) =
    LTLnUntil (ltlc_to_ltlna true nu, ltlc_to_ltlna true mu)
  | ltlc_to_ltlna b (LTLcNeg psi) = ltlc_to_ltlna (not b) psi
  | ltlc_to_ltlna b (LTLcNext phi) = LTLnNext (ltlc_to_ltlna b phi);

fun ltlc_to_ltln phi = ltlc_to_ltlna false phi;

fun map_ltlc f LTLcTrue = LTLcTrue
  | map_ltlc f LTLcFalse = LTLcFalse
  | map_ltlc f (LTLcProp x3) = LTLcProp (f x3)
  | map_ltlc f (LTLcNeg x4) = LTLcNeg (map_ltlc f x4)
  | map_ltlc f (LTLcAnd (x51, x52)) = LTLcAnd (map_ltlc f x51, map_ltlc f x52)
  | map_ltlc f (LTLcOr (x61, x62)) = LTLcOr (map_ltlc f x61, map_ltlc f x62)
  | map_ltlc f (LTLcImplies (x71, x72)) =
    LTLcImplies (map_ltlc f x71, map_ltlc f x72)
  | map_ltlc f (LTLcNext x8) = LTLcNext (map_ltlc f x8)
  | map_ltlc f (LTLcFinal x9) = LTLcFinal (map_ltlc f x9)
  | map_ltlc f (LTLcGlobal x10) = LTLcGlobal (map_ltlc f x10)
  | map_ltlc f (LTLcUntil (x111, x112)) =
    LTLcUntil (map_ltlc f x111, map_ltlc f x112)
  | map_ltlc f (LTLcRelease (x121, x122)) =
    LTLcRelease (map_ltlc f x121, map_ltlc f x122);

fun size_ltln LTLnTrue = Arith.suc Arith.zero_nat
  | size_ltln LTLnFalse = Arith.suc Arith.zero_nat
  | size_ltln (LTLnProp x3) = Arith.suc Arith.zero_nat
  | size_ltln (LTLnNProp x4) = Arith.suc Arith.zero_nat
  | size_ltln (LTLnAnd (x51, x52)) =
    Arith.plus_nat (Arith.plus_nat (size_ltln x51) (size_ltln x52))
      (Arith.suc Arith.zero_nat)
  | size_ltln (LTLnOr (x61, x62)) =
    Arith.plus_nat (Arith.plus_nat (size_ltln x61) (size_ltln x62))
      (Arith.suc Arith.zero_nat)
  | size_ltln (LTLnNext x7) =
    Arith.plus_nat (size_ltln x7) (Arith.suc Arith.zero_nat)
  | size_ltln (LTLnUntil (x81, x82)) =
    Arith.plus_nat (Arith.plus_nat (size_ltln x81) (size_ltln x82))
      (Arith.suc Arith.zero_nat)
  | size_ltln (LTLnRelease (x91, x92)) =
    Arith.plus_nat (Arith.plus_nat (size_ltln x91) (size_ltln x92))
      (Arith.suc Arith.zero_nat);

end; (*struct LTL*)

structure Stringa : sig
  val size_literal : string -> Arith.nat
end = struct

fun size_literal s = Arith.zero_nat;

end; (*struct Stringa*)

structure Product_Type : sig
  val equal_unit : unit HOL.equal
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit HOL.equal;

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

end; (*struct Product_Type*)

structure Predicate : sig
  type 'a seq
  type 'a pred
  val bind : 'a pred -> ('a -> 'b pred) -> 'b pred
  val holds : unit pred -> bool
  val bot_pred : 'a pred
  val single : 'a -> 'a pred
  val sup_pred : 'a pred -> 'a pred -> 'a pred
end = struct

datatype 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);

fun bind (Seq g) f = Seq (fn _ => apply f (g ()))
and apply f Empty = Empty
  | apply f (Insert (x, p)) = Join (f x, Join (bind p f, Empty))
  | apply f (Join (p, xq)) = Join (bind p f, apply f xq);

fun eval A_ (Seq f) = member A_ (f ())
and member A_ Empty x = false
  | member A_ (Insert (y, p)) x = HOL.eq A_ x y orelse eval A_ p x
  | member A_ (Join (p, xq)) x = eval A_ p x orelse member A_ xq x;

fun holds p = eval Product_Type.equal_unit p ();

val bot_pred : 'a pred = Seq (fn _ => Empty);

fun single x = Seq (fn _ => Insert (x, bot_pred));

fun adjunct p Empty = Join (p, Empty)
  | adjunct p (Insert (x, q)) = Insert (x, sup_pred q p)
  | adjunct p (Join (q, xq)) = Join (q, adjunct p xq)
and sup_pred (Seq f) (Seq g) =
  Seq (fn _ =>
        (case f () of Empty => g ()
          | Insert (x, p) => Insert (x, sup_pred p (Seq g))
          | Join (p, xq) => adjunct (Seq g) (Join (p, xq))));

end; (*struct Predicate*)

structure Extended_Nat : sig
  datatype enat = Enat of Arith.nat | Infinity_enat
  val ord_enat : enat Orderings.ord
  val eSuc : enat -> enat
  val zero_enat : enat
  val minus_enat : enat -> enat -> enat
end = struct

datatype enat = Enat of Arith.nat | Infinity_enat;

fun less_eq_enat Infinity_enat (Enat n) = false
  | less_eq_enat q Infinity_enat = true
  | less_eq_enat (Enat m) (Enat n) = Arith.less_eq_nat m n;

fun less_enat Infinity_enat q = false
  | less_enat (Enat m) Infinity_enat = true
  | less_enat (Enat m) (Enat n) = Arith.less_nat m n;

val ord_enat = {less_eq = less_eq_enat, less = less_enat} : enat Orderings.ord;

fun eSuc i =
  (case i of Enat n => Enat (Arith.suc n) | Infinity_enat => Infinity_enat);

val zero_enat : enat = Enat Arith.zero_nat;

fun minus_enat (Enat a) Infinity_enat = zero_enat
  | minus_enat Infinity_enat n = Infinity_enat
  | minus_enat (Enat a) (Enat b) = Enat (Arith.minus_nat a b);

end; (*struct Extended_Nat*)

structure LTL_Rewrite : sig
  val rewrite_iter_slow : 'a HOL.equal -> 'a LTL.ltln -> 'a LTL.ltln
end = struct

fun mk_or x y =
  (case x of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => y
    | LTL.LTLnProp _ =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => x
        | LTL.LTLnProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnNext _ => LTL.LTLnOr (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnOr (x, y))
    | LTL.LTLnNProp _ =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => x
        | LTL.LTLnProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnNext _ => LTL.LTLnOr (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnOr (x, y))
    | LTL.LTLnAnd (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => x
        | LTL.LTLnProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnNext _ => LTL.LTLnOr (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnOr (x, y))
    | LTL.LTLnOr (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => x
        | LTL.LTLnProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnNext _ => LTL.LTLnOr (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnOr (x, y))
    | LTL.LTLnNext _ =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => x
        | LTL.LTLnProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnNext _ => LTL.LTLnOr (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnOr (x, y))
    | LTL.LTLnUntil (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => x
        | LTL.LTLnProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnNext _ => LTL.LTLnOr (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnOr (x, y))
    | LTL.LTLnRelease (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => x
        | LTL.LTLnProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnOr (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnNext _ => LTL.LTLnOr (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnOr (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnOr (x, y)));

fun eq_i_i A_ xa xb =
  Predicate.bind (Predicate.single (xa, xb))
    (fn (x, xaa) =>
      (if HOL.eq A_ x xaa then Predicate.single () else Predicate.bot_pred));

fun mk_and x y =
  (case x of LTL.LTLnTrue => y | LTL.LTLnFalse => LTL.LTLnFalse
    | LTL.LTLnProp _ =>
      (case y of LTL.LTLnTrue => x | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnNext _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnAnd (x, y))
    | LTL.LTLnNProp _ =>
      (case y of LTL.LTLnTrue => x | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnNext _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnAnd (x, y))
    | LTL.LTLnAnd (_, _) =>
      (case y of LTL.LTLnTrue => x | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnNext _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnAnd (x, y))
    | LTL.LTLnOr (_, _) =>
      (case y of LTL.LTLnTrue => x | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnNext _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnAnd (x, y))
    | LTL.LTLnNext _ =>
      (case y of LTL.LTLnTrue => x | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnNext _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnAnd (x, y))
    | LTL.LTLnUntil (_, _) =>
      (case y of LTL.LTLnTrue => x | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnNext _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnAnd (x, y))
    | LTL.LTLnRelease (_, _) =>
      (case y of LTL.LTLnTrue => x | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnNext _ => LTL.LTLnAnd (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnAnd (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnAnd (x, y)));

fun mk_next_pow n x =
  (case x of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
    | LTL.LTLnProp _ => Arith.funpow n LTL.LTLnNext x
    | LTL.LTLnNProp _ => Arith.funpow n LTL.LTLnNext x
    | LTL.LTLnAnd (_, _) => Arith.funpow n LTL.LTLnNext x
    | LTL.LTLnOr (_, _) => Arith.funpow n LTL.LTLnNext x
    | LTL.LTLnNext _ => Arith.funpow n LTL.LTLnNext x
    | LTL.LTLnUntil (_, _) => Arith.funpow n LTL.LTLnNext x
    | LTL.LTLnRelease (_, _) => Arith.funpow n LTL.LTLnNext x);

fun is_constant LTL.LTLnTrue = true
  | is_constant LTL.LTLnFalse = true
  | is_constant (LTL.LTLnProp v) = false
  | is_constant (LTL.LTLnNProp v) = false
  | is_constant (LTL.LTLnAnd (v, va)) = false
  | is_constant (LTL.LTLnOr (v, va)) = false
  | is_constant (LTL.LTLnNext v) = false
  | is_constant (LTL.LTLnUntil (v, va)) = false
  | is_constant (LTL.LTLnRelease (v, va)) = false;

fun the_enat_0 (Extended_Nat.Enat i) = i
  | the_enat_0 Extended_Nat.Infinity_enat = Arith.zero_nat;

fun combine binop (phi, i) (psi, j) =
  let
    val chi =
      binop (mk_next_pow (the_enat_0 (Extended_Nat.minus_enat i j)) phi)
        (mk_next_pow (the_enat_0 (Extended_Nat.minus_enat j i)) psi);
  in
    (chi, (if is_constant chi then Extended_Nat.Infinity_enat
            else Orderings.min Extended_Nat.ord_enat i j))
  end;

fun iterate A_ f x n =
  (if Arith.equal_nata n Arith.zero_nat then x
    else let
           val xa = f x;
         in
           (if HOL.eq A_ x xa then x
             else iterate A_ f xa (Arith.minus_nat n Arith.one_nat))
         end);

fun mk_next x =
  (case x of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
    | LTL.LTLnProp _ => LTL.LTLnNext x | LTL.LTLnNProp _ => LTL.LTLnNext x
    | LTL.LTLnAnd (_, _) => LTL.LTLnNext x | LTL.LTLnOr (_, _) => LTL.LTLnNext x
    | LTL.LTLnNext _ => LTL.LTLnNext x | LTL.LTLnUntil (_, _) => LTL.LTLnNext x
    | LTL.LTLnRelease (_, _) => LTL.LTLnNext x);

fun remove_until (LTL.LTLnUntil (x, y)) = remove_until y
  | remove_until (LTL.LTLnOr (x, y)) =
    LTL.LTLnOr (remove_until x, remove_until y)
  | remove_until LTL.LTLnTrue = LTL.LTLnTrue
  | remove_until LTL.LTLnFalse = LTL.LTLnFalse
  | remove_until (LTL.LTLnProp v) = LTL.LTLnProp v
  | remove_until (LTL.LTLnNProp v) = LTL.LTLnNProp v
  | remove_until (LTL.LTLnAnd (v, va)) = LTL.LTLnAnd (v, va)
  | remove_until (LTL.LTLnNext v) = LTL.LTLnNext v
  | remove_until (LTL.LTLnRelease (v, va)) = LTL.LTLnRelease (v, va);

fun mk_until x y =
  (case x
    of LTL.LTLnTrue =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnUntil (LTL.LTLnTrue, remove_until y)
        | LTL.LTLnNProp _ => LTL.LTLnUntil (LTL.LTLnTrue, remove_until y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnUntil (LTL.LTLnTrue, remove_until y)
        | LTL.LTLnOr (_, _) => LTL.LTLnUntil (LTL.LTLnTrue, remove_until y)
        | LTL.LTLnNext _ => LTL.LTLnUntil (LTL.LTLnTrue, remove_until y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnUntil (LTL.LTLnTrue, remove_until y)
        | LTL.LTLnRelease (_, _) =>
          LTL.LTLnUntil (LTL.LTLnTrue, remove_until y))
    | LTL.LTLnFalse => y
    | LTL.LTLnProp _ =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnNext _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnUntil (x, y))
    | LTL.LTLnNProp _ =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnNext _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnUntil (x, y))
    | LTL.LTLnAnd (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnNext _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnUntil (x, y))
    | LTL.LTLnOr (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnNext _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnUntil (x, y))
    | LTL.LTLnNext _ =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnNext _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnUntil (x, y))
    | LTL.LTLnUntil (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnNext _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnUntil (x, y))
    | LTL.LTLnRelease (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnNext _ => LTL.LTLnUntil (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnUntil (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnUntil (x, y)));

fun remove_release (LTL.LTLnRelease (x, y)) = remove_release y
  | remove_release (LTL.LTLnAnd (x, y)) =
    LTL.LTLnAnd (remove_release x, remove_release y)
  | remove_release LTL.LTLnTrue = LTL.LTLnTrue
  | remove_release LTL.LTLnFalse = LTL.LTLnFalse
  | remove_release (LTL.LTLnProp v) = LTL.LTLnProp v
  | remove_release (LTL.LTLnNProp v) = LTL.LTLnNProp v
  | remove_release (LTL.LTLnOr (v, va)) = LTL.LTLnOr (v, va)
  | remove_release (LTL.LTLnNext v) = LTL.LTLnNext v
  | remove_release (LTL.LTLnUntil (v, va)) = LTL.LTLnUntil (v, va);

fun mk_release x y =
  (case x of LTL.LTLnTrue => y
    | LTL.LTLnFalse =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnRelease (LTL.LTLnFalse, remove_release y)
        | LTL.LTLnNProp _ => LTL.LTLnRelease (LTL.LTLnFalse, remove_release y)
        | LTL.LTLnAnd (_, _) =>
          LTL.LTLnRelease (LTL.LTLnFalse, remove_release y)
        | LTL.LTLnOr (_, _) => LTL.LTLnRelease (LTL.LTLnFalse, remove_release y)
        | LTL.LTLnNext _ => LTL.LTLnRelease (LTL.LTLnFalse, remove_release y)
        | LTL.LTLnUntil (_, _) =>
          LTL.LTLnRelease (LTL.LTLnFalse, remove_release y)
        | LTL.LTLnRelease (_, _) =>
          LTL.LTLnRelease (LTL.LTLnFalse, remove_release y))
    | LTL.LTLnProp _ =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnNext _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnRelease (x, y))
    | LTL.LTLnNProp _ =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnNext _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnRelease (x, y))
    | LTL.LTLnAnd (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnNext _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnRelease (x, y))
    | LTL.LTLnOr (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnNext _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnRelease (x, y))
    | LTL.LTLnNext _ =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnNext _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnRelease (x, y))
    | LTL.LTLnUntil (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnNext _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnRelease (x, y))
    | LTL.LTLnRelease (_, _) =>
      (case y of LTL.LTLnTrue => LTL.LTLnTrue | LTL.LTLnFalse => LTL.LTLnFalse
        | LTL.LTLnProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnNProp _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnAnd (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnOr (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnNext _ => LTL.LTLnRelease (x, y)
        | LTL.LTLnUntil (_, _) => LTL.LTLnRelease (x, y)
        | LTL.LTLnRelease (_, _) => LTL.LTLnRelease (x, y)));

fun rewrite_X_enat LTL.LTLnTrue = (LTL.LTLnTrue, Extended_Nat.Infinity_enat)
  | rewrite_X_enat LTL.LTLnFalse = (LTL.LTLnFalse, Extended_Nat.Infinity_enat)
  | rewrite_X_enat (LTL.LTLnProp a) = (LTL.LTLnProp a, Extended_Nat.zero_enat)
  | rewrite_X_enat (LTL.LTLnNProp a) = (LTL.LTLnNProp a, Extended_Nat.zero_enat)
  | rewrite_X_enat (LTL.LTLnAnd (phi, psi)) =
    combine mk_and (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (LTL.LTLnOr (phi, psi)) =
    combine mk_or (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (LTL.LTLnUntil (phi, psi)) =
    combine mk_until (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (LTL.LTLnRelease (phi, psi)) =
    combine mk_release (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (LTL.LTLnNext phi) = let
  val (phia, n) = rewrite_X_enat phi;
in
  (phia, Extended_Nat.eSuc n)
end;

fun rewrite_X phi =
  let
    val t = rewrite_X_enat phi;
  in
    mk_next_pow (the_enat_0 (Product_Type.snd t)) (Product_Type.fst t)
  end;

fun pure_universal A_ LTL.LTLnTrue = true
  | pure_universal A_ LTL.LTLnFalse = true
  | pure_universal A_ (LTL.LTLnAnd (nua, nu)) =
    pure_universal A_ nua andalso pure_universal A_ nu
  | pure_universal A_ (LTL.LTLnOr (nua, nu)) =
    pure_universal A_ nua andalso pure_universal A_ nu
  | pure_universal A_ (LTL.LTLnUntil (nua, nu)) =
    pure_universal A_ nua andalso pure_universal A_ nu
  | pure_universal A_ (LTL.LTLnRelease (nua, nu)) =
    LTL.equal_ltlna A_ nua LTL.LTLnFalse orelse pure_universal A_ nu
  | pure_universal A_ (LTL.LTLnNext nu) = pure_universal A_ nu
  | pure_universal A_ (LTL.LTLnProp v) = false
  | pure_universal A_ (LTL.LTLnNProp v) = false;

fun pure_eventual A_ LTL.LTLnTrue = true
  | pure_eventual A_ LTL.LTLnFalse = true
  | pure_eventual A_ (LTL.LTLnAnd (mua, mu)) =
    pure_eventual A_ mua andalso pure_eventual A_ mu
  | pure_eventual A_ (LTL.LTLnOr (mua, mu)) =
    pure_eventual A_ mua andalso pure_eventual A_ mu
  | pure_eventual A_ (LTL.LTLnUntil (mua, mu)) =
    LTL.equal_ltlna A_ mua LTL.LTLnTrue orelse pure_eventual A_ mu
  | pure_eventual A_ (LTL.LTLnRelease (mua, mu)) =
    pure_eventual A_ mua andalso pure_eventual A_ mu
  | pure_eventual A_ (LTL.LTLnNext mu) = pure_eventual A_ mu
  | pure_eventual A_ (LTL.LTLnProp v) = false
  | pure_eventual A_ (LTL.LTLnNProp v) = false;

fun suspendable A_ LTL.LTLnTrue = true
  | suspendable A_ LTL.LTLnFalse = true
  | suspendable A_ (LTL.LTLnAnd (xia, xi)) =
    suspendable A_ xia andalso suspendable A_ xi
  | suspendable A_ (LTL.LTLnOr (xia, xi)) =
    suspendable A_ xia andalso suspendable A_ xi
  | suspendable A_ (LTL.LTLnUntil (phi, xi)) =
    LTL.equal_ltlna A_ phi LTL.LTLnTrue andalso pure_universal A_ xi orelse
      suspendable A_ xi
  | suspendable A_ (LTL.LTLnRelease (phi, xi)) =
    LTL.equal_ltlna A_ phi LTL.LTLnFalse andalso pure_eventual A_ xi orelse
      suspendable A_ xi
  | suspendable A_ (LTL.LTLnNext xi) = suspendable A_ xi
  | suspendable A_ (LTL.LTLnProp v) = false
  | suspendable A_ (LTL.LTLnNProp v) = false;

fun rewrite_modal A_ LTL.LTLnTrue = LTL.LTLnTrue
  | rewrite_modal A_ LTL.LTLnFalse = LTL.LTLnFalse
  | rewrite_modal A_ (LTL.LTLnAnd (phi, psi)) =
    LTL.LTLnAnd (rewrite_modal A_ phi, rewrite_modal A_ psi)
  | rewrite_modal A_ (LTL.LTLnOr (phi, psi)) =
    LTL.LTLnOr (rewrite_modal A_ phi, rewrite_modal A_ psi)
  | rewrite_modal A_ (LTL.LTLnUntil (phi, psi)) =
    (if pure_eventual A_ psi orelse suspendable A_ psi then rewrite_modal A_ psi
      else LTL.LTLnUntil (rewrite_modal A_ phi, rewrite_modal A_ psi))
  | rewrite_modal A_ (LTL.LTLnRelease (phi, psi)) =
    (if pure_universal A_ psi orelse suspendable A_ psi
      then rewrite_modal A_ psi
      else LTL.LTLnRelease (rewrite_modal A_ phi, rewrite_modal A_ psi))
  | rewrite_modal A_ (LTL.LTLnNext phi) =
    (if suspendable A_ phi then rewrite_modal A_ phi
      else LTL.LTLnNext (rewrite_modal A_ phi))
  | rewrite_modal A_ (LTL.LTLnProp v) = LTL.LTLnProp v
  | rewrite_modal A_ (LTL.LTLnNProp v) = LTL.LTLnNProp v;

fun syntactical_implies_i_i A_ x xa =
  Predicate.sup_pred
    (Predicate.bind (Predicate.single (x, xa))
      (fn a =>
        (case a of (_, LTL.LTLnTrue) => Predicate.single ()
          | (_, LTL.LTLnFalse) => Predicate.bot_pred
          | (_, LTL.LTLnProp _) => Predicate.bot_pred
          | (_, LTL.LTLnNProp _) => Predicate.bot_pred
          | (_, LTL.LTLnAnd (_, _)) => Predicate.bot_pred
          | (_, LTL.LTLnOr (_, _)) => Predicate.bot_pred
          | (_, LTL.LTLnNext _) => Predicate.bot_pred
          | (_, LTL.LTLnUntil (_, _)) => Predicate.bot_pred
          | (_, LTL.LTLnRelease (_, _)) => Predicate.bot_pred)))
    (Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fn a =>
          (case a of (LTL.LTLnTrue, _) => Predicate.bot_pred
            | (LTL.LTLnFalse, _) => Predicate.single ()
            | (LTL.LTLnProp _, _) => Predicate.bot_pred
            | (LTL.LTLnNProp _, _) => Predicate.bot_pred
            | (LTL.LTLnAnd (_, _), _) => Predicate.bot_pred
            | (LTL.LTLnOr (_, _), _) => Predicate.bot_pred
            | (LTL.LTLnNext _, _) => Predicate.bot_pred
            | (LTL.LTLnUntil (_, _), _) => Predicate.bot_pred
            | (LTL.LTLnRelease (_, _), _) => Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fn (phi, phia) =>
            (if LTL.equal_ltlna A_ phi phia
              then Predicate.bind (eq_i_i (LTL.equal_ltln A_) phi phi)
                     (fn () => Predicate.single ())
              else Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, xa))
            (fn a =>
              (case a of (LTL.LTLnTrue, _) => Predicate.bot_pred
                | (LTL.LTLnFalse, _) => Predicate.bot_pred
                | (LTL.LTLnProp _, _) => Predicate.bot_pred
                | (LTL.LTLnNProp _, _) => Predicate.bot_pred
                | (LTL.LTLnAnd (phi, _), chi) =>
                  Predicate.bind (syntactical_implies_i_i A_ phi chi)
                    (fn () => Predicate.single ())
                | (LTL.LTLnOr (_, _), _) => Predicate.bot_pred
                | (LTL.LTLnNext _, _) => Predicate.bot_pred
                | (LTL.LTLnUntil (_, _), _) => Predicate.bot_pred
                | (LTL.LTLnRelease (_, _), _) => Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, xa))
              (fn a =>
                (case a of (LTL.LTLnTrue, _) => Predicate.bot_pred
                  | (LTL.LTLnFalse, _) => Predicate.bot_pred
                  | (LTL.LTLnProp _, _) => Predicate.bot_pred
                  | (LTL.LTLnNProp _, _) => Predicate.bot_pred
                  | (LTL.LTLnAnd (_, psi), chi) =>
                    Predicate.bind (syntactical_implies_i_i A_ psi chi)
                      (fn () => Predicate.single ())
                  | (LTL.LTLnOr (_, _), _) => Predicate.bot_pred
                  | (LTL.LTLnNext _, _) => Predicate.bot_pred
                  | (LTL.LTLnUntil (_, _), _) => Predicate.bot_pred
                  | (LTL.LTLnRelease (_, _), _) => Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, xa))
                (fn a =>
                  (case a of (_, LTL.LTLnTrue) => Predicate.bot_pred
                    | (_, LTL.LTLnFalse) => Predicate.bot_pred
                    | (_, LTL.LTLnProp _) => Predicate.bot_pred
                    | (_, LTL.LTLnNProp _) => Predicate.bot_pred
                    | (phi, LTL.LTLnAnd (psi, chi)) =>
                      Predicate.bind (syntactical_implies_i_i A_ phi psi)
                        (fn () =>
                          Predicate.bind (syntactical_implies_i_i A_ phi chi)
                            (fn () => Predicate.single ()))
                    | (_, LTL.LTLnOr (_, _)) => Predicate.bot_pred
                    | (_, LTL.LTLnNext _) => Predicate.bot_pred
                    | (_, LTL.LTLnUntil (_, _)) => Predicate.bot_pred
                    | (_, LTL.LTLnRelease (_, _)) => Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, xa))
                  (fn a =>
                    (case a of (_, LTL.LTLnTrue) => Predicate.bot_pred
                      | (_, LTL.LTLnFalse) => Predicate.bot_pred
                      | (_, LTL.LTLnProp _) => Predicate.bot_pred
                      | (_, LTL.LTLnNProp _) => Predicate.bot_pred
                      | (_, LTL.LTLnAnd (_, _)) => Predicate.bot_pred
                      | (phi, LTL.LTLnOr (psi, _)) =>
                        Predicate.bind (syntactical_implies_i_i A_ phi psi)
                          (fn () => Predicate.single ())
                      | (_, LTL.LTLnNext _) => Predicate.bot_pred
                      | (_, LTL.LTLnUntil (_, _)) => Predicate.bot_pred
                      | (_, LTL.LTLnRelease (_, _)) => Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single (x, xa))
                    (fn a =>
                      (case a of (_, LTL.LTLnTrue) => Predicate.bot_pred
                        | (_, LTL.LTLnFalse) => Predicate.bot_pred
                        | (_, LTL.LTLnProp _) => Predicate.bot_pred
                        | (_, LTL.LTLnNProp _) => Predicate.bot_pred
                        | (_, LTL.LTLnAnd (_, _)) => Predicate.bot_pred
                        | (phi, LTL.LTLnOr (_, chi)) =>
                          Predicate.bind (syntactical_implies_i_i A_ phi chi)
                            (fn () => Predicate.single ())
                        | (_, LTL.LTLnNext _) => Predicate.bot_pred
                        | (_, LTL.LTLnUntil (_, _)) => Predicate.bot_pred
                        | (_, LTL.LTLnRelease (_, _)) => Predicate.bot_pred)))
                  (Predicate.sup_pred
                    (Predicate.bind (Predicate.single (x, xa))
                      (fn a =>
                        (case a of (LTL.LTLnTrue, _) => Predicate.bot_pred
                          | (LTL.LTLnFalse, _) => Predicate.bot_pred
                          | (LTL.LTLnProp _, _) => Predicate.bot_pred
                          | (LTL.LTLnNProp _, _) => Predicate.bot_pred
                          | (LTL.LTLnAnd (_, _), _) => Predicate.bot_pred
                          | (LTL.LTLnOr (phi, psi), chi) =>
                            Predicate.bind (syntactical_implies_i_i A_ phi chi)
                              (fn () =>
                                Predicate.bind
                                  (syntactical_implies_i_i A_ psi chi)
                                  (fn () => Predicate.single ()))
                          | (LTL.LTLnNext _, _) => Predicate.bot_pred
                          | (LTL.LTLnUntil (_, _), _) => Predicate.bot_pred
                          | (LTL.LTLnRelease (_, _), _) => Predicate.bot_pred)))
                    (Predicate.sup_pred
                      (Predicate.bind (Predicate.single (x, xa))
                        (fn a =>
                          (case a of (_, LTL.LTLnTrue) => Predicate.bot_pred
                            | (_, LTL.LTLnFalse) => Predicate.bot_pred
                            | (_, LTL.LTLnProp _) => Predicate.bot_pred
                            | (_, LTL.LTLnNProp _) => Predicate.bot_pred
                            | (_, LTL.LTLnAnd (_, _)) => Predicate.bot_pred
                            | (_, LTL.LTLnOr (_, _)) => Predicate.bot_pred
                            | (_, LTL.LTLnNext _) => Predicate.bot_pred
                            | (phi, LTL.LTLnUntil (_, chi)) =>
                              Predicate.bind
                                (syntactical_implies_i_i A_ phi chi)
                                (fn () => Predicate.single ())
                            | (_, LTL.LTLnRelease (_, _)) =>
                              Predicate.bot_pred)))
                      (Predicate.sup_pred
                        (Predicate.bind (Predicate.single (x, xa))
                          (fn a =>
                            (case a of (LTL.LTLnTrue, _) => Predicate.bot_pred
                              | (LTL.LTLnFalse, _) => Predicate.bot_pred
                              | (LTL.LTLnProp _, _) => Predicate.bot_pred
                              | (LTL.LTLnNProp _, _) => Predicate.bot_pred
                              | (LTL.LTLnAnd (_, _), _) => Predicate.bot_pred
                              | (LTL.LTLnOr (_, _), _) => Predicate.bot_pred
                              | (LTL.LTLnNext _, _) => Predicate.bot_pred
                              | (LTL.LTLnUntil (phi, psi), chi) =>
                                Predicate.bind
                                  (syntactical_implies_i_i A_ phi chi)
                                  (fn () =>
                                    Predicate.bind
                                      (syntactical_implies_i_i A_ psi chi)
                                      (fn () => Predicate.single ()))
                              | (LTL.LTLnRelease (_, _), _) =>
                                Predicate.bot_pred)))
                        (Predicate.sup_pred
                          (Predicate.bind (Predicate.single (x, xa))
                            (fn a =>
                              (case a of (LTL.LTLnTrue, _) => Predicate.bot_pred
                                | (LTL.LTLnFalse, _) => Predicate.bot_pred
                                | (LTL.LTLnProp _, _) => Predicate.bot_pred
                                | (LTL.LTLnNProp _, _) => Predicate.bot_pred
                                | (LTL.LTLnAnd (_, _), _) => Predicate.bot_pred
                                | (LTL.LTLnOr (_, _), _) => Predicate.bot_pred
                                | (LTL.LTLnNext _, _) => Predicate.bot_pred
                                | (LTL.LTLnUntil (_, _), LTL.LTLnTrue) =>
                                  Predicate.bot_pred
                                | (LTL.LTLnUntil (_, _), LTL.LTLnFalse) =>
                                  Predicate.bot_pred
                                | (LTL.LTLnUntil (_, _), LTL.LTLnProp _) =>
                                  Predicate.bot_pred
                                | (LTL.LTLnUntil (_, _), LTL.LTLnNProp _) =>
                                  Predicate.bot_pred
                                | (LTL.LTLnUntil (_, _), LTL.LTLnAnd (_, _)) =>
                                  Predicate.bot_pred
                                | (LTL.LTLnUntil (_, _), LTL.LTLnOr (_, _)) =>
                                  Predicate.bot_pred
                                | (LTL.LTLnUntil (_, _), LTL.LTLnNext _) =>
                                  Predicate.bot_pred
                                | (LTL.LTLnUntil (phi, psi),
                                    LTL.LTLnUntil (chi, nu))
                                  => Predicate.bind
                                       (syntactical_implies_i_i A_ phi chi)
                                       (fn () =>
 Predicate.bind (syntactical_implies_i_i A_ psi nu)
   (fn () => Predicate.single ()))
                                | (LTL.LTLnUntil (_, _), LTL.LTLnRelease (_, _))
                                  => Predicate.bot_pred
                                | (LTL.LTLnRelease (_, _), _) =>
                                  Predicate.bot_pred)))
                          (Predicate.sup_pred
                            (Predicate.bind (Predicate.single (x, xa))
                              (fn a =>
                                (case a
                                  of (LTL.LTLnTrue, _) => Predicate.bot_pred
                                  | (LTL.LTLnFalse, _) => Predicate.bot_pred
                                  | (LTL.LTLnProp _, _) => Predicate.bot_pred
                                  | (LTL.LTLnNProp _, _) => Predicate.bot_pred
                                  | (LTL.LTLnAnd (_, _), _) =>
                                    Predicate.bot_pred
                                  | (LTL.LTLnOr (_, _), _) => Predicate.bot_pred
                                  | (LTL.LTLnNext _, _) => Predicate.bot_pred
                                  | (LTL.LTLnUntil (_, _), _) =>
                                    Predicate.bot_pred
                                  | (LTL.LTLnRelease (_, chi), phi) =>
                                    Predicate.bind
                                      (syntactical_implies_i_i A_ chi phi)
                                      (fn () => Predicate.single ()))))
                            (Predicate.sup_pred
                              (Predicate.bind (Predicate.single (x, xa))
                                (fn a =>
                                  (case a
                                    of (_, LTL.LTLnTrue) => Predicate.bot_pred
                                    | (_, LTL.LTLnFalse) => Predicate.bot_pred
                                    | (_, LTL.LTLnProp _) => Predicate.bot_pred
                                    | (_, LTL.LTLnNProp _) => Predicate.bot_pred
                                    | (_, LTL.LTLnAnd (_, _)) =>
                                      Predicate.bot_pred
                                    | (_, LTL.LTLnOr (_, _)) =>
                                      Predicate.bot_pred
                                    | (_, LTL.LTLnNext _) => Predicate.bot_pred
                                    | (_, LTL.LTLnUntil (_, _)) =>
                                      Predicate.bot_pred
                                    | (chi, LTL.LTLnRelease (phi, psi)) =>
                                      Predicate.bind
(syntactical_implies_i_i A_ chi phi)
(fn () =>
  Predicate.bind (syntactical_implies_i_i A_ chi psi)
    (fn () => Predicate.single ())))))
                              (Predicate.sup_pred
                                (Predicate.bind (Predicate.single (x, xa))
                                  (fn a =>
                                    (case a
                                      of (LTL.LTLnTrue, _) => Predicate.bot_pred
                                      | (LTL.LTLnFalse, _) => Predicate.bot_pred
                                      | (LTL.LTLnProp _, _) =>
Predicate.bot_pred
                                      | (LTL.LTLnNProp _, _) =>
Predicate.bot_pred
                                      | (LTL.LTLnAnd (_, _), _) =>
Predicate.bot_pred
                                      | (LTL.LTLnOr (_, _), _) =>
Predicate.bot_pred
                                      | (LTL.LTLnNext _, _) =>
Predicate.bot_pred
                                      | (LTL.LTLnUntil (_, _), _) =>
Predicate.bot_pred
                                      | (LTL.LTLnRelease (_, _), LTL.LTLnTrue)
=> Predicate.bot_pred
                                      | (LTL.LTLnRelease (_, _), LTL.LTLnFalse)
=> Predicate.bot_pred
                                      | (LTL.LTLnRelease (_, _), LTL.LTLnProp _)
=> Predicate.bot_pred
                                      |
(LTL.LTLnRelease (_, _), LTL.LTLnNProp _) => Predicate.bot_pred
                                      |
(LTL.LTLnRelease (_, _), LTL.LTLnAnd (_, _)) => Predicate.bot_pred
                                      |
(LTL.LTLnRelease (_, _), LTL.LTLnOr (_, _)) => Predicate.bot_pred
                                      | (LTL.LTLnRelease (_, _), LTL.LTLnNext _)
=> Predicate.bot_pred
                                      |
(LTL.LTLnRelease (_, _), LTL.LTLnUntil (_, _)) => Predicate.bot_pred
                                      |
(LTL.LTLnRelease (phi, psi), LTL.LTLnRelease (chi, nu)) =>
Predicate.bind (syntactical_implies_i_i A_ phi chi)
  (fn () =>
    Predicate.bind (syntactical_implies_i_i A_ psi nu)
      (fn () => Predicate.single ())))))
                                (Predicate.sup_pred
                                  (Predicate.bind (Predicate.single (x, xa))
                                    (fn a =>
                                      (case a
of (LTL.LTLnTrue, _) => Predicate.bot_pred
| (LTL.LTLnFalse, _) => Predicate.bot_pred
| (LTL.LTLnProp _, _) => Predicate.bot_pred
| (LTL.LTLnNProp _, _) => Predicate.bot_pred
| (LTL.LTLnAnd (_, _), _) => Predicate.bot_pred
| (LTL.LTLnOr (_, _), _) => Predicate.bot_pred
| (LTL.LTLnNext _, _) => Predicate.bot_pred
| (LTL.LTLnUntil (_, _), _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnTrue, _), _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnFalse, _), LTL.LTLnTrue) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnFalse, _), LTL.LTLnFalse) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnFalse, _), LTL.LTLnProp _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnFalse, _), LTL.LTLnNProp _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnFalse, _), LTL.LTLnAnd (_, _)) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnFalse, _), LTL.LTLnOr (_, _)) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnFalse, phi), LTL.LTLnNext psi) =>
  Predicate.bind
    (syntactical_implies_i_i A_ (LTL.LTLnRelease (LTL.LTLnFalse, phi)) psi)
    (fn () => Predicate.single ())
| (LTL.LTLnRelease (LTL.LTLnFalse, _), LTL.LTLnUntil (_, _)) =>
  Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnFalse, _), LTL.LTLnRelease (_, _)) =>
  Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnProp _, _), _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnNProp _, _), _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnAnd (_, _), _), _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnOr (_, _), _), _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnNext _, _), _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnUntil (_, _), _), _) => Predicate.bot_pred
| (LTL.LTLnRelease (LTL.LTLnRelease (_, _), _), _) => Predicate.bot_pred)))
                                  (Predicate.sup_pred
                                    (Predicate.bind (Predicate.single (x, xa))
                                      (fn a =>
(case a of (LTL.LTLnTrue, _) => Predicate.bot_pred
  | (LTL.LTLnFalse, _) => Predicate.bot_pred
  | (LTL.LTLnProp _, _) => Predicate.bot_pred
  | (LTL.LTLnNProp _, _) => Predicate.bot_pred
  | (LTL.LTLnAnd (_, _), _) => Predicate.bot_pred
  | (LTL.LTLnOr (_, _), _) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnTrue) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnFalse) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnProp _) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnNProp _) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnAnd (_, _)) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnOr (_, _)) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnNext _) => Predicate.bot_pred
  | (LTL.LTLnNext phi, LTL.LTLnUntil (LTL.LTLnTrue, psi)) =>
    Predicate.bind
      (syntactical_implies_i_i A_ phi (LTL.LTLnUntil (LTL.LTLnTrue, psi)))
      (fn () => Predicate.single ())
  | (LTL.LTLnNext _, LTL.LTLnUntil (LTL.LTLnFalse, _)) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnUntil (LTL.LTLnProp _, _)) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnUntil (LTL.LTLnNProp _, _)) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnUntil (LTL.LTLnAnd (_, _), _)) =>
    Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnUntil (LTL.LTLnOr (_, _), _)) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnUntil (LTL.LTLnNext _, _)) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnUntil (LTL.LTLnUntil (_, _), _)) =>
    Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnUntil (LTL.LTLnRelease (_, _), _)) =>
    Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnRelease (_, _)) => Predicate.bot_pred
  | (LTL.LTLnUntil (_, _), _) => Predicate.bot_pred
  | (LTL.LTLnRelease (_, _), _) => Predicate.bot_pred)))
                                    (Predicate.bind (Predicate.single (x, xa))
                                      (fn a =>
(case a of (LTL.LTLnTrue, _) => Predicate.bot_pred
  | (LTL.LTLnFalse, _) => Predicate.bot_pred
  | (LTL.LTLnProp _, _) => Predicate.bot_pred
  | (LTL.LTLnNProp _, _) => Predicate.bot_pred
  | (LTL.LTLnAnd (_, _), _) => Predicate.bot_pred
  | (LTL.LTLnOr (_, _), _) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnTrue) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnFalse) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnProp _) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnNProp _) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnAnd (_, _)) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnOr (_, _)) => Predicate.bot_pred
  | (LTL.LTLnNext phi, LTL.LTLnNext psi) =>
    Predicate.bind (syntactical_implies_i_i A_ phi psi)
      (fn () => Predicate.single ())
  | (LTL.LTLnNext _, LTL.LTLnUntil (_, _)) => Predicate.bot_pred
  | (LTL.LTLnNext _, LTL.LTLnRelease (_, _)) => Predicate.bot_pred
  | (LTL.LTLnUntil (_, _), _) => Predicate.bot_pred
  | (LTL.LTLnRelease (_, _), _) => Predicate.bot_pred)))))))))))))))))));

fun syntactical_implies A_ x1 x2 =
  Predicate.holds (syntactical_implies_i_i A_ x1 x2);

fun rewrite_syn_imp A_ (LTL.LTLnAnd (phi, psi)) =
  (if syntactical_implies A_ phi psi then rewrite_syn_imp A_ phi
    else (if syntactical_implies A_ psi phi then rewrite_syn_imp A_ psi
           else (if syntactical_implies A_ phi (LTL.not_n psi) orelse
                      syntactical_implies A_ psi (LTL.not_n phi)
                  then LTL.LTLnFalse
                  else mk_and (rewrite_syn_imp A_ phi)
                         (rewrite_syn_imp A_ psi))))
  | rewrite_syn_imp A_ (LTL.LTLnOr (phi, psi)) =
    (if syntactical_implies A_ phi psi then rewrite_syn_imp A_ psi
      else (if syntactical_implies A_ psi phi then rewrite_syn_imp A_ phi
             else (if syntactical_implies A_ (LTL.not_n phi) psi orelse
                        syntactical_implies A_ (LTL.not_n psi) phi
                    then LTL.LTLnTrue
                    else mk_or (rewrite_syn_imp A_ phi)
                           (rewrite_syn_imp A_ psi))))
  | rewrite_syn_imp A_ (LTL.LTLnUntil (phi, psi)) =
    (if syntactical_implies A_ phi psi then rewrite_syn_imp A_ psi
      else (if syntactical_implies A_ (LTL.not_n phi) psi
             then mk_until LTL.LTLnTrue (rewrite_syn_imp A_ psi)
             else mk_until (rewrite_syn_imp A_ phi) (rewrite_syn_imp A_ psi)))
  | rewrite_syn_imp A_ (LTL.LTLnRelease (phi, psi)) =
    (if syntactical_implies A_ psi phi then rewrite_syn_imp A_ psi
      else (if syntactical_implies A_ psi (LTL.not_n phi)
             then mk_release LTL.LTLnFalse (rewrite_syn_imp A_ psi)
             else mk_release (rewrite_syn_imp A_ phi) (rewrite_syn_imp A_ psi)))
  | rewrite_syn_imp A_ (LTL.LTLnNext phi) = mk_next (rewrite_syn_imp A_ phi)
  | rewrite_syn_imp A_ LTL.LTLnTrue = LTL.LTLnTrue
  | rewrite_syn_imp A_ LTL.LTLnFalse = LTL.LTLnFalse
  | rewrite_syn_imp A_ (LTL.LTLnProp v) = LTL.LTLnProp v
  | rewrite_syn_imp A_ (LTL.LTLnNProp v) = LTL.LTLnNProp v;

fun rewrite_iter_slow A_ phi =
  iterate (LTL.equal_ltln A_)
    (rewrite_syn_imp A_ o rewrite_modal A_ o rewrite_X) phi (LTL.size_ltln phi);

end; (*struct LTL_Rewrite*)

structure LTL_Example : sig
  val rewrite : string LTL.ltlc -> Arith.nat LTL.ltln
end = struct

fun rewrite x =
  (LTL_Rewrite.rewrite_iter_slow Arith.equal_nat o LTL.ltlc_to_ltln o
    LTL.map_ltlc Stringa.size_literal)
    x;

end; (*struct LTL_Example*)
