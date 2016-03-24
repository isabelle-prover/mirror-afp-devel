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
  datatype 'a ltln = True_ltln | False_ltln | Prop_ltln of 'a | Nprop_ltln of 'a
    | And_ltln of 'a ltln * 'a ltln | Or_ltln of 'a ltln * 'a ltln |
    Next_ltln of 'a ltln | Until_ltln of 'a ltln * 'a ltln |
    Release_ltln of 'a ltln * 'a ltln
  val equal_ltlna : 'a HOL.equal -> 'a ltln -> 'a ltln -> bool
  val equal_ltln : 'a HOL.equal -> 'a ltln HOL.equal
  datatype 'a ltlc = True_ltlc | False_ltlc | Prop_ltlc of 'a |
    Not_ltlc of 'a ltlc | And_ltlc of 'a ltlc * 'a ltlc |
    Or_ltlc of 'a ltlc * 'a ltlc | Implies_ltlc of 'a ltlc * 'a ltlc |
    Next_ltlc of 'a ltlc | Final_ltlc of 'a ltlc | Global_ltlc of 'a ltlc |
    Until_ltlc of 'a ltlc * 'a ltlc | Release_ltlc of 'a ltlc * 'a ltlc
  val iff_ltlc : 'a ltlc -> 'a ltlc -> 'a ltlc
  val not_n : 'a ltln -> 'a ltln
  val ltlc_to_ltln : 'a ltlc -> 'a ltln
  val map_ltlc : ('a -> 'b) -> 'a ltlc -> 'b ltlc
  val size_ltln : 'a ltln -> Arith.nat
end = struct

datatype 'a ltln = True_ltln | False_ltln | Prop_ltln of 'a | Nprop_ltln of 'a |
  And_ltln of 'a ltln * 'a ltln | Or_ltln of 'a ltln * 'a ltln |
  Next_ltln of 'a ltln | Until_ltln of 'a ltln * 'a ltln |
  Release_ltln of 'a ltln * 'a ltln;

fun equal_ltlna A_ (Until_ltln (x81, x82)) (Release_ltln (x91, x92)) = false
  | equal_ltlna A_ (Release_ltln (x91, x92)) (Until_ltln (x81, x82)) = false
  | equal_ltlna A_ (Next_ltln x7) (Release_ltln (x91, x92)) = false
  | equal_ltlna A_ (Release_ltln (x91, x92)) (Next_ltln x7) = false
  | equal_ltlna A_ (Next_ltln x7) (Until_ltln (x81, x82)) = false
  | equal_ltlna A_ (Until_ltln (x81, x82)) (Next_ltln x7) = false
  | equal_ltlna A_ (Or_ltln (x61, x62)) (Release_ltln (x91, x92)) = false
  | equal_ltlna A_ (Release_ltln (x91, x92)) (Or_ltln (x61, x62)) = false
  | equal_ltlna A_ (Or_ltln (x61, x62)) (Until_ltln (x81, x82)) = false
  | equal_ltlna A_ (Until_ltln (x81, x82)) (Or_ltln (x61, x62)) = false
  | equal_ltlna A_ (Or_ltln (x61, x62)) (Next_ltln x7) = false
  | equal_ltlna A_ (Next_ltln x7) (Or_ltln (x61, x62)) = false
  | equal_ltlna A_ (And_ltln (x51, x52)) (Release_ltln (x91, x92)) = false
  | equal_ltlna A_ (Release_ltln (x91, x92)) (And_ltln (x51, x52)) = false
  | equal_ltlna A_ (And_ltln (x51, x52)) (Until_ltln (x81, x82)) = false
  | equal_ltlna A_ (Until_ltln (x81, x82)) (And_ltln (x51, x52)) = false
  | equal_ltlna A_ (And_ltln (x51, x52)) (Next_ltln x7) = false
  | equal_ltlna A_ (Next_ltln x7) (And_ltln (x51, x52)) = false
  | equal_ltlna A_ (And_ltln (x51, x52)) (Or_ltln (x61, x62)) = false
  | equal_ltlna A_ (Or_ltln (x61, x62)) (And_ltln (x51, x52)) = false
  | equal_ltlna A_ (Nprop_ltln x4) (Release_ltln (x91, x92)) = false
  | equal_ltlna A_ (Release_ltln (x91, x92)) (Nprop_ltln x4) = false
  | equal_ltlna A_ (Nprop_ltln x4) (Until_ltln (x81, x82)) = false
  | equal_ltlna A_ (Until_ltln (x81, x82)) (Nprop_ltln x4) = false
  | equal_ltlna A_ (Nprop_ltln x4) (Next_ltln x7) = false
  | equal_ltlna A_ (Next_ltln x7) (Nprop_ltln x4) = false
  | equal_ltlna A_ (Nprop_ltln x4) (Or_ltln (x61, x62)) = false
  | equal_ltlna A_ (Or_ltln (x61, x62)) (Nprop_ltln x4) = false
  | equal_ltlna A_ (Nprop_ltln x4) (And_ltln (x51, x52)) = false
  | equal_ltlna A_ (And_ltln (x51, x52)) (Nprop_ltln x4) = false
  | equal_ltlna A_ (Prop_ltln x3) (Release_ltln (x91, x92)) = false
  | equal_ltlna A_ (Release_ltln (x91, x92)) (Prop_ltln x3) = false
  | equal_ltlna A_ (Prop_ltln x3) (Until_ltln (x81, x82)) = false
  | equal_ltlna A_ (Until_ltln (x81, x82)) (Prop_ltln x3) = false
  | equal_ltlna A_ (Prop_ltln x3) (Next_ltln x7) = false
  | equal_ltlna A_ (Next_ltln x7) (Prop_ltln x3) = false
  | equal_ltlna A_ (Prop_ltln x3) (Or_ltln (x61, x62)) = false
  | equal_ltlna A_ (Or_ltln (x61, x62)) (Prop_ltln x3) = false
  | equal_ltlna A_ (Prop_ltln x3) (And_ltln (x51, x52)) = false
  | equal_ltlna A_ (And_ltln (x51, x52)) (Prop_ltln x3) = false
  | equal_ltlna A_ (Prop_ltln x3) (Nprop_ltln x4) = false
  | equal_ltlna A_ (Nprop_ltln x4) (Prop_ltln x3) = false
  | equal_ltlna A_ False_ltln (Release_ltln (x91, x92)) = false
  | equal_ltlna A_ (Release_ltln (x91, x92)) False_ltln = false
  | equal_ltlna A_ False_ltln (Until_ltln (x81, x82)) = false
  | equal_ltlna A_ (Until_ltln (x81, x82)) False_ltln = false
  | equal_ltlna A_ False_ltln (Next_ltln x7) = false
  | equal_ltlna A_ (Next_ltln x7) False_ltln = false
  | equal_ltlna A_ False_ltln (Or_ltln (x61, x62)) = false
  | equal_ltlna A_ (Or_ltln (x61, x62)) False_ltln = false
  | equal_ltlna A_ False_ltln (And_ltln (x51, x52)) = false
  | equal_ltlna A_ (And_ltln (x51, x52)) False_ltln = false
  | equal_ltlna A_ False_ltln (Nprop_ltln x4) = false
  | equal_ltlna A_ (Nprop_ltln x4) False_ltln = false
  | equal_ltlna A_ False_ltln (Prop_ltln x3) = false
  | equal_ltlna A_ (Prop_ltln x3) False_ltln = false
  | equal_ltlna A_ True_ltln (Release_ltln (x91, x92)) = false
  | equal_ltlna A_ (Release_ltln (x91, x92)) True_ltln = false
  | equal_ltlna A_ True_ltln (Until_ltln (x81, x82)) = false
  | equal_ltlna A_ (Until_ltln (x81, x82)) True_ltln = false
  | equal_ltlna A_ True_ltln (Next_ltln x7) = false
  | equal_ltlna A_ (Next_ltln x7) True_ltln = false
  | equal_ltlna A_ True_ltln (Or_ltln (x61, x62)) = false
  | equal_ltlna A_ (Or_ltln (x61, x62)) True_ltln = false
  | equal_ltlna A_ True_ltln (And_ltln (x51, x52)) = false
  | equal_ltlna A_ (And_ltln (x51, x52)) True_ltln = false
  | equal_ltlna A_ True_ltln (Nprop_ltln x4) = false
  | equal_ltlna A_ (Nprop_ltln x4) True_ltln = false
  | equal_ltlna A_ True_ltln (Prop_ltln x3) = false
  | equal_ltlna A_ (Prop_ltln x3) True_ltln = false
  | equal_ltlna A_ True_ltln False_ltln = false
  | equal_ltlna A_ False_ltln True_ltln = false
  | equal_ltlna A_ (Release_ltln (x91, x92)) (Release_ltln (y91, y92)) =
    equal_ltlna A_ x91 y91 andalso equal_ltlna A_ x92 y92
  | equal_ltlna A_ (Until_ltln (x81, x82)) (Until_ltln (y81, y82)) =
    equal_ltlna A_ x81 y81 andalso equal_ltlna A_ x82 y82
  | equal_ltlna A_ (Next_ltln x7) (Next_ltln y7) = equal_ltlna A_ x7 y7
  | equal_ltlna A_ (Or_ltln (x61, x62)) (Or_ltln (y61, y62)) =
    equal_ltlna A_ x61 y61 andalso equal_ltlna A_ x62 y62
  | equal_ltlna A_ (And_ltln (x51, x52)) (And_ltln (y51, y52)) =
    equal_ltlna A_ x51 y51 andalso equal_ltlna A_ x52 y52
  | equal_ltlna A_ (Nprop_ltln x4) (Nprop_ltln y4) = HOL.eq A_ x4 y4
  | equal_ltlna A_ (Prop_ltln x3) (Prop_ltln y3) = HOL.eq A_ x3 y3
  | equal_ltlna A_ False_ltln False_ltln = true
  | equal_ltlna A_ True_ltln True_ltln = true;

fun equal_ltln A_ = {equal = equal_ltlna A_} : 'a ltln HOL.equal;

datatype 'a ltlc = True_ltlc | False_ltlc | Prop_ltlc of 'a |
  Not_ltlc of 'a ltlc | And_ltlc of 'a ltlc * 'a ltlc |
  Or_ltlc of 'a ltlc * 'a ltlc | Implies_ltlc of 'a ltlc * 'a ltlc |
  Next_ltlc of 'a ltlc | Final_ltlc of 'a ltlc | Global_ltlc of 'a ltlc |
  Until_ltlc of 'a ltlc * 'a ltlc | Release_ltlc of 'a ltlc * 'a ltlc;

fun iff_ltlc phi psi =
  And_ltlc (Implies_ltlc (phi, psi), Implies_ltlc (psi, phi));

fun not_n True_ltln = False_ltln
  | not_n False_ltln = True_ltln
  | not_n (Prop_ltln a) = Nprop_ltln a
  | not_n (Nprop_ltln a) = Prop_ltln a
  | not_n (And_ltln (phi, psi)) = Or_ltln (not_n phi, not_n psi)
  | not_n (Or_ltln (phi, psi)) = And_ltln (not_n phi, not_n psi)
  | not_n (Until_ltln (phi, psi)) = Release_ltln (not_n phi, not_n psi)
  | not_n (Release_ltln (phi, psi)) = Until_ltln (not_n phi, not_n psi)
  | not_n (Next_ltln phi) = Next_ltln (not_n phi);

fun ltlc_to_ltlna false True_ltlc = True_ltln
  | ltlc_to_ltlna false False_ltlc = False_ltln
  | ltlc_to_ltlna false (Prop_ltlc q) = Prop_ltln q
  | ltlc_to_ltlna false (And_ltlc (phi, psi)) =
    And_ltln (ltlc_to_ltlna false phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna false (Or_ltlc (phi, psi)) =
    Or_ltln (ltlc_to_ltlna false phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna false (Implies_ltlc (phi, psi)) =
    Or_ltln (ltlc_to_ltlna true phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna false (Final_ltlc phi) =
    Until_ltln (True_ltln, ltlc_to_ltlna false phi)
  | ltlc_to_ltlna false (Global_ltlc phi) =
    Release_ltln (False_ltln, ltlc_to_ltlna false phi)
  | ltlc_to_ltlna false (Until_ltlc (phi, psi)) =
    Until_ltln (ltlc_to_ltlna false phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna false (Release_ltlc (phi, psi)) =
    Release_ltln (ltlc_to_ltlna false phi, ltlc_to_ltlna false psi)
  | ltlc_to_ltlna true True_ltlc = False_ltln
  | ltlc_to_ltlna true False_ltlc = True_ltln
  | ltlc_to_ltlna true (Prop_ltlc q) = Nprop_ltln q
  | ltlc_to_ltlna true (And_ltlc (nu, mu)) =
    Or_ltln (ltlc_to_ltlna true nu, ltlc_to_ltlna true mu)
  | ltlc_to_ltlna true (Or_ltlc (nu, mu)) =
    And_ltln (ltlc_to_ltlna true nu, ltlc_to_ltlna true mu)
  | ltlc_to_ltlna true (Implies_ltlc (phi, psi)) =
    And_ltln (ltlc_to_ltlna false phi, ltlc_to_ltlna true psi)
  | ltlc_to_ltlna true (Final_ltlc phi) =
    Release_ltln (False_ltln, ltlc_to_ltlna true phi)
  | ltlc_to_ltlna true (Global_ltlc phi) =
    Until_ltln (True_ltln, ltlc_to_ltlna true phi)
  | ltlc_to_ltlna true (Until_ltlc (nu, mu)) =
    Release_ltln (ltlc_to_ltlna true nu, ltlc_to_ltlna true mu)
  | ltlc_to_ltlna true (Release_ltlc (nu, mu)) =
    Until_ltln (ltlc_to_ltlna true nu, ltlc_to_ltlna true mu)
  | ltlc_to_ltlna b (Not_ltlc psi) = ltlc_to_ltlna (not b) psi
  | ltlc_to_ltlna b (Next_ltlc phi) = Next_ltln (ltlc_to_ltlna b phi);

fun ltlc_to_ltln phi = ltlc_to_ltlna false phi;

fun map_ltlc f True_ltlc = True_ltlc
  | map_ltlc f False_ltlc = False_ltlc
  | map_ltlc f (Prop_ltlc x3) = Prop_ltlc (f x3)
  | map_ltlc f (Not_ltlc x4) = Not_ltlc (map_ltlc f x4)
  | map_ltlc f (And_ltlc (x51, x52)) = And_ltlc (map_ltlc f x51, map_ltlc f x52)
  | map_ltlc f (Or_ltlc (x61, x62)) = Or_ltlc (map_ltlc f x61, map_ltlc f x62)
  | map_ltlc f (Implies_ltlc (x71, x72)) =
    Implies_ltlc (map_ltlc f x71, map_ltlc f x72)
  | map_ltlc f (Next_ltlc x8) = Next_ltlc (map_ltlc f x8)
  | map_ltlc f (Final_ltlc x9) = Final_ltlc (map_ltlc f x9)
  | map_ltlc f (Global_ltlc x10) = Global_ltlc (map_ltlc f x10)
  | map_ltlc f (Until_ltlc (x111, x112)) =
    Until_ltlc (map_ltlc f x111, map_ltlc f x112)
  | map_ltlc f (Release_ltlc (x121, x122)) =
    Release_ltlc (map_ltlc f x121, map_ltlc f x122);

fun size_ltln True_ltln = Arith.suc Arith.zero_nat
  | size_ltln False_ltln = Arith.suc Arith.zero_nat
  | size_ltln (Prop_ltln x3) = Arith.suc Arith.zero_nat
  | size_ltln (Nprop_ltln x4) = Arith.suc Arith.zero_nat
  | size_ltln (And_ltln (x51, x52)) =
    Arith.plus_nat (Arith.plus_nat (size_ltln x51) (size_ltln x52))
      (Arith.suc Arith.zero_nat)
  | size_ltln (Or_ltln (x61, x62)) =
    Arith.plus_nat (Arith.plus_nat (size_ltln x61) (size_ltln x62))
      (Arith.suc Arith.zero_nat)
  | size_ltln (Next_ltln x7) =
    Arith.plus_nat (size_ltln x7) (Arith.suc Arith.zero_nat)
  | size_ltln (Until_ltln (x81, x82)) =
    Arith.plus_nat (Arith.plus_nat (size_ltln x81) (size_ltln x82))
      (Arith.suc Arith.zero_nat)
  | size_ltln (Release_ltln (x91, x92)) =
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
  (case x of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => y
    | LTL.Prop_ltln _ =>
      (case y of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => x
        | LTL.Prop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Or_ltln (x, y))
    | LTL.Nprop_ltln _ =>
      (case y of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => x
        | LTL.Prop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Or_ltln (x, y))
    | LTL.And_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => x
        | LTL.Prop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Or_ltln (x, y))
    | LTL.Or_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => x
        | LTL.Prop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Or_ltln (x, y))
    | LTL.Next_ltln _ =>
      (case y of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => x
        | LTL.Prop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Or_ltln (x, y))
    | LTL.Until_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => x
        | LTL.Prop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Or_ltln (x, y))
    | LTL.Release_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => x
        | LTL.Prop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Or_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Or_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Or_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Or_ltln (x, y)));

fun eq_i_i A_ xa xb =
  Predicate.bind (Predicate.single (xa, xb))
    (fn (x, xaa) =>
      (if HOL.eq A_ x xaa then Predicate.single () else Predicate.bot_pred));

fun mk_and x y =
  (case x of LTL.True_ltln => y | LTL.False_ltln => LTL.False_ltln
    | LTL.Prop_ltln _ =>
      (case y of LTL.True_ltln => x | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.And_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.And_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Next_ltln _ => LTL.And_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.And_ltln (x, y))
    | LTL.Nprop_ltln _ =>
      (case y of LTL.True_ltln => x | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.And_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.And_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Next_ltln _ => LTL.And_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.And_ltln (x, y))
    | LTL.And_ltln (_, _) =>
      (case y of LTL.True_ltln => x | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.And_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.And_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Next_ltln _ => LTL.And_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.And_ltln (x, y))
    | LTL.Or_ltln (_, _) =>
      (case y of LTL.True_ltln => x | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.And_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.And_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Next_ltln _ => LTL.And_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.And_ltln (x, y))
    | LTL.Next_ltln _ =>
      (case y of LTL.True_ltln => x | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.And_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.And_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Next_ltln _ => LTL.And_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.And_ltln (x, y))
    | LTL.Until_ltln (_, _) =>
      (case y of LTL.True_ltln => x | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.And_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.And_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Next_ltln _ => LTL.And_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.And_ltln (x, y))
    | LTL.Release_ltln (_, _) =>
      (case y of LTL.True_ltln => x | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.And_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.And_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Next_ltln _ => LTL.And_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.And_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.And_ltln (x, y)));

fun mk_next_pow n x =
  (case x of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => LTL.False_ltln
    | LTL.Prop_ltln _ => Arith.funpow n LTL.Next_ltln x
    | LTL.Nprop_ltln _ => Arith.funpow n LTL.Next_ltln x
    | LTL.And_ltln (_, _) => Arith.funpow n LTL.Next_ltln x
    | LTL.Or_ltln (_, _) => Arith.funpow n LTL.Next_ltln x
    | LTL.Next_ltln _ => Arith.funpow n LTL.Next_ltln x
    | LTL.Until_ltln (_, _) => Arith.funpow n LTL.Next_ltln x
    | LTL.Release_ltln (_, _) => Arith.funpow n LTL.Next_ltln x);

fun is_constant LTL.True_ltln = true
  | is_constant LTL.False_ltln = true
  | is_constant (LTL.Prop_ltln v) = false
  | is_constant (LTL.Nprop_ltln v) = false
  | is_constant (LTL.And_ltln (v, va)) = false
  | is_constant (LTL.Or_ltln (v, va)) = false
  | is_constant (LTL.Next_ltln v) = false
  | is_constant (LTL.Until_ltln (v, va)) = false
  | is_constant (LTL.Release_ltln (v, va)) = false;

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
  (case x of LTL.True_ltln => LTL.True_ltln | LTL.False_ltln => LTL.False_ltln
    | LTL.Prop_ltln _ => LTL.Next_ltln x | LTL.Nprop_ltln _ => LTL.Next_ltln x
    | LTL.And_ltln (_, _) => LTL.Next_ltln x
    | LTL.Or_ltln (_, _) => LTL.Next_ltln x | LTL.Next_ltln _ => LTL.Next_ltln x
    | LTL.Until_ltln (_, _) => LTL.Next_ltln x
    | LTL.Release_ltln (_, _) => LTL.Next_ltln x);

fun remove_until (LTL.Until_ltln (x, y)) = remove_until y
  | remove_until (LTL.Or_ltln (x, y)) =
    LTL.Or_ltln (remove_until x, remove_until y)
  | remove_until LTL.True_ltln = LTL.True_ltln
  | remove_until LTL.False_ltln = LTL.False_ltln
  | remove_until (LTL.Prop_ltln v) = LTL.Prop_ltln v
  | remove_until (LTL.Nprop_ltln v) = LTL.Nprop_ltln v
  | remove_until (LTL.And_ltln (v, va)) = LTL.And_ltln (v, va)
  | remove_until (LTL.Next_ltln v) = LTL.Next_ltln v
  | remove_until (LTL.Release_ltln (v, va)) = LTL.Release_ltln (v, va);

fun mk_until x y =
  (case x
    of LTL.True_ltln =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Until_ltln (LTL.True_ltln, remove_until y)
        | LTL.Nprop_ltln _ => LTL.Until_ltln (LTL.True_ltln, remove_until y)
        | LTL.And_ltln (_, _) => LTL.Until_ltln (LTL.True_ltln, remove_until y)
        | LTL.Or_ltln (_, _) => LTL.Until_ltln (LTL.True_ltln, remove_until y)
        | LTL.Next_ltln _ => LTL.Until_ltln (LTL.True_ltln, remove_until y)
        | LTL.Until_ltln (_, _) =>
          LTL.Until_ltln (LTL.True_ltln, remove_until y)
        | LTL.Release_ltln (_, _) =>
          LTL.Until_ltln (LTL.True_ltln, remove_until y))
    | LTL.False_ltln => y
    | LTL.Prop_ltln _ =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Until_ltln (x, y))
    | LTL.Nprop_ltln _ =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Until_ltln (x, y))
    | LTL.And_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Until_ltln (x, y))
    | LTL.Or_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Until_ltln (x, y))
    | LTL.Next_ltln _ =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Until_ltln (x, y))
    | LTL.Until_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Until_ltln (x, y))
    | LTL.Release_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Until_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Until_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Until_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Until_ltln (x, y)));

fun remove_release (LTL.Release_ltln (x, y)) = remove_release y
  | remove_release (LTL.And_ltln (x, y)) =
    LTL.And_ltln (remove_release x, remove_release y)
  | remove_release LTL.True_ltln = LTL.True_ltln
  | remove_release LTL.False_ltln = LTL.False_ltln
  | remove_release (LTL.Prop_ltln v) = LTL.Prop_ltln v
  | remove_release (LTL.Nprop_ltln v) = LTL.Nprop_ltln v
  | remove_release (LTL.Or_ltln (v, va)) = LTL.Or_ltln (v, va)
  | remove_release (LTL.Next_ltln v) = LTL.Next_ltln v
  | remove_release (LTL.Until_ltln (v, va)) = LTL.Until_ltln (v, va);

fun mk_release x y =
  (case x of LTL.True_ltln => y
    | LTL.False_ltln =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Release_ltln (LTL.False_ltln, remove_release y)
        | LTL.Nprop_ltln _ =>
          LTL.Release_ltln (LTL.False_ltln, remove_release y)
        | LTL.And_ltln (_, _) =>
          LTL.Release_ltln (LTL.False_ltln, remove_release y)
        | LTL.Or_ltln (_, _) =>
          LTL.Release_ltln (LTL.False_ltln, remove_release y)
        | LTL.Next_ltln _ => LTL.Release_ltln (LTL.False_ltln, remove_release y)
        | LTL.Until_ltln (_, _) =>
          LTL.Release_ltln (LTL.False_ltln, remove_release y)
        | LTL.Release_ltln (_, _) =>
          LTL.Release_ltln (LTL.False_ltln, remove_release y))
    | LTL.Prop_ltln _ =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Release_ltln (x, y))
    | LTL.Nprop_ltln _ =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Release_ltln (x, y))
    | LTL.And_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Release_ltln (x, y))
    | LTL.Or_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Release_ltln (x, y))
    | LTL.Next_ltln _ =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Release_ltln (x, y))
    | LTL.Until_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Release_ltln (x, y))
    | LTL.Release_ltln (_, _) =>
      (case y of LTL.True_ltln => LTL.True_ltln
        | LTL.False_ltln => LTL.False_ltln
        | LTL.Prop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Nprop_ltln _ => LTL.Release_ltln (x, y)
        | LTL.And_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Or_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Next_ltln _ => LTL.Release_ltln (x, y)
        | LTL.Until_ltln (_, _) => LTL.Release_ltln (x, y)
        | LTL.Release_ltln (_, _) => LTL.Release_ltln (x, y)));

fun rewrite_X_enat LTL.True_ltln = (LTL.True_ltln, Extended_Nat.Infinity_enat)
  | rewrite_X_enat LTL.False_ltln = (LTL.False_ltln, Extended_Nat.Infinity_enat)
  | rewrite_X_enat (LTL.Prop_ltln a) = (LTL.Prop_ltln a, Extended_Nat.zero_enat)
  | rewrite_X_enat (LTL.Nprop_ltln a) =
    (LTL.Nprop_ltln a, Extended_Nat.zero_enat)
  | rewrite_X_enat (LTL.And_ltln (phi, psi)) =
    combine mk_and (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (LTL.Or_ltln (phi, psi)) =
    combine mk_or (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (LTL.Until_ltln (phi, psi)) =
    combine mk_until (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (LTL.Release_ltln (phi, psi)) =
    combine mk_release (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (LTL.Next_ltln phi) = let
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

fun pure_universal A_ LTL.True_ltln = true
  | pure_universal A_ LTL.False_ltln = true
  | pure_universal A_ (LTL.And_ltln (nua, nu)) =
    pure_universal A_ nua andalso pure_universal A_ nu
  | pure_universal A_ (LTL.Or_ltln (nua, nu)) =
    pure_universal A_ nua andalso pure_universal A_ nu
  | pure_universal A_ (LTL.Until_ltln (nua, nu)) =
    pure_universal A_ nua andalso pure_universal A_ nu
  | pure_universal A_ (LTL.Release_ltln (nua, nu)) =
    LTL.equal_ltlna A_ nua LTL.False_ltln orelse pure_universal A_ nu
  | pure_universal A_ (LTL.Next_ltln nu) = pure_universal A_ nu
  | pure_universal A_ (LTL.Prop_ltln v) = false
  | pure_universal A_ (LTL.Nprop_ltln v) = false;

fun pure_eventual A_ LTL.True_ltln = true
  | pure_eventual A_ LTL.False_ltln = true
  | pure_eventual A_ (LTL.And_ltln (mua, mu)) =
    pure_eventual A_ mua andalso pure_eventual A_ mu
  | pure_eventual A_ (LTL.Or_ltln (mua, mu)) =
    pure_eventual A_ mua andalso pure_eventual A_ mu
  | pure_eventual A_ (LTL.Until_ltln (mua, mu)) =
    LTL.equal_ltlna A_ mua LTL.True_ltln orelse pure_eventual A_ mu
  | pure_eventual A_ (LTL.Release_ltln (mua, mu)) =
    pure_eventual A_ mua andalso pure_eventual A_ mu
  | pure_eventual A_ (LTL.Next_ltln mu) = pure_eventual A_ mu
  | pure_eventual A_ (LTL.Prop_ltln v) = false
  | pure_eventual A_ (LTL.Nprop_ltln v) = false;

fun suspendable A_ LTL.True_ltln = true
  | suspendable A_ LTL.False_ltln = true
  | suspendable A_ (LTL.And_ltln (xia, xi)) =
    suspendable A_ xia andalso suspendable A_ xi
  | suspendable A_ (LTL.Or_ltln (xia, xi)) =
    suspendable A_ xia andalso suspendable A_ xi
  | suspendable A_ (LTL.Until_ltln (phi, xi)) =
    LTL.equal_ltlna A_ phi LTL.True_ltln andalso pure_universal A_ xi orelse
      suspendable A_ xi
  | suspendable A_ (LTL.Release_ltln (phi, xi)) =
    LTL.equal_ltlna A_ phi LTL.False_ltln andalso pure_eventual A_ xi orelse
      suspendable A_ xi
  | suspendable A_ (LTL.Next_ltln xi) = suspendable A_ xi
  | suspendable A_ (LTL.Prop_ltln v) = false
  | suspendable A_ (LTL.Nprop_ltln v) = false;

fun rewrite_modal A_ LTL.True_ltln = LTL.True_ltln
  | rewrite_modal A_ LTL.False_ltln = LTL.False_ltln
  | rewrite_modal A_ (LTL.And_ltln (phi, psi)) =
    LTL.And_ltln (rewrite_modal A_ phi, rewrite_modal A_ psi)
  | rewrite_modal A_ (LTL.Or_ltln (phi, psi)) =
    LTL.Or_ltln (rewrite_modal A_ phi, rewrite_modal A_ psi)
  | rewrite_modal A_ (LTL.Until_ltln (phi, psi)) =
    (if pure_eventual A_ psi orelse suspendable A_ psi then rewrite_modal A_ psi
      else LTL.Until_ltln (rewrite_modal A_ phi, rewrite_modal A_ psi))
  | rewrite_modal A_ (LTL.Release_ltln (phi, psi)) =
    (if pure_universal A_ psi orelse suspendable A_ psi
      then rewrite_modal A_ psi
      else LTL.Release_ltln (rewrite_modal A_ phi, rewrite_modal A_ psi))
  | rewrite_modal A_ (LTL.Next_ltln phi) =
    (if suspendable A_ phi then rewrite_modal A_ phi
      else LTL.Next_ltln (rewrite_modal A_ phi))
  | rewrite_modal A_ (LTL.Prop_ltln v) = LTL.Prop_ltln v
  | rewrite_modal A_ (LTL.Nprop_ltln v) = LTL.Nprop_ltln v;

fun syntactical_implies_i_i A_ x xa =
  Predicate.sup_pred
    (Predicate.bind (Predicate.single (x, xa))
      (fn a =>
        (case a of (_, LTL.True_ltln) => Predicate.single ()
          | (_, LTL.False_ltln) => Predicate.bot_pred
          | (_, LTL.Prop_ltln _) => Predicate.bot_pred
          | (_, LTL.Nprop_ltln _) => Predicate.bot_pred
          | (_, LTL.And_ltln (_, _)) => Predicate.bot_pred
          | (_, LTL.Or_ltln (_, _)) => Predicate.bot_pred
          | (_, LTL.Next_ltln _) => Predicate.bot_pred
          | (_, LTL.Until_ltln (_, _)) => Predicate.bot_pred
          | (_, LTL.Release_ltln (_, _)) => Predicate.bot_pred)))
    (Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fn a =>
          (case a of (LTL.True_ltln, _) => Predicate.bot_pred
            | (LTL.False_ltln, _) => Predicate.single ()
            | (LTL.Prop_ltln _, _) => Predicate.bot_pred
            | (LTL.Nprop_ltln _, _) => Predicate.bot_pred
            | (LTL.And_ltln (_, _), _) => Predicate.bot_pred
            | (LTL.Or_ltln (_, _), _) => Predicate.bot_pred
            | (LTL.Next_ltln _, _) => Predicate.bot_pred
            | (LTL.Until_ltln (_, _), _) => Predicate.bot_pred
            | (LTL.Release_ltln (_, _), _) => Predicate.bot_pred)))
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
              (case a of (LTL.True_ltln, _) => Predicate.bot_pred
                | (LTL.False_ltln, _) => Predicate.bot_pred
                | (LTL.Prop_ltln _, _) => Predicate.bot_pred
                | (LTL.Nprop_ltln _, _) => Predicate.bot_pred
                | (LTL.And_ltln (phi, _), chi) =>
                  Predicate.bind (syntactical_implies_i_i A_ phi chi)
                    (fn () => Predicate.single ())
                | (LTL.Or_ltln (_, _), _) => Predicate.bot_pred
                | (LTL.Next_ltln _, _) => Predicate.bot_pred
                | (LTL.Until_ltln (_, _), _) => Predicate.bot_pred
                | (LTL.Release_ltln (_, _), _) => Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, xa))
              (fn a =>
                (case a of (LTL.True_ltln, _) => Predicate.bot_pred
                  | (LTL.False_ltln, _) => Predicate.bot_pred
                  | (LTL.Prop_ltln _, _) => Predicate.bot_pred
                  | (LTL.Nprop_ltln _, _) => Predicate.bot_pred
                  | (LTL.And_ltln (_, psi), chi) =>
                    Predicate.bind (syntactical_implies_i_i A_ psi chi)
                      (fn () => Predicate.single ())
                  | (LTL.Or_ltln (_, _), _) => Predicate.bot_pred
                  | (LTL.Next_ltln _, _) => Predicate.bot_pred
                  | (LTL.Until_ltln (_, _), _) => Predicate.bot_pred
                  | (LTL.Release_ltln (_, _), _) => Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, xa))
                (fn a =>
                  (case a of (_, LTL.True_ltln) => Predicate.bot_pred
                    | (_, LTL.False_ltln) => Predicate.bot_pred
                    | (_, LTL.Prop_ltln _) => Predicate.bot_pred
                    | (_, LTL.Nprop_ltln _) => Predicate.bot_pred
                    | (phi, LTL.And_ltln (psi, chi)) =>
                      Predicate.bind (syntactical_implies_i_i A_ phi psi)
                        (fn () =>
                          Predicate.bind (syntactical_implies_i_i A_ phi chi)
                            (fn () => Predicate.single ()))
                    | (_, LTL.Or_ltln (_, _)) => Predicate.bot_pred
                    | (_, LTL.Next_ltln _) => Predicate.bot_pred
                    | (_, LTL.Until_ltln (_, _)) => Predicate.bot_pred
                    | (_, LTL.Release_ltln (_, _)) => Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, xa))
                  (fn a =>
                    (case a of (_, LTL.True_ltln) => Predicate.bot_pred
                      | (_, LTL.False_ltln) => Predicate.bot_pred
                      | (_, LTL.Prop_ltln _) => Predicate.bot_pred
                      | (_, LTL.Nprop_ltln _) => Predicate.bot_pred
                      | (_, LTL.And_ltln (_, _)) => Predicate.bot_pred
                      | (phi, LTL.Or_ltln (psi, _)) =>
                        Predicate.bind (syntactical_implies_i_i A_ phi psi)
                          (fn () => Predicate.single ())
                      | (_, LTL.Next_ltln _) => Predicate.bot_pred
                      | (_, LTL.Until_ltln (_, _)) => Predicate.bot_pred
                      | (_, LTL.Release_ltln (_, _)) => Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single (x, xa))
                    (fn a =>
                      (case a of (_, LTL.True_ltln) => Predicate.bot_pred
                        | (_, LTL.False_ltln) => Predicate.bot_pred
                        | (_, LTL.Prop_ltln _) => Predicate.bot_pred
                        | (_, LTL.Nprop_ltln _) => Predicate.bot_pred
                        | (_, LTL.And_ltln (_, _)) => Predicate.bot_pred
                        | (phi, LTL.Or_ltln (_, chi)) =>
                          Predicate.bind (syntactical_implies_i_i A_ phi chi)
                            (fn () => Predicate.single ())
                        | (_, LTL.Next_ltln _) => Predicate.bot_pred
                        | (_, LTL.Until_ltln (_, _)) => Predicate.bot_pred
                        | (_, LTL.Release_ltln (_, _)) => Predicate.bot_pred)))
                  (Predicate.sup_pred
                    (Predicate.bind (Predicate.single (x, xa))
                      (fn a =>
                        (case a of (LTL.True_ltln, _) => Predicate.bot_pred
                          | (LTL.False_ltln, _) => Predicate.bot_pred
                          | (LTL.Prop_ltln _, _) => Predicate.bot_pred
                          | (LTL.Nprop_ltln _, _) => Predicate.bot_pred
                          | (LTL.And_ltln (_, _), _) => Predicate.bot_pred
                          | (LTL.Or_ltln (phi, psi), chi) =>
                            Predicate.bind (syntactical_implies_i_i A_ phi chi)
                              (fn () =>
                                Predicate.bind
                                  (syntactical_implies_i_i A_ psi chi)
                                  (fn () => Predicate.single ()))
                          | (LTL.Next_ltln _, _) => Predicate.bot_pred
                          | (LTL.Until_ltln (_, _), _) => Predicate.bot_pred
                          | (LTL.Release_ltln (_, _), _) =>
                            Predicate.bot_pred)))
                    (Predicate.sup_pred
                      (Predicate.bind (Predicate.single (x, xa))
                        (fn a =>
                          (case a of (_, LTL.True_ltln) => Predicate.bot_pred
                            | (_, LTL.False_ltln) => Predicate.bot_pred
                            | (_, LTL.Prop_ltln _) => Predicate.bot_pred
                            | (_, LTL.Nprop_ltln _) => Predicate.bot_pred
                            | (_, LTL.And_ltln (_, _)) => Predicate.bot_pred
                            | (_, LTL.Or_ltln (_, _)) => Predicate.bot_pred
                            | (_, LTL.Next_ltln _) => Predicate.bot_pred
                            | (phi, LTL.Until_ltln (_, chi)) =>
                              Predicate.bind
                                (syntactical_implies_i_i A_ phi chi)
                                (fn () => Predicate.single ())
                            | (_, LTL.Release_ltln (_, _)) =>
                              Predicate.bot_pred)))
                      (Predicate.sup_pred
                        (Predicate.bind (Predicate.single (x, xa))
                          (fn a =>
                            (case a of (LTL.True_ltln, _) => Predicate.bot_pred
                              | (LTL.False_ltln, _) => Predicate.bot_pred
                              | (LTL.Prop_ltln _, _) => Predicate.bot_pred
                              | (LTL.Nprop_ltln _, _) => Predicate.bot_pred
                              | (LTL.And_ltln (_, _), _) => Predicate.bot_pred
                              | (LTL.Or_ltln (_, _), _) => Predicate.bot_pred
                              | (LTL.Next_ltln _, _) => Predicate.bot_pred
                              | (LTL.Until_ltln (phi, psi), chi) =>
                                Predicate.bind
                                  (syntactical_implies_i_i A_ phi chi)
                                  (fn () =>
                                    Predicate.bind
                                      (syntactical_implies_i_i A_ psi chi)
                                      (fn () => Predicate.single ()))
                              | (LTL.Release_ltln (_, _), _) =>
                                Predicate.bot_pred)))
                        (Predicate.sup_pred
                          (Predicate.bind (Predicate.single (x, xa))
                            (fn a =>
                              (case a
                                of (LTL.True_ltln, _) => Predicate.bot_pred
                                | (LTL.False_ltln, _) => Predicate.bot_pred
                                | (LTL.Prop_ltln _, _) => Predicate.bot_pred
                                | (LTL.Nprop_ltln _, _) => Predicate.bot_pred
                                | (LTL.And_ltln (_, _), _) => Predicate.bot_pred
                                | (LTL.Or_ltln (_, _), _) => Predicate.bot_pred
                                | (LTL.Next_ltln _, _) => Predicate.bot_pred
                                | (LTL.Until_ltln (_, _), LTL.True_ltln) =>
                                  Predicate.bot_pred
                                | (LTL.Until_ltln (_, _), LTL.False_ltln) =>
                                  Predicate.bot_pred
                                | (LTL.Until_ltln (_, _), LTL.Prop_ltln _) =>
                                  Predicate.bot_pred
                                | (LTL.Until_ltln (_, _), LTL.Nprop_ltln _) =>
                                  Predicate.bot_pred
                                | (LTL.Until_ltln (_, _), LTL.And_ltln (_, _))
                                  => Predicate.bot_pred
                                | (LTL.Until_ltln (_, _), LTL.Or_ltln (_, _)) =>
                                  Predicate.bot_pred
                                | (LTL.Until_ltln (_, _), LTL.Next_ltln _) =>
                                  Predicate.bot_pred
                                | (LTL.Until_ltln (phi, psi),
                                    LTL.Until_ltln (chi, nu))
                                  => Predicate.bind
                                       (syntactical_implies_i_i A_ phi chi)
                                       (fn () =>
 Predicate.bind (syntactical_implies_i_i A_ psi nu)
   (fn () => Predicate.single ()))
                                | (LTL.Until_ltln (_, _),
                                    LTL.Release_ltln (_, _))
                                  => Predicate.bot_pred
                                | (LTL.Release_ltln (_, _), _) =>
                                  Predicate.bot_pred)))
                          (Predicate.sup_pred
                            (Predicate.bind (Predicate.single (x, xa))
                              (fn a =>
                                (case a
                                  of (LTL.True_ltln, _) => Predicate.bot_pred
                                  | (LTL.False_ltln, _) => Predicate.bot_pred
                                  | (LTL.Prop_ltln _, _) => Predicate.bot_pred
                                  | (LTL.Nprop_ltln _, _) => Predicate.bot_pred
                                  | (LTL.And_ltln (_, _), _) =>
                                    Predicate.bot_pred
                                  | (LTL.Or_ltln (_, _), _) =>
                                    Predicate.bot_pred
                                  | (LTL.Next_ltln _, _) => Predicate.bot_pred
                                  | (LTL.Until_ltln (_, _), _) =>
                                    Predicate.bot_pred
                                  | (LTL.Release_ltln (_, chi), phi) =>
                                    Predicate.bind
                                      (syntactical_implies_i_i A_ chi phi)
                                      (fn () => Predicate.single ()))))
                            (Predicate.sup_pred
                              (Predicate.bind (Predicate.single (x, xa))
                                (fn a =>
                                  (case a
                                    of (_, LTL.True_ltln) => Predicate.bot_pred
                                    | (_, LTL.False_ltln) => Predicate.bot_pred
                                    | (_, LTL.Prop_ltln _) => Predicate.bot_pred
                                    | (_, LTL.Nprop_ltln _) =>
                                      Predicate.bot_pred
                                    | (_, LTL.And_ltln (_, _)) =>
                                      Predicate.bot_pred
                                    | (_, LTL.Or_ltln (_, _)) =>
                                      Predicate.bot_pred
                                    | (_, LTL.Next_ltln _) => Predicate.bot_pred
                                    | (_, LTL.Until_ltln (_, _)) =>
                                      Predicate.bot_pred
                                    | (chi, LTL.Release_ltln (phi, psi)) =>
                                      Predicate.bind
(syntactical_implies_i_i A_ chi phi)
(fn () =>
  Predicate.bind (syntactical_implies_i_i A_ chi psi)
    (fn () => Predicate.single ())))))
                              (Predicate.sup_pred
                                (Predicate.bind (Predicate.single (x, xa))
                                  (fn a =>
                                    (case a
                                      of (LTL.True_ltln, _) =>
Predicate.bot_pred
                                      | (LTL.False_ltln, _) =>
Predicate.bot_pred
                                      | (LTL.Prop_ltln _, _) =>
Predicate.bot_pred
                                      | (LTL.Nprop_ltln _, _) =>
Predicate.bot_pred
                                      | (LTL.And_ltln (_, _), _) =>
Predicate.bot_pred
                                      | (LTL.Or_ltln (_, _), _) =>
Predicate.bot_pred
                                      | (LTL.Next_ltln _, _) =>
Predicate.bot_pred
                                      | (LTL.Until_ltln (_, _), _) =>
Predicate.bot_pred
                                      | (LTL.Release_ltln (_, _), LTL.True_ltln)
=> Predicate.bot_pred
                                      |
(LTL.Release_ltln (_, _), LTL.False_ltln) => Predicate.bot_pred
                                      |
(LTL.Release_ltln (_, _), LTL.Prop_ltln _) => Predicate.bot_pred
                                      |
(LTL.Release_ltln (_, _), LTL.Nprop_ltln _) => Predicate.bot_pred
                                      |
(LTL.Release_ltln (_, _), LTL.And_ltln (_, _)) => Predicate.bot_pred
                                      |
(LTL.Release_ltln (_, _), LTL.Or_ltln (_, _)) => Predicate.bot_pred
                                      |
(LTL.Release_ltln (_, _), LTL.Next_ltln _) => Predicate.bot_pred
                                      |
(LTL.Release_ltln (_, _), LTL.Until_ltln (_, _)) => Predicate.bot_pred
                                      |
(LTL.Release_ltln (phi, psi), LTL.Release_ltln (chi, nu)) =>
Predicate.bind (syntactical_implies_i_i A_ phi chi)
  (fn () =>
    Predicate.bind (syntactical_implies_i_i A_ psi nu)
      (fn () => Predicate.single ())))))
                                (Predicate.sup_pred
                                  (Predicate.bind (Predicate.single (x, xa))
                                    (fn a =>
                                      (case a
of (LTL.True_ltln, _) => Predicate.bot_pred
| (LTL.False_ltln, _) => Predicate.bot_pred
| (LTL.Prop_ltln _, _) => Predicate.bot_pred
| (LTL.Nprop_ltln _, _) => Predicate.bot_pred
| (LTL.And_ltln (_, _), _) => Predicate.bot_pred
| (LTL.Or_ltln (_, _), _) => Predicate.bot_pred
| (LTL.Next_ltln _, _) => Predicate.bot_pred
| (LTL.Until_ltln (_, _), _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.True_ltln, _), _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.False_ltln, _), LTL.True_ltln) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.False_ltln, _), LTL.False_ltln) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.False_ltln, _), LTL.Prop_ltln _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.False_ltln, _), LTL.Nprop_ltln _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.False_ltln, _), LTL.And_ltln (_, _)) =>
  Predicate.bot_pred
| (LTL.Release_ltln (LTL.False_ltln, _), LTL.Or_ltln (_, _)) =>
  Predicate.bot_pred
| (LTL.Release_ltln (LTL.False_ltln, phi), LTL.Next_ltln psi) =>
  Predicate.bind
    (syntactical_implies_i_i A_ (LTL.Release_ltln (LTL.False_ltln, phi)) psi)
    (fn () => Predicate.single ())
| (LTL.Release_ltln (LTL.False_ltln, _), LTL.Until_ltln (_, _)) =>
  Predicate.bot_pred
| (LTL.Release_ltln (LTL.False_ltln, _), LTL.Release_ltln (_, _)) =>
  Predicate.bot_pred
| (LTL.Release_ltln (LTL.Prop_ltln _, _), _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.Nprop_ltln _, _), _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.And_ltln (_, _), _), _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.Or_ltln (_, _), _), _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.Next_ltln _, _), _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.Until_ltln (_, _), _), _) => Predicate.bot_pred
| (LTL.Release_ltln (LTL.Release_ltln (_, _), _), _) => Predicate.bot_pred)))
                                  (Predicate.sup_pred
                                    (Predicate.bind (Predicate.single (x, xa))
                                      (fn a =>
(case a of (LTL.True_ltln, _) => Predicate.bot_pred
  | (LTL.False_ltln, _) => Predicate.bot_pred
  | (LTL.Prop_ltln _, _) => Predicate.bot_pred
  | (LTL.Nprop_ltln _, _) => Predicate.bot_pred
  | (LTL.And_ltln (_, _), _) => Predicate.bot_pred
  | (LTL.Or_ltln (_, _), _) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.True_ltln) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.False_ltln) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Prop_ltln _) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Nprop_ltln _) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.And_ltln (_, _)) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Or_ltln (_, _)) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Next_ltln _) => Predicate.bot_pred
  | (LTL.Next_ltln phi, LTL.Until_ltln (LTL.True_ltln, psi)) =>
    Predicate.bind
      (syntactical_implies_i_i A_ phi (LTL.Until_ltln (LTL.True_ltln, psi)))
      (fn () => Predicate.single ())
  | (LTL.Next_ltln _, LTL.Until_ltln (LTL.False_ltln, _)) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Until_ltln (LTL.Prop_ltln _, _)) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Until_ltln (LTL.Nprop_ltln _, _)) =>
    Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Until_ltln (LTL.And_ltln (_, _), _)) =>
    Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Until_ltln (LTL.Or_ltln (_, _), _)) =>
    Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Until_ltln (LTL.Next_ltln _, _)) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Until_ltln (LTL.Until_ltln (_, _), _)) =>
    Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Until_ltln (LTL.Release_ltln (_, _), _)) =>
    Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Release_ltln (_, _)) => Predicate.bot_pred
  | (LTL.Until_ltln (_, _), _) => Predicate.bot_pred
  | (LTL.Release_ltln (_, _), _) => Predicate.bot_pred)))
                                    (Predicate.bind (Predicate.single (x, xa))
                                      (fn a =>
(case a of (LTL.True_ltln, _) => Predicate.bot_pred
  | (LTL.False_ltln, _) => Predicate.bot_pred
  | (LTL.Prop_ltln _, _) => Predicate.bot_pred
  | (LTL.Nprop_ltln _, _) => Predicate.bot_pred
  | (LTL.And_ltln (_, _), _) => Predicate.bot_pred
  | (LTL.Or_ltln (_, _), _) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.True_ltln) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.False_ltln) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Prop_ltln _) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Nprop_ltln _) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.And_ltln (_, _)) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Or_ltln (_, _)) => Predicate.bot_pred
  | (LTL.Next_ltln phi, LTL.Next_ltln psi) =>
    Predicate.bind (syntactical_implies_i_i A_ phi psi)
      (fn () => Predicate.single ())
  | (LTL.Next_ltln _, LTL.Until_ltln (_, _)) => Predicate.bot_pred
  | (LTL.Next_ltln _, LTL.Release_ltln (_, _)) => Predicate.bot_pred
  | (LTL.Until_ltln (_, _), _) => Predicate.bot_pred
  | (LTL.Release_ltln (_, _), _) => Predicate.bot_pred)))))))))))))))))));

fun syntactical_implies A_ x1 x2 =
  Predicate.holds (syntactical_implies_i_i A_ x1 x2);

fun rewrite_syn_imp A_ (LTL.And_ltln (phi, psi)) =
  (if syntactical_implies A_ phi psi then rewrite_syn_imp A_ phi
    else (if syntactical_implies A_ psi phi then rewrite_syn_imp A_ psi
           else (if syntactical_implies A_ phi (LTL.not_n psi) orelse
                      syntactical_implies A_ psi (LTL.not_n phi)
                  then LTL.False_ltln
                  else mk_and (rewrite_syn_imp A_ phi)
                         (rewrite_syn_imp A_ psi))))
  | rewrite_syn_imp A_ (LTL.Or_ltln (phi, psi)) =
    (if syntactical_implies A_ phi psi then rewrite_syn_imp A_ psi
      else (if syntactical_implies A_ psi phi then rewrite_syn_imp A_ phi
             else (if syntactical_implies A_ (LTL.not_n phi) psi orelse
                        syntactical_implies A_ (LTL.not_n psi) phi
                    then LTL.True_ltln
                    else mk_or (rewrite_syn_imp A_ phi)
                           (rewrite_syn_imp A_ psi))))
  | rewrite_syn_imp A_ (LTL.Until_ltln (phi, psi)) =
    (if syntactical_implies A_ phi psi then rewrite_syn_imp A_ psi
      else (if syntactical_implies A_ (LTL.not_n phi) psi
             then mk_until LTL.True_ltln (rewrite_syn_imp A_ psi)
             else mk_until (rewrite_syn_imp A_ phi) (rewrite_syn_imp A_ psi)))
  | rewrite_syn_imp A_ (LTL.Release_ltln (phi, psi)) =
    (if syntactical_implies A_ psi phi then rewrite_syn_imp A_ psi
      else (if syntactical_implies A_ psi (LTL.not_n phi)
             then mk_release LTL.False_ltln (rewrite_syn_imp A_ psi)
             else mk_release (rewrite_syn_imp A_ phi) (rewrite_syn_imp A_ psi)))
  | rewrite_syn_imp A_ (LTL.Next_ltln phi) = mk_next (rewrite_syn_imp A_ phi)
  | rewrite_syn_imp A_ LTL.True_ltln = LTL.True_ltln
  | rewrite_syn_imp A_ LTL.False_ltln = LTL.False_ltln
  | rewrite_syn_imp A_ (LTL.Prop_ltln v) = LTL.Prop_ltln v
  | rewrite_syn_imp A_ (LTL.Nprop_ltln v) = LTL.Nprop_ltln v;

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
