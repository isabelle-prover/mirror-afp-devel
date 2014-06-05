
structure Uint : sig
  val set_bit : Word.word -> IntInf.int -> bool -> Word.word
  val shiftl : Word.word -> IntInf.int -> Word.word
  val shiftr : Word.word -> IntInf.int -> Word.word
  val shiftr_signed : Word.word -> IntInf.int -> Word.word
  val test_bit : Word.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word.orb (x, mask)
     else Word.andb (x, Word.notb mask)
  end

fun shiftl x n =
  Word.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word.andb (x, Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word.fromInt 0

end; (* struct Uint *)

(* Test that words can handle numbers between 0 and 3 *)
val _ = if 3 <= Word.wordSize then () else raise (Fail ("wordSize less than 3"));

structure Uint8 : sig
  val set_bit : Word8.word -> IntInf.int -> bool -> Word8.word
  val shiftl : Word8.word -> IntInf.int -> Word8.word
  val shiftr : Word8.word -> IntInf.int -> Word8.word
  val shiftr_signed : Word8.word -> IntInf.int -> Word8.word
  val test_bit : Word8.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word8.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word8.orb (x, mask)
     else Word8.andb (x, Word8.notb mask)
  end

fun shiftl x n =
  Word8.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word8.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word8.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word8.andb (x, Word8.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word8.fromInt 0

end; (* struct Uint8 *)

(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of 
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x) 
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then 
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

end;

end;

structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;

  fun grow (aref, inc, x) = case aref of 
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x) 
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then 
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
    );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:int) = 
  sub (a,i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:int) (e:'a) = 
  update (a, i, e) handle Subscript => d ()

end;
end;





  structure Statistics : sig
    type stat_entry = string * (unit -> bool) * (unit -> string)
  
    val register_stat : stat_entry -> unit
    val get_active_stats : unit -> (string * string) list
    val pretty_stats : (string * string) list -> string

  end = struct
    type stat_entry = string * (unit -> bool) * (unit -> string)
    val stats : stat_entry list Unsynchronized.ref = Unsynchronized.ref []
  
    fun register_stat e = stats := e :: !stats

    fun get_active_stats () = let
      fun flt [] = []
        | flt ((n,a,s)::l) = if a () then (n,s ()) :: flt l else flt l

    in flt (!stats)
    end

    fun pretty_stats [] = ""
      | pretty_stats ((n,s)::l) = "=== " ^ n ^ " ===\n" ^ s ^ "\n" ^ pretty_stats l
  end

(* Argh! Functors not compatible with ML_val command!
  functor Timer () : sig 
    val reset : unit -> unit
    val start : unit -> unit
    val stop : unit -> unit
    val set : Time.time -> unit
    val get : unit -> Time.time
    val pretty : unit -> string
  end = struct

    open Time;

    val time : Time.time Unsynchronized.ref = Unsynchronized.ref Time.zeroTime
    val running : bool Unsynchronized.ref = Unsynchronized.ref false
    val start_time : Time.time Unsynchronized.ref = Unsynchronized.ref Time.zeroTime
        
    fun reset () = (
      time := Time.zeroTime;
      running := false;
      start_time := Time.zeroTime
    )

    fun start () = 
      if !running then 
        () 
      else (
        running := true;
        start_time := Time.now ()
      )

    fun this_runs_time () = 
      if !running then 
        Time.now () - !start_time 
      else 
        Time.zeroTime

    fun stop () = (
      time := !time + this_runs_time ();
      running := false
    )

    fun get () = !time + this_runs_time ()
    fun set t = time := t - this_runs_time ()
  
    fun pretty () = Time.toString (!time) ^ "s"
  end
  *)



structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromInt n))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromInt n)))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromInt n)
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromInt n)
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromInt n)) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)


    structure PromelaUtils = struct
      exception UnsupportedConstruct of string
      exception StaticError of string
      fun warn msg = TextIO.print ("Warning: " ^ msg ^ "\n")
      fun usc  c   = raise (UnsupportedConstruct c)
      fun err  e   = raise (StaticError e)
    end 


    structure PromelaStatistics = struct
      val active = Unsynchronized.ref false
      val parseTime = Unsynchronized.ref Time.zeroTime
      val time = Unsynchronized.ref Time.zeroTime

      fun is_active () = !active

      fun start () = (
            active := true; 
            if !parseTime = Time.zeroTime then () else parseTime := Time.- (Time.now (), !parseTime);
            time := Time.now ())
      fun start_parse () = (active := true; parseTime := Time.now())
      fun stop_timer () = (time := Time.- (Time.now (), !time))

      fun to_string () = let
        val t = Time.toMilliseconds (!time)
        val pt = Time.toMilliseconds (!parseTime)
      in
        (if pt = 0 then "" else 
        "Parsing time : " ^ IntInf.toString pt ^ "ms\n")
      ^ "Building time: " ^ IntInf.toString t ^ "ms\n"
      end
        
      val _ = Statistics.register_stat ("Promela",is_active,to_string)
    end


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

structure Map : sig
  val map_of : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
end = struct

fun map_of A_ ((l, v) :: ps) k =
  (if HOL.eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

end; (*struct Map*)

structure Orderings : sig
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val max : 'a ord -> 'a -> 'a -> 'a
  type 'a preorder
  val ord_preorder : 'a preorder -> 'a ord
  type 'a order
  val preorder_order : 'a order -> 'a preorder
  type 'a linorder
  val order_linorder : 'a linorder -> 'a order
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

end; (*struct Orderings*)

structure Product_Type : sig
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val apfst : ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val map_pair : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val equal_proda : 'a HOL.equal -> 'b HOL.equal -> 'a * 'b -> 'a * 'b -> bool
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> ('a * 'b) HOL.equal
  val equal_unita : unit -> unit -> bool
  val equal_unit : unit HOL.equal
  val equal_bool : bool -> bool -> bool
end = struct

fun fst (a, b) = a;

fun snd (a, b) = b;

fun apfst f (x, y) = (f x, y);

fun apsnd f (x, y) = (x, f y);

fun map_pair f g (a, b) = (f a, g b);

fun equal_proda A_ B_ (aa, ba) (a, b) = HOL.eq A_ aa a andalso HOL.eq B_ ba b;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) HOL.equal;

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit HOL.equal;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

end; (*struct Product_Type*)

structure Arith : sig
  datatype nat = Nat of IntInf.int
  datatype num = One | Bit0 of num | Bit1 of num
  val integer_of_nat : nat -> IntInf.int
  val plus_nata : nat -> nat -> nat
  val one_nata : nat
  val suc : nat -> nat
  type 'a one
  val one : 'a one -> 'a
  val one_nat : nat one
  type 'a plus
  val plus : 'a plus -> 'a -> 'a -> 'a
  val plus_nat : nat plus
  type 'a semigroup_add
  val plus_semigroup_add : 'a semigroup_add -> 'a plus
  type 'a numeral
  val one_numeral : 'a numeral -> 'a one
  val semigroup_add_numeral : 'a numeral -> 'a semigroup_add
  val numeral : 'a numeral -> num -> 'a
  type 'a times
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a power
  val one_power : 'a power -> 'a one
  val times_power : 'a power -> 'a times
  val ord_integer : IntInf.int Orderings.ord
  val minus_nat : nat -> nat -> nat
  val equal_nat : nat -> nat -> bool
  val zero_nat : nat
  val powera : 'a -> ('a -> 'a -> 'a) -> 'a -> nat -> 'a
  val power : 'a power -> 'a -> nat -> 'a
  val less_nat : nat -> nat -> bool
  val semigroup_add_nat : nat semigroup_add
  val numeral_nat : nat numeral
  val less_eq_nat : nat -> nat -> bool
  val one_integera : IntInf.int
  val one_integer : IntInf.int one
  val abs_integer : IntInf.int -> IntInf.int
  val sgn_integer : IntInf.int -> IntInf.int
  val divmod_integer : IntInf.int -> IntInf.int -> IntInf.int * IntInf.int
  val div_integer : IntInf.int -> IntInf.int -> IntInf.int
  val mod_integer : IntInf.int -> IntInf.int -> IntInf.int
  val plus_integer : IntInf.int plus
  val equal_integer : IntInf.int HOL.equal
  val preorder_integer : IntInf.int Orderings.preorder
  val order_integer : IntInf.int Orderings.order
  val times_integer : IntInf.int times
  val power_integer : IntInf.int power
  val nat_of_integer : IntInf.int -> nat
  val semigroup_add_integer : IntInf.int semigroup_add
  val numeral_integer : IntInf.int numeral
  val linorder_integer : IntInf.int Orderings.linorder
end = struct

datatype nat = Nat of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

fun integer_of_nat (Nat x) = x;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nata : nat = Nat (1 : IntInf.int);

fun suc n = plus_nata n one_nata;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

fun numeral A_ (Bit1 n) =
  let
    val m = numeral A_ n;
  in
    plus ((plus_semigroup_add o semigroup_add_numeral) A_)
      (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
      (one (one_numeral A_))
  end
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ One = one (one_numeral A_);

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int Orderings.ord;

fun minus_nat m n =
  Nat (Orderings.max ord_integer 0
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val zero_nat : nat = Nat 0;

fun powera one times a n =
  (if equal_nat n zero_nat then one
    else times a (powera one times a (minus_nat n one_nata)));

fun power A_ = powera (one (one_power A_)) (times (times_power A_));

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

fun abs_integer k = (if IntInf.< (k, 0) then IntInf.~ k else k);

fun sgn_integer k =
  (if ((k : IntInf.int) = 0) then 0
    else (if IntInf.< (k, 0) then IntInf.~ (1 : IntInf.int)
           else (1 : IntInf.int)));

fun divmod_integer k l =
  (if ((k : IntInf.int) = 0) then (0, 0)
    else (if ((l : IntInf.int) = 0) then (0, k)
           else (Product_Type.apsnd o (fn a => fn b => IntInf.* (a, b)) o
                  sgn_integer)
                  l (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                      then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                      else let
                             val (r, s) =
                               IntInf.divMod (IntInf.abs k, IntInf.abs l);
                           in
                             (if ((s : IntInf.int) = 0) then (IntInf.~ r, 0)
                               else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                      IntInf.- (abs_integer l, s)))
                           end)));

fun div_integer k l = Product_Type.fst (divmod_integer k l);

fun mod_integer k l = Product_Type.snd (divmod_integer k l);

val plus_integer = {plus = (fn a => fn b => IntInf.+ (a, b))} : IntInf.int plus;

val equal_integer = {equal = (fn a => fn b => ((a : IntInf.int) = b))} :
  IntInf.int HOL.equal;

val preorder_integer = {ord_preorder = ord_integer} :
  IntInf.int Orderings.preorder;

val order_integer = {preorder_order = preorder_integer} :
  IntInf.int Orderings.order;

val times_integer = {times = (fn a => fn b => IntInf.* (a, b))} :
  IntInf.int times;

val power_integer = {one_power = one_integer, times_power = times_integer} :
  IntInf.int power;

fun nat_of_integer k = Nat (Orderings.max ord_integer 0 k);

val semigroup_add_integer = {plus_semigroup_add = plus_integer} :
  IntInf.int semigroup_add;

val numeral_integer =
  {one_numeral = one_integer, semigroup_add_numeral = semigroup_add_integer} :
  IntInf.int numeral;

val linorder_integer = {order_linorder = order_integer} :
  IntInf.int Orderings.linorder;

end; (*struct Arith*)

structure List : sig
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val map : ('a -> 'b) -> 'a list -> 'b list
  val nth : 'a list -> Arith.nat -> 'a
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val upt : Arith.nat -> Arith.nat -> Arith.nat list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val find : ('a -> bool) -> 'a list -> 'a option
  val null : 'a list -> bool
  val last : 'a list -> 'a
  val maps : ('a -> 'b list) -> 'a list -> 'b list
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val concat : ('a list) list -> 'a list
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val insert : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val butlast : 'a list -> 'a list
  val enumerate : Arith.nat -> 'a list -> (Arith.nat * 'a) list
  val equal_lista : 'a HOL.equal -> 'a list -> 'a list -> bool
  val equal_list : 'a HOL.equal -> ('a list) HOL.equal
  val replicate : Arith.nat -> 'a -> 'a list
  val gen_length : Arith.nat -> 'a list -> Arith.nat
  val size_list : 'a list -> Arith.nat
  val insort_key :
    'b Orderings.linorder -> ('a -> 'b) -> 'a -> 'a list -> 'a list
  val list_update : 'a list -> Arith.nat -> 'a -> 'a list
end = struct

fun hd (x :: xs) = x;

fun tl [] = []
  | tl (x :: xs) = xs;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs;

fun nth (x :: xs) n =
  (if Arith.equal_nat n Arith.zero_nat then x
    else nth xs (Arith.minus_nat n Arith.one_nata));

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun upt i j = (if Arith.less_nat i j then i :: upt (Arith.suc i) j else []);

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun null [] = true
  | null (x :: xs) = false;

fun last (x :: xs) = (if null xs then x else last xs);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldr f [] = Fun.id
  | foldr f (x :: xs) = f x o foldr f xs;

fun concat xss = foldr (fn a => fn b => a @ b) xss [];

fun member A_ [] y = false
  | member A_ (x :: xs) y = HOL.eq A_ x y orelse member A_ xs y;

fun insert A_ x xs = (if member A_ xs x then xs else x :: xs);

fun butlast [] = []
  | butlast (x :: xs) = (if null xs then [] else x :: butlast xs);

fun enumerate n (x :: xs) = (n, x) :: enumerate (Arith.suc n) xs
  | enumerate n [] = [];

fun equal_lista A_ (a :: lista) [] = false
  | equal_lista A_ [] (a :: lista) = false
  | equal_lista A_ (aa :: listaa) (a :: lista) =
    HOL.eq A_ aa a andalso equal_lista A_ listaa lista
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) HOL.equal;

fun replicate n x =
  (if Arith.equal_nat n Arith.zero_nat then []
    else x :: replicate (Arith.minus_nat n Arith.one_nata) x);

fun gen_length n (x :: xs) = gen_length (Arith.suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length Arith.zero_nat x;

fun insort_key B_ f x [] = [x]
  | insort_key B_ f x (y :: ys) =
    (if Orderings.less_eq
          ((Orderings.ord_preorder o Orderings.preorder_order o
             Orderings.order_linorder)
            B_)
          (f x) (f y)
      then x :: y :: ys else y :: insort_key B_ f x ys);

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if Arith.equal_nat i Arith.zero_nat then y :: xs
      else x :: list_update xs (Arith.minus_nat i Arith.one_nata) y);

end; (*struct List*)

structure Dlist : sig
  datatype 'a dlist = Dlist of 'a list
  val empty : 'a dlist
  val list_of_dlist : 'a dlist -> 'a list
  val insert : 'a HOL.equal -> 'a -> 'a dlist -> 'a dlist
end = struct

datatype 'a dlist = Dlist of 'a list;

val empty : 'a dlist = Dlist [];

fun list_of_dlist (Dlist x) = x;

fun insert A_ x dxs = Dlist (List.insert A_ x (list_of_dlist dxs));

end; (*struct Dlist*)

structure Foldi : sig
  val foldli : 'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
end = struct

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

end; (*struct Foldi*)

structure IArray : sig
  val sub : 'a Vector.vector -> Arith.nat -> 'a
  val length : 'a Vector.vector -> Arith.nat
  val list_of : 'a Vector.vector -> 'a list
  val equal_iarray :
    'a HOL.equal -> 'a Vector.vector -> 'a Vector.vector -> bool
end = struct

fun sub asa n = Vector.sub (asa, Arith.integer_of_nat n);

fun length asa = Arith.nat_of_integer (Vector.length asa);

fun list_of asa = List.map (sub asa) (List.upt Arith.zero_nat (length asa));

fun equal_iarray A_ asa bs = List.equal_lista A_ (list_of asa) (list_of bs);

end; (*struct IArray*)

structure Option : sig
  val map : ('a -> 'b) -> 'a option -> 'b option
  val the : 'a option -> 'a
  val is_none : 'a option -> bool
end = struct

fun map f (SOME x) = SOME (f x)
  | map f NONE = NONE;

fun the (SOME x) = x;

fun is_none (SOME x) = false
  | is_none NONE = true;

end; (*struct Option*)

structure While_Combinator : sig
  val whilea : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a
end = struct

fun whilea b c s = (if b s then whilea b c (c s) else s);

end; (*struct While_Combinator*)

structure Refine_Det : sig
  datatype 'a dres = DSUCCEEDi | DFAILi | DRETURN of 'a
  val dbind : 'a dres -> ('a -> 'b dres) -> 'b dres
end = struct

datatype 'a dres = DSUCCEEDi | DFAILi | DRETURN of 'a;

fun dbind DFAILi f = DFAILi
  | dbind DSUCCEEDi f = DSUCCEEDi
  | dbind (DRETURN x) f = f x;

end; (*struct Refine_Det*)

structure Refine_Transfer : sig
  val the_res : 'a Refine_Det.dres -> 'a
end = struct

fun the_res (Refine_Det.DRETURN x) = x;

end; (*struct Refine_Transfer*)

structure List_lexord : sig
  val less_eq_list :
    'a HOL.equal * 'a Orderings.order -> 'a list -> 'a list -> bool
  val less_list :
    'a HOL.equal * 'a Orderings.order -> 'a list -> 'a list -> bool
  val ord_list : 'a HOL.equal * 'a Orderings.order -> ('a list) Orderings.ord
  val preorder_list :
    'a HOL.equal * 'a Orderings.order -> ('a list) Orderings.preorder
  val order_list :
    'a HOL.equal * 'a Orderings.order -> ('a list) Orderings.order
  val linorder_list :
    'a HOL.equal * 'a Orderings.linorder -> ('a list) Orderings.linorder
end = struct

fun less_eq_list (A1_, A2_) (x :: xs) (y :: ys) =
  Orderings.less ((Orderings.ord_preorder o Orderings.preorder_order) A2_) x
    y orelse
    HOL.eq A1_ x y andalso less_eq_list (A1_, A2_) xs ys
  | less_eq_list (A1_, A2_) [] xs = true
  | less_eq_list (A1_, A2_) (x :: xs) [] = false;

fun less_list (A1_, A2_) (x :: xs) (y :: ys) =
  Orderings.less ((Orderings.ord_preorder o Orderings.preorder_order) A2_) x
    y orelse
    HOL.eq A1_ x y andalso less_list (A1_, A2_) xs ys
  | less_list (A1_, A2_) [] (x :: xs) = true
  | less_list (A1_, A2_) xs [] = false;

fun ord_list (A1_, A2_) =
  {less_eq = less_eq_list (A1_, A2_), less = less_list (A1_, A2_)} :
  ('a list) Orderings.ord;

fun preorder_list (A1_, A2_) = {ord_preorder = ord_list (A1_, A2_)} :
  ('a list) Orderings.preorder;

fun order_list (A1_, A2_) = {preorder_order = preorder_list (A1_, A2_)} :
  ('a list) Orderings.order;

fun linorder_list (A1_, A2_) =
  {order_linorder = order_list (A1_, Orderings.order_linorder A2_)} :
  ('a list) Orderings.linorder;

end; (*struct List_lexord*)

structure Dlist_add : sig
  val dlist_iteratei :
    'a Dlist.dlist -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
end = struct

fun dlist_iteratei xs = Foldi.foldli (Dlist.list_of_dlist xs);

end; (*struct Dlist_add*)

structure ListSetImpl : sig
  val g_sng_ls_basic_ops : 'a HOL.equal -> 'a -> 'a Dlist.dlist
  val iteratei_bset_op_list_it_ls_basic_ops :
    'a Dlist.dlist -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val g_union_ls_basic_ops :
    'a HOL.equal -> 'a Dlist.dlist -> 'a Dlist.dlist -> 'a Dlist.dlist
  val g_isEmpty_ls_basic_ops : 'a Dlist.dlist -> bool
end = struct

fun g_sng_ls_basic_ops A_ x = Dlist.insert A_ x Dlist.empty;

fun iteratei_bset_op_list_it_ls_basic_ops s = Dlist_add.dlist_iteratei s;

fun g_union_ls_basic_ops A_ s1 s2 =
  iteratei_bset_op_list_it_ls_basic_ops s1 (fn _ => true) (Dlist.insert A_) s2;

fun g_isEmpty_ls_basic_ops s =
  iteratei_bset_op_list_it_ls_basic_ops s (fn c => c) (fn _ => fn _ => false)
    true;

end; (*struct ListSetImpl*)

structure Assoc_List : sig
  datatype ('a, 'b) assoc_list = Assoc_List of ('a * 'b) list
  val empty : ('a, 'b) assoc_list
  val impl_of : ('a, 'b) assoc_list -> ('a * 'b) list
  val lookup : 'a HOL.equal -> ('a, 'b) assoc_list -> 'a -> 'b option
  val update_with_aux :
    'b HOL.equal -> 'a -> 'b -> ('a -> 'a) -> ('b * 'a) list -> ('b * 'a) list
  val update_with :
    'a HOL.equal ->
      'b -> 'a -> ('b -> 'b) -> ('a, 'b) assoc_list -> ('a, 'b) assoc_list
  val update :
    'a HOL.equal -> 'a -> 'b -> ('a, 'b) assoc_list -> ('a, 'b) assoc_list
  val iteratei :
    ('a, 'b) assoc_list -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val equal_assoc_list :
    'a HOL.equal -> 'b HOL.equal ->
      ('a, 'b) assoc_list -> ('a, 'b) assoc_list -> bool
end = struct

datatype ('a, 'b) assoc_list = Assoc_List of ('a * 'b) list;

val empty : ('a, 'b) assoc_list = Assoc_List [];

fun impl_of (Assoc_List x) = x;

fun lookup A_ al = Map.map_of A_ (impl_of al);

fun update_with_aux B_ v k f [] = [(k, f v)]
  | update_with_aux B_ v k f (p :: ps) =
    (if HOL.eq B_ (Product_Type.fst p) k then (k, f (Product_Type.snd p)) :: ps
      else p :: update_with_aux B_ v k f ps);

fun update_with A_ v k f al =
  Assoc_List (update_with_aux A_ v k f (impl_of al));

fun update A_ k v = update_with A_ v k (fn _ => v);

fun iteratei al c f = Foldi.foldli (impl_of al) c f;

fun equal_assoc_list A_ B_ ala al =
  List.equal_lista (Product_Type.equal_prod A_ B_) (impl_of ala) (impl_of al);

end; (*struct Assoc_List*)

structure ListMapImpl : sig
  val g_sng_lm_basic_ops :
    'a HOL.equal -> 'a -> 'b -> ('a, 'b) Assoc_List.assoc_list
  val iteratei_bmap_op_list_it_lm_basic_ops :
    ('a, 'b) Assoc_List.assoc_list ->
      ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val g_size_lm_basic_ops : ('a, 'b) Assoc_List.assoc_list -> Arith.nat
  val g_list_to_map_lm_basic_ops :
    'a HOL.equal -> ('a * 'b) list -> ('a, 'b) Assoc_List.assoc_list
  val iteratei_map_op_list_it_lm_ops :
    ('a, 'b) Assoc_List.assoc_list ->
      ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

fun g_sng_lm_basic_ops A_ k v = Assoc_List.update A_ k v Assoc_List.empty;

fun iteratei_bmap_op_list_it_lm_basic_ops s = Assoc_List.iteratei s;

fun g_size_lm_basic_ops m =
  iteratei_bmap_op_list_it_lm_basic_ops m (fn _ => true) (fn _ => Arith.suc)
    Arith.zero_nat;

fun g_list_to_map_lm_basic_ops A_ l =
  List.foldl (fn m => fn (k, v) => Assoc_List.update A_ k v m) Assoc_List.empty
    (List.rev l);

fun iteratei_map_op_list_it_lm_ops s = Assoc_List.iteratei s;

end; (*struct ListMapImpl*)

structure PromelaAST : sig
  datatype varType = VarTypeBit | VarTypeBool | VarTypeByte | VarTypePid |
    VarTypeShort | VarTypeInt | VarTypeMType | VarTypeChan | VarTypeUnsigned |
    VarTypeCustom of string
  datatype binOp = BinOpAdd | BinOpSub | BinOpMul | BinOpDiv | BinOpMod |
    BinOpBitAnd | BinOpBitXor | BinOpBitOr | BinOpGr | BinOpLe | BinOpGEq |
    BinOpLEq | BinOpEq | BinOpNEq | BinOpShiftL | BinOpShiftR | BinOpAnd |
    BinOpOr
  datatype unOp = UnOpComp | UnOpMinus | UnOpNeg
  datatype expr = ExprBinOp of binOp * expr * expr | ExprUnOp of unOp * expr |
    ExprCond of expr * expr * expr | ExprLen of varRef |
    ExprPoll of varRef * recvArg list | ExprRndPoll of varRef * recvArg list |
    ExprVarRef of varRef | ExprConst of IntInf.int | ExprTimeOut | ExprNP |
    ExprEnabled of expr | ExprPC of expr |
    ExprRemoteRef of string * expr option * string | ExprGetPrio of expr |
    ExprSetPrio of expr * expr | ExprFull of varRef | ExprEmpty of varRef |
    ExprNFull of varRef | ExprNEmpty of varRef
  and varRef = VarRef of string * expr option * varRef option
  and recvArg = RecvArgVar of varRef | RecvArgEval of expr |
    RecvArgConst of IntInf.int
  datatype varDecl = VarDeclNum of string * IntInf.int option * expr option |
    VarDeclChan of
      string * IntInf.int option * (IntInf.int * varType list) option
    | VarDeclUnsigned of string * IntInf.int * expr option |
    VarDeclMType of string * IntInf.int option * string option
  datatype decl = Decl of bool option * varType * varDecl list
  datatype range = RangeFromTo of varRef * expr * expr |
    RangeIn of varRef * varRef
  datatype step = StepStmnt of stmnt * stmnt option | StepDecl of decl |
    StepXR of varRef list | StepXS of varRef list
  and stmnt = StmntIf of (step list) list | StmntDo of (step list) list |
    StmntFor of range * step list | StmntAtomic of step list |
    StmntDStep of step list | StmntSelect of range | StmntSeq of step list |
    StmntSend of varRef * expr list | StmntSortSend of varRef * expr list |
    StmntRecv of varRef * recvArg list | StmntRndRecv of varRef * recvArg list |
    StmntRecvX of varRef * recvArg list | StmntRndRecvX of varRef * recvArg list
    | StmntAssign of varRef * expr | StmntIncr of varRef | StmntDecr of varRef |
    StmntElse | StmntBreak | StmntGoTo of string |
    StmntLabeled of string * stmnt | StmntPrintF of string * expr list |
    StmntPrintM of string | StmntRun of string * expr list * IntInf.int option |
    StmntAssert of expr | StmntCond of expr | StmntCall of string * varRef list
  datatype module =
    ProcType of
      (IntInf.int option) option * string * decl list * IntInf.int option *
        expr option * step list
    | DProcType of
        (IntInf.int option) option * string * decl list * IntInf.int option *
          expr option * step list
    | Init of IntInf.int option * step list | Never of step list |
    Trace of step list | NoTrace of step list |
    Inline of string * string list * step list | TypeDef of string * decl list |
    MType of string list | ModuDecl of decl | Ltl of string * string
end = struct

datatype varType = VarTypeBit | VarTypeBool | VarTypeByte | VarTypePid |
  VarTypeShort | VarTypeInt | VarTypeMType | VarTypeChan | VarTypeUnsigned |
  VarTypeCustom of string;

datatype binOp = BinOpAdd | BinOpSub | BinOpMul | BinOpDiv | BinOpMod |
  BinOpBitAnd | BinOpBitXor | BinOpBitOr | BinOpGr | BinOpLe | BinOpGEq |
  BinOpLEq | BinOpEq | BinOpNEq | BinOpShiftL | BinOpShiftR | BinOpAnd |
  BinOpOr;

datatype unOp = UnOpComp | UnOpMinus | UnOpNeg;

datatype expr = ExprBinOp of binOp * expr * expr | ExprUnOp of unOp * expr |
  ExprCond of expr * expr * expr | ExprLen of varRef |
  ExprPoll of varRef * recvArg list | ExprRndPoll of varRef * recvArg list |
  ExprVarRef of varRef | ExprConst of IntInf.int | ExprTimeOut | ExprNP |
  ExprEnabled of expr | ExprPC of expr |
  ExprRemoteRef of string * expr option * string | ExprGetPrio of expr |
  ExprSetPrio of expr * expr | ExprFull of varRef | ExprEmpty of varRef |
  ExprNFull of varRef | ExprNEmpty of varRef
and varRef = VarRef of string * expr option * varRef option
and recvArg = RecvArgVar of varRef | RecvArgEval of expr |
  RecvArgConst of IntInf.int;

datatype varDecl = VarDeclNum of string * IntInf.int option * expr option |
  VarDeclChan of string * IntInf.int option * (IntInf.int * varType list) option
  | VarDeclUnsigned of string * IntInf.int * expr option |
  VarDeclMType of string * IntInf.int option * string option;

datatype decl = Decl of bool option * varType * varDecl list;

datatype range = RangeFromTo of varRef * expr * expr |
  RangeIn of varRef * varRef;

datatype step = StepStmnt of stmnt * stmnt option | StepDecl of decl |
  StepXR of varRef list | StepXS of varRef list
and stmnt = StmntIf of (step list) list | StmntDo of (step list) list |
  StmntFor of range * step list | StmntAtomic of step list |
  StmntDStep of step list | StmntSelect of range | StmntSeq of step list |
  StmntSend of varRef * expr list | StmntSortSend of varRef * expr list |
  StmntRecv of varRef * recvArg list | StmntRndRecv of varRef * recvArg list |
  StmntRecvX of varRef * recvArg list | StmntRndRecvX of varRef * recvArg list |
  StmntAssign of varRef * expr | StmntIncr of varRef | StmntDecr of varRef |
  StmntElse | StmntBreak | StmntGoTo of string | StmntLabeled of string * stmnt
  | StmntPrintF of string * expr list | StmntPrintM of string |
  StmntRun of string * expr list * IntInf.int option | StmntAssert of expr |
  StmntCond of expr | StmntCall of string * varRef list;

datatype module =
  ProcType of
    (IntInf.int option) option * string * decl list * IntInf.int option *
      expr option * step list
  | DProcType of
      (IntInf.int option) option * string * decl list * IntInf.int option *
        expr option * step list
  | Init of IntInf.int option * step list | Never of step list |
  Trace of step list | NoTrace of step list |
  Inline of string * string list * step list | TypeDef of string * decl list |
  MType of string list | ModuDecl of decl | Ltl of string * string;

end; (*struct PromelaAST*)

structure Sum_Type : sig
  datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
end = struct

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

end; (*struct Sum_Type*)

structure Stringa : sig
  datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
    Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC |
    NibbleD | NibbleE | NibbleF
  val equal_literal : string HOL.equal
end = struct

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string HOL.equal;

end; (*struct Stringa*)

structure Promela : sig
  datatype edgeAtomic = NonAtomic | Atomic | InAtomic
  datatype binOp = BinOpAdd | BinOpSub | BinOpMul | BinOpDiv | BinOpMod |
    BinOpGr | BinOpLe | BinOpGEq | BinOpLEq | BinOpEq | BinOpNEq | BinOpAnd |
    BinOpOr
  datatype unOp = UnOpMinus | UnOpNeg
  datatype expr = ExprBinOp of binOp * expr * expr | ExprUnOp of unOp * expr |
    ExprCond of expr * expr * expr | ExprLen of chanRef | ExprVarRef of varRef |
    ExprConst of IntInf.int | ExprMConst of IntInf.int * string | ExprTimeOut |
    ExprFull of chanRef | ExprEmpty of chanRef |
    ExprPoll of chanRef * recvArg list * bool
  and varRef = VarRef of bool * string * expr option
  and chanRef = ChanRef of varRef
  and recvArg = RecvArgVar of varRef | RecvArgEval of expr |
    RecvArgConst of IntInf.int | RecvArgMConst of IntInf.int * string
  datatype procVarDecl =
    ProcVarDeclNum of
      IntInf.int * IntInf.int * string * IntInf.int option * expr option
    | ProcVarDeclChan of string * IntInf.int option
  datatype edgeEffect = EEEnd | EEId | EEGoto | EEAssert of expr |
    EEAssign of varRef * expr | EEDecl of procVarDecl |
    EERun of string * expr list | EESend of chanRef * expr list * bool |
    EERecv of chanRef * recvArg list * bool * bool
  datatype edgeIndex = Index of Arith.nat |
    LabelJump of string * Arith.nat option
  datatype edgeCond = ECElse | ECTrue | ECFalse | ECExpr of expr |
    ECRun of string | ECSend of chanRef |
    ECRecv of chanRef * recvArg list * bool
  datatype 'a edge_ext =
    Edge_ext of edgeCond * edgeEffect * edgeIndex * IntInf.int * edgeAtomic * 'a
  val skip :
    'a * (IntInf.int * (Arith.nat * (edgeIndex * 'b))) ->
      (unit edge_ext list) list * (edgeIndex * 'a)
  datatype 'a gState_I_ext =
    GState_I_ext of Arith.nat * IntInf.int list * Arith.nat * bool * 'a
  datatype varType = VTBounded of IntInf.int * IntInf.int | VTChan
  datatype variable = Var of varType * IntInf.int |
    VArray of varType * Arith.nat * IntInf.int Vector.vector
  datatype 'a pState_ext =
    PState_ext of
      Arith.nat * (string, variable) Assoc_List.assoc_list * Arith.nat *
        IntInf.int list * Arith.nat * 'a
  datatype channel =
    Channel of IntInf.int * varType list * (IntInf.int list) list |
    HSChannel of varType list | InvChannel
  datatype 'a gState_ext =
    GState_ext of
      (string, variable) Assoc_List.assoc_list * channel list * bool *
        unit pState_ext list * 'a
  val to_I : unit gState_ext -> unit gState_I_ext gState_ext
  val vars_update :
    ((string, variable) Assoc_List.assoc_list ->
      (string, variable) Assoc_List.assoc_list) ->
      'a gState_ext -> 'a gState_ext
  datatype varDecl =
    VarDeclNum of
      IntInf.int * IntInf.int * string * IntInf.int option * expr option
    | VarDeclChan of
        string * IntInf.int option * (IntInf.int * varType list) option
  datatype procArg = ProcArg of varType * string
  datatype 'a program_ext =
    Program_ext of
      (Arith.nat * (edgeIndex * (procArg list * varDecl list))) Vector.vector *
        (string, Arith.nat) Assoc_List.assoc_list Vector.vector *
        ((IntInf.int * unit edge_ext list) Vector.vector) Vector.vector *
        string Vector.vector * (string, Arith.nat) Assoc_List.assoc_list * 'a
  datatype step = StepStmnt of stmnt * stmnt option |
    StepDecl of procVarDecl list | StepSkip
  and stmnt = StmntIf of (step list) list | StmntDo of (step list) list |
    StmntAtomic of step list | StmntSeq of step list |
    StmntSend of chanRef * expr list * bool |
    StmntRecv of chanRef * recvArg list * bool * bool |
    StmntAssign of varRef * expr | StmntElse | StmntBreak | StmntSkip |
    StmntGoTo of string | StmntLabeled of string * stmnt |
    StmntRun of string * expr list | StmntCond of expr | StmntAssert of expr
  datatype proc =
    ProcType of
      (IntInf.int option) option * string * procArg list * varDecl list *
        step list
    | Init of varDecl list * step list
  val max_array_size : 'a Arith.numeral -> 'a
  val channels : 'a gState_ext -> channel list
  val min_var_value : IntInf.int
  val max_var_value : IntInf.int
  val varType_inv : varType -> bool
  val for_all : ('a -> bool) -> 'a list -> bool
  val channel_inv : channel -> bool
  val checkVarValue : varType -> IntInf.int -> IntInf.int
  val timeout : 'a gState_ext -> bool
  val varsa : 'a pState_ext -> (string, variable) Assoc_List.assoc_list
  val vars : 'a gState_ext -> (string, variable) Assoc_List.assoc_list
  val lookupVar : variable -> IntInf.int option -> IntInf.int
  val getVar :
    bool ->
      string ->
        IntInf.int option ->
          'a gState_ext -> unit pState_ext -> IntInf.int option
  val withVar :
    bool ->
      string ->
        IntInf.int option ->
          (IntInf.int -> 'a) -> 'b gState_ext -> unit pState_ext -> 'a
  val withChannel :
    bool ->
      string ->
        IntInf.int option ->
          (Arith.nat -> channel -> 'a) -> 'b gState_ext -> unit pState_ext -> 'a
  val exprArith : 'a gState_ext -> unit pState_ext -> expr -> IntInf.int
  val recvArgsCheck :
    'a gState_ext -> unit pState_ext -> recvArg list -> IntInf.int list -> bool
  val pollCheck :
    'a gState_ext -> unit pState_ext -> channel -> recvArg list -> bool -> bool
  val toVariable :
    'a gState_ext ->
      unit pState_ext -> varDecl -> string * (variable * channel list)
  val channels_updatea :
    (IntInf.int list -> IntInf.int list) -> 'a pState_ext -> 'a pState_ext
  val channels_update :
    (channel list -> channel list) -> 'a gState_ext -> 'a gState_ext
  val channelsa : 'a pState_ext -> IntInf.int list
  val max_channels : 'a Arith.numeral -> 'a
  val mkChannels :
    'a gState_ext ->
      unit pState_ext -> channel list -> 'a gState_ext * unit pState_ext
  val mkVarChannel :
    varDecl ->
      (((string, variable) Assoc_List.assoc_list ->
         (string, variable) Assoc_List.assoc_list) ->
        'a gState_ext * unit pState_ext -> 'a gState_ext * unit pState_ext) ->
        'a gState_ext -> unit pState_ext -> 'a gState_ext * unit pState_ext
  val prio : 'a edge_ext -> IntInf.int
  val min_prio : unit edge_ext list -> IntInf.int -> IntInf.int
  val calculatePrios :
    (unit edge_ext list) list -> (IntInf.int * unit edge_ext list) list
  val target_update : (edgeIndex -> edgeIndex) -> 'a edge_ext -> 'a edge_ext
  val atomic_update : (edgeAtomic -> edgeAtomic) -> 'a edge_ext -> 'a edge_ext
  val atomica : 'a edge_ext -> edgeAtomic
  val inAtomica : unit edge_ext -> bool
  val isAtomic : unit edge_ext -> bool
  val target : 'a edge_ext -> edgeIndex
  val resolveLabel :
    string -> (string, Arith.nat) Assoc_List.assoc_list -> Arith.nat
  val resolveLabels :
    (unit edge_ext list) list ->
      (string, Arith.nat) Assoc_List.assoc_list ->
        unit edge_ext list -> unit edge_ext list
  val step_folda :
    ('a ->
      (string, Arith.nat) Assoc_List.assoc_list *
        ('b * (Arith.nat * (edgeIndex * (edgeIndex option * 'c)))) ->
        'd list * (edgeIndex * (string, Arith.nat) Assoc_List.assoc_list)) ->
      'a list ->
        (string, Arith.nat) Assoc_List.assoc_list ->
          'b -> Arith.nat ->
                  edgeIndex ->
                    edgeIndex option ->
                      'c -> Arith.nat *
                              (edgeIndex *
                                ((string, Arith.nat) Assoc_List.assoc_list *
                                  'd list))
  val step_foldL_step :
    ('a ->
      (string, Arith.nat) Assoc_List.assoc_list *
        ('b * (Arith.nat * (edgeIndex * (edgeIndex option * bool)))) ->
        'c list * (edgeIndex * (string, Arith.nat) Assoc_List.assoc_list)) ->
      'b -> edgeIndex option ->
              'a list ->
                Arith.nat *
                  (edgeIndex *
                    ((string, Arith.nat) Assoc_List.assoc_list *
                      ('c list * 'c list))) ->
                  Arith.nat *
                    (edgeIndex *
                      ((string, Arith.nat) Assoc_List.assoc_list *
                        ('c list * 'c list)))
  val step_foldL :
    ('a ->
      (string, Arith.nat) Assoc_List.assoc_list *
        ('b * (Arith.nat * (edgeIndex * (edgeIndex option * bool)))) ->
        'c list * (edgeIndex * (string, Arith.nat) Assoc_List.assoc_list)) ->
      ('a list) list ->
        (string, Arith.nat) Assoc_List.assoc_list ->
          'b -> Arith.nat ->
                  edgeIndex ->
                    edgeIndex option ->
                      Arith.nat *
                        (edgeIndex *
                          ((string, Arith.nat) Assoc_List.assoc_list *
                            ('c list * 'c list)))
  val step_fold :
    ('a ->
      (string, Arith.nat) Assoc_List.assoc_list *
        ('b * (Arith.nat * (edgeIndex * (edgeIndex option * 'c)))) ->
        'd list * (edgeIndex * (string, Arith.nat) Assoc_List.assoc_list)) ->
      'a list ->
        (string, Arith.nat) Assoc_List.assoc_list ->
          'b -> Arith.nat ->
                  edgeIndex ->
                    edgeIndex option ->
                      'c -> 'd list *
                              (edgeIndex *
                                (string, Arith.nat) Assoc_List.assoc_list)
  val add_label :
    string ->
      (string, Arith.nat) Assoc_List.assoc_list ->
        Arith.nat -> (string, Arith.nat) Assoc_List.assoc_list
  val atomize :
    Arith.nat -> Arith.nat -> unit edge_ext list -> unit edge_ext list
  val stepToState :
    step ->
      (string, Arith.nat) Assoc_List.assoc_list *
        (IntInf.int * (Arith.nat * (edgeIndex * (edgeIndex option * bool)))) ->
        (unit edge_ext list) list *
          (edgeIndex * (string, Arith.nat) Assoc_List.assoc_list)
  val stmntToState :
    stmnt ->
      (string, Arith.nat) Assoc_List.assoc_list *
        (IntInf.int * (Arith.nat * (edgeIndex * (edgeIndex option * bool)))) ->
        (unit edge_ext list) list *
          (edgeIndex * (string, Arith.nat) Assoc_List.assoc_list)
  val endState : unit edge_ext list
  val toStates :
    step list ->
      (IntInf.int * unit edge_ext list) Vector.vector *
        (edgeIndex * (string, Arith.nat) Assoc_List.assoc_list)
  val toProcess :
    Arith.nat ->
      proc ->
        (IntInf.int * unit edge_ext list) Vector.vector *
          (Arith.nat *
            (string *
              ((string, Arith.nat) Assoc_List.assoc_list *
                (Arith.nat * (edgeIndex * (procArg list * varDecl list))))))
  val emptyProc : unit pState_ext
  val procs_update :
    (unit pState_ext list -> unit pState_ext list) ->
      'a gState_ext -> 'a gState_ext
  val processes :
    'a program_ext ->
      (Arith.nat * (edgeIndex * (procArg list * varDecl list))) Vector.vector
  val proc_data : 'a program_ext -> (string, Arith.nat) Assoc_List.assoc_list
  val max_procs : 'a Arith.numeral -> 'a
  val procs : 'a gState_ext -> unit pState_ext list
  val vars_updatea :
    ((string, variable) Assoc_List.assoc_list ->
      (string, variable) Assoc_List.assoc_list) ->
      'a pState_ext -> 'a pState_ext
  val modProcArg : procArg * IntInf.int -> string * variable
  val mkProc :
    'a gState_ext ->
      unit pState_ext ->
        expr list ->
          Arith.nat * (edgeIndex * (procArg list * varDecl list)) ->
            Arith.nat -> 'a gState_ext * unit pState_ext
  val runProc :
    string ->
      expr list ->
        unit program_ext ->
          'a gState_ext -> unit pState_ext -> 'a gState_ext * unit pState_ext
  val setUp :
    varDecl list * (proc list * (string * string) list) ->
      (string, string) Assoc_List.assoc_list *
        (unit gState_ext * unit program_ext)
  val from_I : 'a gState_ext -> unit gState_ext
  val editVar : variable -> IntInf.int option -> IntInf.int -> variable
  val setVara :
    bool ->
      string ->
        IntInf.int option ->
          IntInf.int ->
            'a gState_ext -> unit pState_ext -> 'a gState_ext * unit pState_ext
  val liftVar :
    (bool ->
      string ->
        IntInf.int option -> 'a -> 'b gState_ext -> unit pState_ext -> 'c) ->
      varRef -> 'a -> 'b gState_ext -> unit pState_ext -> 'c
  val setVar :
    varRef ->
      IntInf.int ->
        'a gState_ext -> unit pState_ext -> 'a gState_ext * unit pState_ext
  val reset_I : unit gState_I_ext gState_ext -> unit gState_I_ext gState_ext
  val handshake : 'a gState_I_ext gState_ext -> Arith.nat
  val hsdata : 'a gState_I_ext gState_ext -> IntInf.int list
  val elsea : 'a gState_I_ext gState_ext -> bool
  val withChannela :
    chanRef ->
      (Arith.nat -> channel -> 'a) -> 'b gState_ext -> unit pState_ext -> 'a
  val evalCond :
    edgeCond -> unit gState_I_ext gState_ext -> unit pState_ext -> bool
  val assertVar : varRef
  val proc_names : 'a program_ext -> string Vector.vector
  val pid : 'a pState_ext -> Arith.nat
  val idx : 'a pState_ext -> Arith.nat
  val procDescr :
    (IntInf.int -> char list) ->
      unit program_ext -> unit pState_ext -> char list
  val exclusive_update :
    (Arith.nat -> Arith.nat) ->
      'a gState_I_ext gState_ext -> 'a gState_I_ext gState_ext
  val pc_update : (Arith.nat -> Arith.nat) -> 'a pState_ext -> 'a pState_ext
  val states :
    'a program_ext ->
      ((IntInf.int * unit edge_ext list) Vector.vector) Vector.vector
  val effect : 'a edge_ext -> edgeEffect
  val pc : 'a pState_ext -> Arith.nat
  val removeProcs :
    'a pState_ext list -> bool * (bool * ('a pState_ext list * IntInf.int list))
  val cleanChans : IntInf.int list -> channel list -> channel list
  val checkDeadProcs : 'a gState_ext -> 'a gState_ext
  val handshake_update :
    (Arith.nat -> Arith.nat) ->
      'a gState_I_ext gState_ext -> 'a gState_I_ext gState_ext
  val hsdata_update :
    (IntInf.int list -> IntInf.int list) ->
      'a gState_I_ext gState_ext -> 'a gState_I_ext gState_ext
  val mkVarChannelProc :
    procVarDecl ->
      'a gState_ext -> unit pState_ext -> 'a gState_ext * unit pState_ext
  val evalRecvArgs :
    recvArg list ->
      IntInf.int list ->
        unit gState_I_ext gState_ext ->
          unit pState_ext -> unit gState_I_ext gState_ext * unit pState_ext
  val find_remove : ('a -> bool) -> 'a list -> 'a option * 'a list
  val evalEffect :
    edgeEffect ->
      unit program_ext ->
        unit gState_I_ext gState_ext ->
          unit pState_ext -> unit gState_I_ext gState_ext * unit pState_ext
  val applyEdge_impl :
    unit program_ext ->
      unit edge_ext ->
        unit pState_ext ->
          unit gState_I_ext gState_ext -> unit gState_I_ext gState_ext
  val apply_triv :
    unit program_ext ->
      unit gState_I_ext gState_ext ->
        unit edge_ext * unit pState_ext -> unit gState_I_ext gState_ext
  val cond : 'a edge_ext -> edgeCond
  val evalHandshake :
    edgeCond ->
      Arith.nat -> unit gState_I_ext gState_ext -> unit pState_ext -> bool
  val getChoices :
    unit gState_I_ext gState_ext ->
      unit pState_ext ->
        unit edge_ext list -> (unit edge_ext * unit pState_ext) list
  val timeout_update : (bool -> bool) -> 'a gState_ext -> 'a gState_ext
  val exclusive : 'a gState_I_ext gState_ext -> Arith.nat
  val else_update :
    (bool -> bool) -> 'a gState_I_ext gState_ext -> 'a gState_I_ext gState_ext
  val sort_by_pri : Arith.nat -> 'a edge_ext list -> ('a edge_ext list) list
  val executable_impl :
    ((IntInf.int * unit edge_ext list) Vector.vector) Vector.vector ->
      unit gState_I_ext gState_ext -> (unit edge_ext * unit pState_ext) list
  val nexts_code_0 :
    'a HOL.equal ->
      unit program_ext ->
        (unit gState_I_ext gState_ext -> 'a) ->
          unit gState_I_ext gState_ext -> 'a Dlist.dlist Refine_Det.dres
  val nexts_code :
    'a HOL.equal ->
      unit program_ext ->
        (unit gState_ext -> 'a) ->
          unit gState_ext -> 'a Dlist.dlist Refine_Det.dres
  val equal_varTypea : varType -> varType -> bool
  val equal_variablea : variable -> variable -> bool
  val equal_variable : variable HOL.equal
  val equal_pState_exta : 'a HOL.equal -> 'a pState_ext -> 'a pState_ext -> bool
  val equal_pState_ext : 'a HOL.equal -> 'a pState_ext HOL.equal
  val equal_varType : varType HOL.equal
  val equal_channela : channel -> channel -> bool
  val equal_channel : channel HOL.equal
  val equal_gState_exta : 'a HOL.equal -> 'a gState_ext -> 'a gState_ext -> bool
  val equal_gState_ext : 'a HOL.equal -> 'a gState_ext HOL.equal
  val nexts_triv :
    unit program_ext ->
      unit gState_ext -> unit gState_ext Dlist.dlist Refine_Det.dres
  val printList :
    ('a -> char list) ->
      'a list -> char list -> char list -> char list -> char list
  val printBinOp : binOp -> char list
  val printUnOp : unOp -> char list
  val printExpr : (IntInf.int -> char list) -> expr -> char list
  val printVarRef : (IntInf.int -> char list) -> varRef -> char list
  val printChanRef : (IntInf.int -> char list) -> chanRef -> char list
  val printFun : (IntInf.int -> char list) -> char list -> chanRef -> char list
  val printRecvArg : (IntInf.int -> char list) -> recvArg -> char list
  val printVarDecl : (IntInf.int -> char list) -> procVarDecl -> char list
  val printEffect : (IntInf.int -> char list) -> edgeEffect -> char list
  val printIndex : (IntInf.int -> char list) -> edgeIndex -> char list
  val printCond : (IntInf.int -> char list) -> edgeCond -> char list
  val printEdge :
    (IntInf.int -> char list) -> Arith.nat -> unit edge_ext -> char list
  val printInitial :
    (IntInf.int -> char list) ->
      unit program_ext -> unit gState_ext -> char list
  val replay_code_0 :
    unit program_ext ->
      (unit gState_I_ext gState_ext -> bool) ->
        unit gState_I_ext gState_ext ->
          ((unit edge_ext * unit pState_ext) list) Refine_Det.dres
  val replay_code :
    unit program_ext ->
      unit gState_ext ->
        unit gState_ext -> (unit edge_ext * unit pState_ext) list
  val printConfig :
    (IntInf.int -> char list) ->
      unit program_ext -> unit gState_ext option -> unit gState_ext -> char list
  val executable_triv :
    'a * ((IntInf.int * unit edge_ext list) Vector.vector) Vector.vector ->
      unit gState_I_ext gState_ext -> (unit edge_ext * unit pState_ext) list
  val decr : varRef -> stmnt
  val incr : varRef -> stmnt
  val labels :
    'a program_ext -> (string, Arith.nat) Assoc_List.assoc_list Vector.vector
  val ppVarType : PromelaAST.varType -> varType
  val enforceChan : (varRef, chanRef) Sum_Type.sum -> chanRef
  val dealWithVar :
    (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list)) ->
      string ->
        (string -> IntInf.int option * bool -> expr option -> 'a) ->
          (string -> IntInf.int option * bool -> expr option -> 'a) ->
            (IntInf.int -> 'a) -> 'a
  val resolveIdx : expr option -> expr option -> expr option
  val liftChan : (varRef, chanRef) Sum_Type.sum -> varRef
  val ppBinOp : PromelaAST.binOp -> binOp
  val ppUnOp : PromelaAST.unOp -> unOp
  val ppExpr :
    (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list)) ->
      PromelaAST.expr -> expr
  val ppVarRef :
    (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list)) ->
      PromelaAST.varRef -> (varRef, chanRef) Sum_Type.sum
  val ppRecvArg :
    (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list)) ->
      PromelaAST.recvArg -> recvArg
  val ppVarDecl :
    (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list)) ->
      varType ->
        bool ->
          PromelaAST.varDecl ->
            ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
              ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                ((string, IntInf.int) Assoc_List.assoc_list *
                  (string, varRef) Assoc_List.assoc_list))) *
              varDecl
  val cvm_fold : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val liftDecl :
    ('a -> varType -> 'b -> PromelaAST.varDecl -> 'a * 'c) ->
      'b -> 'a -> PromelaAST.decl -> 'a * 'c list
  val ppDecl :
    bool ->
      (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
          ((string, IntInf.int) Assoc_List.assoc_list *
            (string, varRef) Assoc_List.assoc_list)) ->
        PromelaAST.decl ->
          ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
            ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
              ((string, IntInf.int) Assoc_List.assoc_list *
                (string, varRef) Assoc_List.assoc_list))) *
            varDecl list
  val ppProcVarDecl :
    (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list)) ->
      varType ->
        bool ->
          PromelaAST.varDecl ->
            ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
              ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                ((string, IntInf.int) Assoc_List.assoc_list *
                  (string, varRef) Assoc_List.assoc_list))) *
              procVarDecl
  val ppDeclProc :
    (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list)) ->
      PromelaAST.decl ->
        ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
          ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
            ((string, IntInf.int) Assoc_List.assoc_list *
              (string, varRef) Assoc_List.assoc_list))) *
          procVarDecl list
  val forInArray : varRef -> IntInf.int -> step list -> stmnt
  val forInChan : varRef -> chanRef -> step list -> stmnt
  val forFromTo : varRef -> expr -> expr -> step list -> stmnt
  val select : varRef -> expr -> expr -> stmnt
  val ppStep :
    bool *
      (varDecl list *
        ((string,
           (string list *
             ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                  ((string, IntInf.int) Assoc_List.assoc_list *
                    (string, varRef) Assoc_List.assoc_list)) ->
               ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                 ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                   ((string, IntInf.int) Assoc_List.assoc_list *
                     (string, varRef) Assoc_List.assoc_list))) *
                 step list)))
           Assoc_List.assoc_list *
          ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
            ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
              ((string, IntInf.int) Assoc_List.assoc_list *
                (string, varRef) Assoc_List.assoc_list))))) ->
      PromelaAST.step ->
        (bool *
          (varDecl list *
            ((string,
               (string list *
                 ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                    ((string, (IntInf.int option * bool))
                       Assoc_List.assoc_list *
                      ((string, IntInf.int) Assoc_List.assoc_list *
                        (string, varRef) Assoc_List.assoc_list)) ->
                   ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                     ((string, (IntInf.int option * bool))
                        Assoc_List.assoc_list *
                       ((string, IntInf.int) Assoc_List.assoc_list *
                         (string, varRef) Assoc_List.assoc_list))) *
                     step list)))
               Assoc_List.assoc_list *
              ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                  ((string, IntInf.int) Assoc_List.assoc_list *
                    (string, varRef) Assoc_List.assoc_list)))))) *
          step
  val ppStmnt :
    bool *
      (varDecl list *
        ((string,
           (string list *
             ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                  ((string, IntInf.int) Assoc_List.assoc_list *
                    (string, varRef) Assoc_List.assoc_list)) ->
               ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                 ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                   ((string, IntInf.int) Assoc_List.assoc_list *
                     (string, varRef) Assoc_List.assoc_list))) *
                 step list)))
           Assoc_List.assoc_list *
          ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
            ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
              ((string, IntInf.int) Assoc_List.assoc_list *
                (string, varRef) Assoc_List.assoc_list))))) ->
      PromelaAST.stmnt ->
        (bool *
          (varDecl list *
            ((string,
               (string list *
                 ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                    ((string, (IntInf.int option * bool))
                       Assoc_List.assoc_list *
                      ((string, IntInf.int) Assoc_List.assoc_list *
                        (string, varRef) Assoc_List.assoc_list)) ->
                   ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                     ((string, (IntInf.int option * bool))
                        Assoc_List.assoc_list *
                       ((string, IntInf.int) Assoc_List.assoc_list *
                         (string, varRef) Assoc_List.assoc_list))) *
                     step list)))
               Assoc_List.assoc_list *
              ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                  ((string, IntInf.int) Assoc_List.assoc_list *
                    (string, varRef) Assoc_List.assoc_list)))))) *
          stmnt
  val ppProcArg :
    (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list)) ->
      varType ->
        bool ->
          PromelaAST.varDecl ->
            ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
              ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                ((string, IntInf.int) Assoc_List.assoc_list *
                  (string, varRef) Assoc_List.assoc_list))) *
              procArg
  val ppDeclProcArg :
    (string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list)) ->
      PromelaAST.decl ->
        ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
          ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
            ((string, IntInf.int) Assoc_List.assoc_list *
              (string, varRef) Assoc_List.assoc_list))) *
          procArg list
  val ppModule :
    ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
      ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
        ((string, IntInf.int) Assoc_List.assoc_list *
          (string, varRef) Assoc_List.assoc_list))) *
      (string,
        (string list *
          ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
             ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
               ((string, IntInf.int) Assoc_List.assoc_list *
                 (string, varRef) Assoc_List.assoc_list)) ->
            ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
              ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                ((string, IntInf.int) Assoc_List.assoc_list *
                  (string, varRef) Assoc_List.assoc_list))) *
              step list)))
        Assoc_List.assoc_list ->
      PromelaAST.module ->
        ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
          ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
            ((string, IntInf.int) Assoc_List.assoc_list *
              (string, varRef) Assoc_List.assoc_list))) *
          ((string,
             (string list *
               ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                  ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                    ((string, IntInf.int) Assoc_List.assoc_list *
                      (string, varRef) Assoc_List.assoc_list)) ->
                 ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                   ((string, (IntInf.int option * bool)) Assoc_List.assoc_list *
                     ((string, IntInf.int) Assoc_List.assoc_list *
                       (string, varRef) Assoc_List.assoc_list))) *
                   step list)))
             Assoc_List.assoc_list *
            ((varDecl list), (proc, (string * string)) Sum_Type.sum)
              Sum_Type.sum)
  val preprocess :
    PromelaAST.module list ->
      varDecl list * (proc list * (string * string) list)
  val printEdges :
    (IntInf.int -> char list) ->
      (IntInf.int * unit edge_ext list) Vector.vector -> (char list) list
  val printLabels :
    (IntInf.int -> char list) ->
      (string, Arith.nat) Assoc_List.assoc_list -> (char list) list
  val printProcesses :
    (IntInf.int -> char list) -> unit program_ext -> (char list) list
end = struct

datatype edgeAtomic = NonAtomic | Atomic | InAtomic;

datatype binOp = BinOpAdd | BinOpSub | BinOpMul | BinOpDiv | BinOpMod | BinOpGr
  | BinOpLe | BinOpGEq | BinOpLEq | BinOpEq | BinOpNEq | BinOpAnd | BinOpOr;

datatype unOp = UnOpMinus | UnOpNeg;

datatype expr = ExprBinOp of binOp * expr * expr | ExprUnOp of unOp * expr |
  ExprCond of expr * expr * expr | ExprLen of chanRef | ExprVarRef of varRef |
  ExprConst of IntInf.int | ExprMConst of IntInf.int * string | ExprTimeOut |
  ExprFull of chanRef | ExprEmpty of chanRef |
  ExprPoll of chanRef * recvArg list * bool
and varRef = VarRef of bool * string * expr option
and chanRef = ChanRef of varRef
and recvArg = RecvArgVar of varRef | RecvArgEval of expr |
  RecvArgConst of IntInf.int | RecvArgMConst of IntInf.int * string;

datatype procVarDecl =
  ProcVarDeclNum of
    IntInf.int * IntInf.int * string * IntInf.int option * expr option
  | ProcVarDeclChan of string * IntInf.int option;

datatype edgeEffect = EEEnd | EEId | EEGoto | EEAssert of expr |
  EEAssign of varRef * expr | EEDecl of procVarDecl |
  EERun of string * expr list | EESend of chanRef * expr list * bool |
  EERecv of chanRef * recvArg list * bool * bool;

datatype edgeIndex = Index of Arith.nat |
  LabelJump of string * Arith.nat option;

datatype edgeCond = ECElse | ECTrue | ECFalse | ECExpr of expr | ECRun of string
  | ECSend of chanRef | ECRecv of chanRef * recvArg list * bool;

datatype 'a edge_ext =
  Edge_ext of edgeCond * edgeEffect * edgeIndex * IntInf.int * edgeAtomic * 'a;

fun skip (lbls, (pri, (pos, (nxt, uu)))) =
  ([[Edge_ext
       (ECExpr (ExprConst (1 : IntInf.int)), EEId, nxt, pri, NonAtomic, ())]],
    (Index pos, lbls));

datatype 'a gState_I_ext =
  GState_I_ext of Arith.nat * IntInf.int list * Arith.nat * bool * 'a;

datatype varType = VTBounded of IntInf.int * IntInf.int | VTChan;

datatype variable = Var of varType * IntInf.int |
  VArray of varType * Arith.nat * IntInf.int Vector.vector;

datatype 'a pState_ext =
  PState_ext of
    Arith.nat * (string, variable) Assoc_List.assoc_list * Arith.nat *
      IntInf.int list * Arith.nat * 'a;

datatype channel = Channel of IntInf.int * varType list * (IntInf.int list) list
  | HSChannel of varType list | InvChannel;

datatype 'a gState_ext =
  GState_ext of
    (string, variable) Assoc_List.assoc_list * channel list * bool *
      unit pState_ext list * 'a;

fun to_I (GState_ext (v, ch, t, p, ())) =
  GState_ext
    (v, ch, false, p,
      GState_I_ext (Arith.zero_nat, [], Arith.zero_nat, false, ()));

fun vars_update varsa (GState_ext (vars, channels, timeout, procs, more)) =
  GState_ext (varsa vars, channels, timeout, procs, more);

datatype varDecl =
  VarDeclNum of
    IntInf.int * IntInf.int * string * IntInf.int option * expr option
  | VarDeclChan of
      string * IntInf.int option * (IntInf.int * varType list) option;

datatype procArg = ProcArg of varType * string;

datatype 'a program_ext =
  Program_ext of
    (Arith.nat * (edgeIndex * (procArg list * varDecl list))) Vector.vector *
      (string, Arith.nat) Assoc_List.assoc_list Vector.vector *
      ((IntInf.int * unit edge_ext list) Vector.vector) Vector.vector *
      string Vector.vector * (string, Arith.nat) Assoc_List.assoc_list * 'a;

datatype step = StepStmnt of stmnt * stmnt option | StepDecl of procVarDecl list
  | StepSkip
and stmnt = StmntIf of (step list) list | StmntDo of (step list) list |
  StmntAtomic of step list | StmntSeq of step list |
  StmntSend of chanRef * expr list * bool |
  StmntRecv of chanRef * recvArg list * bool * bool |
  StmntAssign of varRef * expr | StmntElse | StmntBreak | StmntSkip |
  StmntGoTo of string | StmntLabeled of string * stmnt |
  StmntRun of string * expr list | StmntCond of expr | StmntAssert of expr;

datatype proc =
  ProcType of
    (IntInf.int option) option * string * procArg list * varDecl list *
      step list
  | Init of varDecl list * step list;

fun max_array_size A_ =
  Arith.numeral A_
    (Arith.Bit1
      (Arith.Bit1
        (Arith.Bit1
          (Arith.Bit1
            (Arith.Bit1
              (Arith.Bit1
                (Arith.Bit1
                  (Arith.Bit1
                    (Arith.Bit1
                      (Arith.Bit1
                        (Arith.Bit1
                          (Arith.Bit1
                            (Arith.Bit1
                              (Arith.Bit1 (Arith.Bit1 Arith.One)))))))))))))));

fun channels (GState_ext (vars, channels, timeout, procs, more)) = channels;

val min_var_value : IntInf.int =
  IntInf.~
    (Arith.power Arith.power_integer (2 : IntInf.int)
      (Arith.nat_of_integer (31 : IntInf.int)));

val max_var_value : IntInf.int =
  IntInf.- (Arith.power Arith.power_integer (2 : IntInf.int)
              (Arith.nat_of_integer (31 : IntInf.int)), (1 : IntInf.int));

fun varType_inv (VTBounded (l, h)) =
  IntInf.<= (min_var_value, l) andalso
    (IntInf.<= (l, 0) andalso
      (IntInf.<= (h, max_var_value) andalso IntInf.< (l, h)))
  | varType_inv VTChan = true;

fun for_all f xs = Foldi.foldli xs Fun.id (fn kv => fn _ => f kv) true;

fun channel_inv (HSChannel ts) =
  for_all varType_inv ts andalso
    Arith.less_eq_nat (List.size_list ts) (max_array_size Arith.numeral_nat)
  | channel_inv (Channel (cap, ts, q)) =
    IntInf.<= (cap, max_array_size Arith.numeral_integer) andalso
      (IntInf.<= (0, cap) andalso
        (for_all varType_inv ts andalso
          (Arith.less_eq_nat (List.size_list ts)
             (max_array_size Arith.numeral_nat) andalso
            (Arith.less_eq_nat (List.size_list q)
               (max_array_size Arith.numeral_nat) andalso
              for_all
                (fn x =>
                  Arith.equal_nat (List.size_list x) (List.size_list ts) andalso
                    for_all
                      (fn y =>
                        IntInf.<= (min_var_value, y) andalso
                          IntInf.<= (y, max_var_value))
                      x)
                q))));

fun checkVarValue (VTBounded (lRange, hRange)) vala =
  (if IntInf.<= (vala, hRange) andalso IntInf.<= (lRange, vala) then vala
    else (if ((lRange : IntInf.int) = 0) andalso IntInf.< (0, vala)
           then Arith.mod_integer vala (IntInf.+ (hRange, (1 : IntInf.int)))
           else (raise Fail "Value overflow") (fn _ => lRange)))
  | checkVarValue VTChan vala =
    (if IntInf.< (vala, min_var_value) orelse IntInf.< (max_var_value, vala)
      then (raise Fail "Value overflow") (fn _ => 0) else vala);

fun timeout (GState_ext (vars, channels, timeout, procs, more)) = timeout;

fun varsa (PState_ext (pid, vars, pc, channels, idx, more)) = vars;

fun vars (GState_ext (vars, channels, timeout, procs, more)) = vars;

fun lookupVar (Var (uu, vala)) NONE = vala
  | lookupVar (Var (uv, uw)) (SOME ux) =
    (raise Fail "Array used on var") (fn _ => 0)
  | lookupVar (VArray (uy, uz, vals)) NONE = IArray.sub vals Arith.zero_nat
  | lookupVar (VArray (va, siz, vals)) (SOME idx) =
    IArray.sub vals (Arith.nat_of_integer idx);

fun getVar gl v idx g p =
  let
    val varsb = (if gl then vars g else varsa p);
  in
    Option.map (fn x => lookupVar x idx)
      (Assoc_List.lookup Stringa.equal_literal varsb v)
  end;

fun withVar gl v idx f g p = f (Option.the (getVar gl v idx g p));

fun withChannel gl v idx f g p =
  let
    val error =
      (fn _ =>
        (raise Fail
          (String.implode
            ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" ", #"i", #"s",
               #" ", #"n", #"o", #"t", #" ", #"a", #" ", #"c", #"h", #"a", #"n",
               #"n", #"e", #"l", #":", #" "] @
              String.explode v)))
          (fn _ => f Arith.zero_nat InvChannel));
    val msg =
      String.implode
        ([#"C", #"h", #"a", #"n", #"n", #"e", #"l", #" ", #"a", #"l", #"r",
           #"e", #"a", #"d", #"y", #" ", #"c", #"l", #"o", #"s", #"e", #"d",
           #" ", #"/", #" ", #"i", #"n", #"v", #"a", #"l", #"i", #"d", #":",
           #" "] @
          String.explode v);
  in
    withVar gl v idx
      (fn i =>
        let
          val ia = Arith.nat_of_integer i;
        in
          (if Arith.less_eq_nat (List.size_list (channels g)) ia then error ()
            else let
                   val c = List.nth (channels g) ia;
                 in
                   (case c of Channel (_, _, _) => f ia c
                     | HSChannel _ => f ia c
                     | InvChannel =>
                       (raise Fail msg) (fn _ => f Arith.zero_nat InvChannel))
                 end)
        end)
      g p
  end;

fun exprArith g p (ExprConst x) = x
  | exprArith g p (ExprMConst (x, uu)) = x
  | exprArith g p ExprTimeOut = (if timeout g then (1 : IntInf.int) else 0)
  | exprArith g p (ExprLen (ChanRef (VarRef (gl, name, NONE)))) =
    withChannel gl name NONE
      (fn _ => fn a =>
        (case a of Channel (_, _, q) => Arith.integer_of_nat (List.size_list q)
          | HSChannel _ => 0))
      g p
  | exprArith g p (ExprLen (ChanRef (VarRef (gl, name, SOME idx)))) =
    withChannel gl name (SOME (exprArith g p idx))
      (fn _ => fn a =>
        (case a of Channel (_, _, q) => Arith.integer_of_nat (List.size_list q)
          | HSChannel _ => 0))
      g p
  | exprArith g p (ExprEmpty (ChanRef (VarRef (gl, name, NONE)))) =
    (if withChannel gl name NONE
          (fn _ => fn a =>
            (case a of Channel (_, _, aa) => List.null aa
              | HSChannel _ => true))
          g p
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprEmpty (ChanRef (VarRef (gl, name, SOME idx)))) =
    (if withChannel gl name (SOME (exprArith g p idx))
          (fn _ => fn a =>
            (case a of Channel (_, _, aa) => List.null aa
              | HSChannel _ => true))
          g p
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprFull (ChanRef (VarRef (gl, name, NONE)))) =
    (if withChannel gl name NONE
          (fn _ => fn a =>
            (case a
              of Channel (cap, _, q) =>
                IntInf.<= (cap, Arith.integer_of_nat (List.size_list q))
              | HSChannel _ => false))
          g p
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprFull (ChanRef (VarRef (gl, name, SOME idx)))) =
    (if withChannel gl name (SOME (exprArith g p idx))
          (fn _ => fn a =>
            (case a
              of Channel (cap, _, q) =>
                IntInf.<= (cap, Arith.integer_of_nat (List.size_list q))
              | HSChannel _ => false))
          g p
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprVarRef (VarRef (gl, name, NONE))) =
    withVar gl name NONE Fun.id g p
  | exprArith g p (ExprVarRef (VarRef (gl, name, SOME idx))) =
    withVar gl name (SOME (exprArith g p idx)) Fun.id g p
  | exprArith g p (ExprUnOp (UnOpMinus, expr)) =
    IntInf.- (0, exprArith g p expr)
  | exprArith g p (ExprUnOp (UnOpNeg, expr)) =
    Arith.mod_integer (IntInf.+ (exprArith g p expr, (1 : IntInf.int)))
      (2 : IntInf.int)
  | exprArith g p (ExprBinOp (BinOpAdd, lexpr, rexpr)) =
    IntInf.+ (exprArith g p lexpr, exprArith g p rexpr)
  | exprArith g p (ExprBinOp (BinOpSub, lexpr, rexpr)) =
    IntInf.- (exprArith g p lexpr, exprArith g p rexpr)
  | exprArith g p (ExprBinOp (BinOpMul, lexpr, rexpr)) =
    IntInf.* (exprArith g p lexpr, exprArith g p rexpr)
  | exprArith g p (ExprBinOp (BinOpDiv, lexpr, rexpr)) =
    Arith.div_integer (exprArith g p lexpr) (exprArith g p rexpr)
  | exprArith g p (ExprBinOp (BinOpMod, lexpr, rexpr)) =
    Arith.mod_integer (exprArith g p lexpr) (exprArith g p rexpr)
  | exprArith g p (ExprBinOp (BinOpGr, lexpr, rexpr)) =
    (if IntInf.< (exprArith g p rexpr, exprArith g p lexpr)
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprBinOp (BinOpLe, lexpr, rexpr)) =
    (if IntInf.< (exprArith g p lexpr, exprArith g p rexpr)
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprBinOp (BinOpGEq, lexpr, rexpr)) =
    (if IntInf.<= (exprArith g p rexpr, exprArith g p lexpr)
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprBinOp (BinOpLEq, lexpr, rexpr)) =
    (if IntInf.<= (exprArith g p lexpr, exprArith g p rexpr)
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprBinOp (BinOpEq, lexpr, rexpr)) =
    (if (((exprArith g p lexpr) : IntInf.int) = (exprArith g p rexpr))
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprBinOp (BinOpNEq, lexpr, rexpr)) =
    (if not (((exprArith g p lexpr) : IntInf.int) = (exprArith g p rexpr))
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprBinOp (BinOpAnd, lexpr, rexpr)) =
    (if not (((exprArith g p lexpr) : IntInf.int) = 0) andalso
          not (((exprArith g p rexpr) : IntInf.int) = 0)
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprBinOp (BinOpOr, lexpr, rexpr)) =
    (if not (((exprArith g p lexpr) : IntInf.int) = 0) orelse
          not (((exprArith g p rexpr) : IntInf.int) = 0)
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprCond (cexpr, texpr, fexpr)) =
    (if not (((exprArith g p cexpr) : IntInf.int) = 0) then exprArith g p texpr
      else exprArith g p fexpr)
  | exprArith g p (ExprPoll (ChanRef (VarRef (gl, name, NONE)), rs, srt)) =
    (if withChannel gl name NONE (fn _ => fn c => pollCheck g p c rs srt) g p
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprPoll (ChanRef (VarRef (gl, name, SOME idx)), rs, srt)) =
    (if withChannel gl name (SOME (exprArith g p idx))
          (fn _ => fn c => pollCheck g p c rs srt) g p
      then (1 : IntInf.int) else 0)
and recvArgsCheck vc vd [] [] = true
  | recvArgsCheck ve vf (v :: va) [] =
    (raise Fail "Length mismatch on receiving.") (fn _ => false)
  | recvArgsCheck vh vi [] (v :: va) =
    (raise Fail "Length mismatch on receiving.") (fn _ => false)
  | recvArgsCheck g p (r :: rs) (v :: vs) =
    (case r of RecvArgVar _ => true
      | RecvArgEval e => (((exprArith g p e) : IntInf.int) = v)
      | RecvArgConst c => ((c : IntInf.int) = v)
      | RecvArgMConst (c, _) => ((c : IntInf.int) = v)) andalso
      recvArgsCheck g p rs vs
and pollCheck g p InvChannel uv uw =
  (raise Fail "Channel already closed / invalid.") (fn _ => false)
  | pollCheck g p (HSChannel ux) uy uz = false
  | pollCheck g p (Channel (va, vb, q)) rs srt =
    (if List.null q then false
      else (if not srt then recvArgsCheck g p rs (List.hd q)
             else not (Option.is_none (List.find (recvArgsCheck g p rs) q))));

fun toVariable g p (VarDeclNum (lb, hb, name, siz, init)) =
  let
    val typea = VTBounded (lb, hb);
  in
    (if not (varType_inv typea)
      then (raise Fail "Invalid var def")
             (fn _ => (name, (Var (VTChan, 0), [])))
      else let
             val inita =
               checkVarValue typea
                 (case init of NONE => 0 | SOME a => exprArith g p a);
             val v =
               (case siz of NONE => Var (typea, inita)
                 | SOME s =>
                   (if Arith.less_eq_nat (Arith.nat_of_integer s)
                         (max_array_size Arith.numeral_nat)
                     then VArray
                            (typea, Arith.nat_of_integer s,
                              Vector.tabulate (s, (fn _ => inita)))
                     else (raise Fail "Invalid var def")
                            (fn _ => Var (VTChan, 0))));
           in
             (name, (v, []))
           end)
  end
  | toVariable g p (VarDeclChan (name, siz, types)) =
    let
      val size =
        (case siz of NONE => Arith.one_nata | SOME a => Arith.nat_of_integer a);
      val chans =
        (case types of NONE => []
          | SOME (cap, tys) =>
            let
              val c =
                (if ((cap : IntInf.int) = 0) then HSChannel tys
                  else Channel (cap, tys, []));
            in
              (if not (channel_inv c)
                then (raise Fail "Invalid var def") (fn _ => [])
                else List.replicate size c)
            end);
      val cidx =
        (case types of NONE => 0
          | SOME _ => Arith.integer_of_nat (List.size_list (channels g)));
      val v =
        (case siz of NONE => Var (VTChan, cidx)
          | SOME s =>
            (if Arith.less_eq_nat (Arith.nat_of_integer s)
                  (max_array_size Arith.numeral_nat)
              then VArray
                     (VTChan, Arith.nat_of_integer s,
                       Vector.tabulate
                         (s, (fn i =>
                               (if ((cidx : IntInf.int) = 0) then 0
                                 else IntInf.+ (i, cidx)))))
              else (raise Fail "Invalid var def") (fn _ => Var (VTChan, 0))));
    in
      (name, (v, chans))
    end;

fun channels_updatea channelsa (PState_ext (pid, vars, pc, channels, idx, more))
  = PState_ext (pid, vars, pc, channelsa channels, idx, more);

fun channels_update channelsa
  (GState_ext (vars, channels, timeout, procs, more)) =
  GState_ext (vars, channelsa channels, timeout, procs, more);

fun channelsa (PState_ext (pid, vars, pc, channels, idx, more)) = channels;

fun max_channels A_ =
  Arith.numeral A_
    (Arith.Bit1
      (Arith.Bit1
        (Arith.Bit1
          (Arith.Bit1
            (Arith.Bit1
              (Arith.Bit1
                (Arith.Bit1
                  (Arith.Bit1
                    (Arith.Bit1
                      (Arith.Bit1
                        (Arith.Bit1
                          (Arith.Bit1
                            (Arith.Bit1
                              (Arith.Bit1 (Arith.Bit1 Arith.One)))))))))))))));

fun mkChannels g p cs =
  (if List.null cs then (g, p)
    else let
           val l = List.size_list (channels g);
         in
           (if Arith.less_nat (max_channels Arith.numeral_nat)
                 (Arith.plus_nata l (List.size_list cs))
             then (raise Fail "Too much channels") (fn _ => (g, p))
             else let
                    val cs_p =
                      List.map Arith.integer_of_nat
                        (List.upt l (Arith.plus_nata l (List.size_list cs)));
                    val ga = channels_update (fn _ => channels g @ cs) g;
                    val a = channels_updatea (fn _ => channelsa p @ cs_p) p;
                  in
                    (ga, a)
                  end)
         end);

fun mkVarChannel v upd g p =
  let
    val (k, (va, cs)) = toVariable g p v;
    val (ga, pa) = upd (Assoc_List.update Stringa.equal_literal k va) (g, p);
  in
    mkChannels ga pa cs
  end;

fun prio (Edge_ext (cond, effect, target, prio, atomic, more)) = prio;

fun min_prio es start =
  List.fold (fn e => fn pri => (if IntInf.< (prio e, pri) then prio e else pri))
    es start;

fun calculatePrios ess = List.map (fn es => (min_prio es 0, es)) ess;

fun target_update targeta (Edge_ext (cond, effect, target, prio, atomic, more))
  = Edge_ext (cond, effect, targeta target, prio, atomic, more);

fun atomic_update atomica (Edge_ext (cond, effect, target, prio, atomic, more))
  = Edge_ext (cond, effect, target, prio, atomica atomic, more);

fun atomica (Edge_ext (cond, effect, target, prio, atomic, more)) = atomic;

fun inAtomica e =
  (case atomica e of NonAtomic => false | Atomic => true | InAtomic => true);

fun isAtomic e =
  (case atomica e of NonAtomic => false | Atomic => true | InAtomic => false);

fun target (Edge_ext (cond, effect, target, prio, atomic, more)) = target;

fun resolveLabel l lbls =
  (case Assoc_List.lookup Stringa.equal_literal lbls l
    of NONE =>
      (raise Fail
        (String.implode
          ([#"U", #"n", #"r", #"e", #"s", #"o", #"l", #"v", #"e", #"d", #" ",
             #"l", #"a", #"b", #"e", #"l", #":", #" "] @
            String.explode l)))
        (fn _ => Arith.zero_nat)
    | SOME pos => pos);

fun resolveLabels uu uv [] = []
  | resolveLabels edges lbls (e :: es) =
    let
      val check_atomic =
        (fn pos =>
          List.fold (fn ea => fn a => a andalso inAtomica ea)
            (List.nth edges pos) true);
    in
      (case target e of Index _ => e
        | LabelJump (l, NONE) =>
          let
            val pos = resolveLabel l lbls;
          in
            atomic_update
              (fn _ =>
                (if inAtomica e
                  then (if check_atomic pos then Atomic else InAtomic)
                  else NonAtomic))
              (target_update (fn _ => Index pos) e)
          end
        | LabelJump (l, SOME via) =>
          let
            val pos = resolveLabel l lbls;
          in
            atomic_update
              (fn _ =>
                (if isAtomic e
                  then (if check_atomic pos andalso check_atomic via then Atomic
                         else InAtomic)
                  else atomica e))
              (target_update (fn _ => Index pos) e)
          end)
    end ::
      resolveLabels edges lbls es;

fun step_folda g steps lbls pri pos nxt onxt iB =
  List.foldr
    (fn step => fn (posa, (nxta, (lblsa, es))) =>
      let
        val (e, (enxt, lblsb)) =
          g step (lblsa, (pri, (posa, (nxta, (onxt, iB)))));
      in
        (Arith.plus_nata posa (List.size_list e), (enxt, (lblsb, es @ e)))
      end)
    steps (pos, (nxt, (lbls, [])));

fun step_foldL_step uu uv uw [] (pos, (nxt, (lbls, (es, is)))) =
  (pos, (nxt, (lbls, (es, is))))
  | step_foldL_step g pri onxt (s :: steps) (pos, (nxt, (lbls, (es, is)))) =
    let
      val (posa, (nxta, (lblsa, ss))) =
        step_folda g steps lbls pri pos nxt onxt false;
      val (sa, (_, lblsb)) = g s (lblsa, (pri, (posa, (nxta, (onxt, true)))));
      val rs = List.butlast sa;
      val sb = List.last sa;
    in
      (Arith.plus_nata posa (List.size_list rs),
        (nxt, (lblsb, (es @ ss @ rs, sb :: is))))
    end;

fun step_foldL g stepss lbls pri pos nxt onxt =
  List.foldr (step_foldL_step g pri onxt) stepss (pos, (nxt, (lbls, ([], []))));

fun step_fold g steps lbls pri pos nxt onxt iB =
  let
    val (_, (nxta, (lblsa, s))) = step_folda g steps lbls pri pos nxt onxt iB;
  in
    (s, (nxta, lblsa))
  end;

fun add_label l lbls pos =
  (case Assoc_List.lookup Stringa.equal_literal lbls l
    of NONE => Assoc_List.update Stringa.equal_literal l pos lbls
    | SOME _ =>
      (raise Fail
        (String.implode
          ([#"L", #"a", #"b", #"e", #"l", #" ", #"g", #"i", #"v", #"e", #"n",
             #" ", #"t", #"w", #"i", #"c", #"e", #":", #" "] @
            String.explode l)))
        (fn _ => lbls));

fun atomize lp hp es =
  List.fold
    (fn e => fn esa =>
      let
        val ea =
          (case target e
            of Index p =>
              (if Arith.less_eq_nat lp p andalso Arith.less_eq_nat p hp
                then atomic_update (fn _ => Atomic) e
                else atomic_update (fn _ => InAtomic) e)
            | LabelJump (_, NONE) => atomic_update (fn _ => InAtomic) e
            | LabelJump (_, SOME via) =>
              (if Arith.less_eq_nat lp via andalso Arith.less_eq_nat via hp
                then atomic_update (fn _ => Atomic) e
                else atomic_update (fn _ => InAtomic) e));
      in
        ea :: esa
      end)
    es [];

fun stepToState (StepStmnt (s, NONE)) data = stmntToState s data
  | stepToState (StepStmnt (s, SOME u)) (lbls, (pri, (pos, (nxt, (onxt, uu)))))
    = let
        val (ues, (_, lblsa)) =
          stmntToState u (lbls, (pri, (pos, (nxt, (onxt, true)))));
        val ua = List.last ues;
        val uesa = List.butlast ues;
        val posa = Arith.plus_nata pos (List.size_list uesa);
        val pria = min_prio ua pri;
        val (ses, (spos, lblsb)) =
          stmntToState s
            (lblsa,
              (IntInf.- (pria, (1 : IntInf.int)),
                (posa, (nxt, (onxt, false)))));
        val sesa = List.map (fn a => ua @ a) ses;
      in
        (uesa @ sesa, (spos, lblsb))
      end
  | stepToState (StepDecl decls) (lbls, (pri, (pos, (nxt, (onxt, uv))))) =
    let
      val edgeF =
        (fn d => fn (lblsa, (pria, (posa, (nxta, _)))) =>
          ([[Edge_ext (ECTrue, EEDecl d, nxta, pria, NonAtomic, ())]],
            (Index posa, lblsa)));
    in
      step_fold edgeF decls lbls pri pos nxt onxt false
    end
  | stepToState StepSkip (lbls, (uw, (ux, (nxt, uy)))) = ([], (nxt, lbls))
and stmntToState StmntSkip d = skip d
  | stmntToState (StmntRecv (v, r, srt, rem)) (lbls, (pri, (pos, (nxt, vp)))) =
    ([[Edge_ext
         (ECRecv (v, r, srt), EERecv (v, r, srt, rem), nxt, pri, NonAtomic,
           ())]],
      (Index pos, lbls))
  | stmntToState (StmntSend (v, e, srt)) (lbls, (pri, (pos, (nxt, vo)))) =
    ([[Edge_ext (ECSend v, EESend (v, e, srt), nxt, pri, NonAtomic, ())]],
      (Index pos, lbls))
  | stmntToState (StmntGoTo l) (lbls, (pri, (pos, vn))) =
    ([[Edge_ext (ECTrue, EEGoto, LabelJump (l, NONE), pri, NonAtomic, ())]],
      (LabelJump (l, SOME pos), lbls))
  | stmntToState (StmntRun (n, args)) (lbls, (pri, (pos, (nxt, (onxt, vm))))) =
    ([[Edge_ext (ECRun n, EERun (n, args), nxt, pri, NonAtomic, ())]],
      (Index pos, lbls))
  | stmntToState StmntBreak (vh, (vi, (vj, (vk, (NONE, vl))))) =
    (raise Fail "Misplaced break")
      (fn _ => ([], (Index Arith.zero_nat, Assoc_List.empty)))
  | stmntToState StmntBreak (lbls, (pri, (ve, (vf, (SOME onxt, vg))))) =
    ([[Edge_ext (ECTrue, EEGoto, onxt, pri, NonAtomic, ())]], (onxt, lbls))
  | stmntToState StmntElse (lbls, (pri, (pos, (nxt, vd)))) =
    ([[Edge_ext (ECElse, EEId, nxt, pri, NonAtomic, ())]], (Index pos, lbls))
  | stmntToState (StmntCond e) (lbls, (pri, (pos, (nxt, vc)))) =
    ([[Edge_ext (ECExpr e, EEId, nxt, pri, NonAtomic, ())]], (Index pos, lbls))
  | stmntToState (StmntAssert e) (lbls, (pri, (pos, (nxt, vb)))) =
    ([[Edge_ext (ECTrue, EEAssert e, nxt, pri, NonAtomic, ())]],
      (Index pos, lbls))
  | stmntToState (StmntAssign (v, e)) (lbls, (pri, (pos, (nxt, va)))) =
    ([[Edge_ext (ECTrue, EEAssign (v, e), nxt, pri, NonAtomic, ())]],
      (Index pos, lbls))
  | stmntToState (StmntSeq steps) (lbls, (pri, (pos, (nxt, (onxt, inBlock))))) =
    step_fold stepToState steps lbls pri pos nxt onxt inBlock
  | stmntToState (StmntIf stepss) (lbls, (pri, (pos, (nxt, (onxt, uz))))) =
    let
      val (posa, (_, (lblsa, (es, is)))) =
        step_foldL stepToState stepss lbls pri pos nxt onxt;
    in
      (es @ [List.concat is], (Index posa, lblsa))
    end
  | stmntToState (StmntDo stepss) (lbls, (pri, (pos, (nxt, (onxt, inBlock))))) =
    let
      val (_, (_, (lblsa, (es, is)))) =
        step_foldL stepToState stepss lbls pri
          (Arith.plus_nata pos Arith.one_nata) (Index pos) (SOME nxt);
      val esa = List.concat is :: es;
    in
      (if inBlock then (esa @ [List.concat is], (Index pos, lblsa))
        else (esa, (Index pos, lblsa)))
    end
  | stmntToState (StmntLabeled (l, s)) (lbls, (pri, (pos, d))) =
    let
      val (es, (posa, lblsa)) = stmntToState s (lbls, (pri, (pos, d)));
      val lpos = (case posa of Index p => p | LabelJump (_, _) => pos);
      val lblsb = add_label l lblsa lpos;
    in
      (es, (posa, lblsb))
    end
  | stmntToState (StmntAtomic steps)
    (lbls, (pri, (pos, (nxt, (onxt, inBlock))))) =
    let
      val (es, (posa, lblsa)) =
        step_fold stepToState steps lbls pri pos nxt onxt inBlock;
      val esa =
        List.map (atomize pos (Arith.plus_nata pos (List.size_list es))) es;
    in
      (esa, (posa, lblsa))
    end;

val endState : unit edge_ext list =
  [Edge_ext (ECFalse, EEEnd, Index Arith.zero_nat, 0, NonAtomic, ())];

fun toStates steps =
  let
    val (states, (pos, lbls)) =
      step_fold stepToState steps Assoc_List.empty 0 Arith.one_nata
        (Index Arith.zero_nat) NONE false;
    val posa =
      (case pos of Index _ => pos
        | LabelJump (l, _) => Index (resolveLabel l lbls));
    val statesa = endState :: states;
    val statesb = List.map (resolveLabels statesa lbls) statesa;
    val statesc = calculatePrios statesb;
    val Index s = posa;
  in
    (if Arith.less_nat s (List.size_list statesc)
      then (Vector.fromList statesc, (posa, lbls))
      else (raise Fail "Oops!")
             (fn _ => (Vector.fromList statesc, (Index Arith.zero_nat, lbls))))
  end;

fun toProcess sidx (ProcType (act, name, args, decls, steps)) =
  let
    val (states, (start, lbls)) = toStates steps;
    val acta =
      (case act of NONE => Arith.zero_nat | SOME NONE => Arith.one_nata
        | SOME (SOME a) => Arith.nat_of_integer a);
  in
    (states, (acta, (name, (lbls, (sidx, (start, (args, decls)))))))
  end
  | toProcess sidx (Init (decls, steps)) =
    let
      val (states, (start, lbls)) = toStates steps;
    in
      (states,
        (Arith.one_nata, (":init:", (lbls, (sidx, (start, ([], decls)))))))
    end;

val emptyProc : unit pState_ext =
  PState_ext
    (Arith.zero_nat, Assoc_List.empty, Arith.zero_nat, [], Arith.zero_nat, ());

fun procs_update procsa (GState_ext (vars, channels, timeout, procs, more)) =
  GState_ext (vars, channels, timeout, procsa procs, more);

fun processes
  (Program_ext (processes, labels, states, proc_names, proc_data, more)) =
  processes;

fun proc_data
  (Program_ext (processes, labels, states, proc_names, proc_data, more)) =
  proc_data;

fun max_procs A_ =
  Arith.numeral A_
    (Arith.Bit1
      (Arith.Bit1
        (Arith.Bit1
          (Arith.Bit1 (Arith.Bit1 (Arith.Bit1 (Arith.Bit1 Arith.One)))))));

fun procs (GState_ext (vars, channels, timeout, procs, more)) = procs;

fun vars_updatea varsa (PState_ext (pid, vars, pc, channels, idx, more)) =
  PState_ext (pid, varsa vars, pc, channels, idx, more);

fun modProcArg x =
  let
    val (ProcArg (ty, name), vala) = x;
  in
    (if varType_inv ty
      then let
             val init = checkVarValue ty vala;
           in
             (name, Var (ty, init))
           end
      else (raise Fail "Invalid proc arg") (fn _ => (name, Var (VTChan, 0))))
  end;

fun mkProc g p args (sidx, (start, (argDecls, decls))) pidN =
  let
    val starta =
      (case start of Index x => x
        | LabelJump (_, _) => (raise Fail "UGH!") (fn _ => Arith.zero_nat));
  in
    (if not (Arith.equal_nat (List.size_list args) (List.size_list argDecls))
      then (raise Fail "Signature mismatch") (fn _ => (g, emptyProc))
      else let
             val eArgs = List.map (exprArith g p) args;
             val argVars = List.map modProcArg (List.zip argDecls eArgs);
             val pidI = Arith.integer_of_nat pidN;
             val argVarsa =
               ("_pid", Var (VTBounded (0, pidI), pidI)) :: argVars;
             val argVarsb =
               ListMapImpl.g_list_to_map_lm_basic_ops Stringa.equal_literal
                 argVarsa;
             val pa = PState_ext (pidN, argVarsb, starta, [], sidx, ());
           in
             List.foldl
               (fn (ga, pb) => fn d =>
                 mkVarChannel d (Product_Type.apsnd o vars_updatea) ga pb)
               (g, pa) decls
           end)
  end;

fun runProc name args prog g p =
  (if Arith.less_eq_nat (max_procs Arith.numeral_nat) (List.size_list (procs g))
    then (raise Fail "Too many processes") (fn _ => (g, p))
    else let
           val pid = Arith.plus_nata (List.size_list (procs g)) Arith.one_nata;
         in
           (case Assoc_List.lookup Stringa.equal_literal (proc_data prog) name
             of NONE =>
               (raise Fail
                 (String.implode
                   ([#"N", #"o", #" ", #"s", #"u", #"c", #"h", #" ", #"p", #"r",
                      #"o", #"c", #"e", #"s", #"s", #":", #" "] @
                     String.explode name)))
                 (fn _ => (g, p))
             | SOME proc_idx =>
               let
                 val (ga, proc) =
                   mkProc g p args (IArray.sub (processes prog) proc_idx) pid;
               in
                 (procs_update (fn _ => procs g @ [proc]) ga, p)
               end)
         end);

fun setUp prom =
  let
    val (decls, (procs, ltls)) = prom;
    val assertVar = Var (VTBounded (0, (1 : IntInf.int)), 0);
    val ltlsa =
      ListMapImpl.g_list_to_map_lm_basic_ops Stringa.equal_literal ltls;
    val pre_procs =
      List.map (fn (a, b) => toProcess a b)
        (List.enumerate Arith.one_nata procs);
    val procsa =
      Vector.fromList
        ((Arith.zero_nat, (Index Arith.zero_nat, ([], []))) ::
          List.map (fn (_, (_, (_, (_, p)))) => p) pre_procs);
    val labels =
      Vector.fromList
        (Assoc_List.empty ::
          List.map (fn (_, (_, (_, (l, _)))) => l) pre_procs);
    val states =
      Vector.fromList
        (Vector.fromList [(0, [])] :: List.map (fn (s, _) => s) pre_procs);
    val names =
      Vector.fromList
        ("invalid" :: List.map (fn (_, (_, (n, _))) => n) pre_procs);
    val proc_data =
      ListMapImpl.g_list_to_map_lm_basic_ops Stringa.equal_literal
        (List.map (fn (_, (_, (n, (_, (idx, _))))) => (n, idx)) pre_procs);
    val prog = Program_ext (procsa, labels, states, names, proc_data, ());
    val g =
      GState_ext
        (ListMapImpl.g_sng_lm_basic_ops Stringa.equal_literal "__assert__"
           assertVar,
          [InvChannel], false, [], ());
    val ga =
      List.foldl
        (fn ga => fn d =>
          Product_Type.fst
            (mkVarChannel d (Product_Type.apfst o vars_update) ga emptyProc))
        g decls;
    val gb =
      List.foldl
        (fn gb => fn (_, (a, (name, _))) =>
          List.foldl
            (fn gc => fn namea =>
              Product_Type.fst (runProc namea [] prog gc emptyProc))
            gb (List.replicate a name))
        ga pre_procs;
  in
    (ltlsa, (gb, prog))
  end;

fun from_I (GState_ext (v, ch, t, p, m)) = GState_ext (v, ch, t, p, ());

fun editVar (Var (typea, uu)) NONE vala = Var (typea, checkVarValue typea vala)
  | editVar (Var (uv, uw)) (SOME ux) uy =
    (raise Fail "Array used on var") (fn _ => Var (VTChan, 0))
  | editVar (VArray (typea, siz, vals)) NONE vala =
    let
      val lv = IArray.list_of vals;
      val v = List.list_update lv Arith.zero_nat (checkVarValue typea vala);
    in
      VArray (typea, siz, Vector.fromList v)
    end
  | editVar (VArray (typea, siz, vals)) (SOME idx) vala =
    let
      val lv = IArray.list_of vals;
      val v =
        List.list_update lv (Arith.nat_of_integer idx)
          (checkVarValue typea vala);
    in
      VArray (typea, siz, Vector.fromList v)
    end;

fun setVara gl v idx vala g p =
  (if gl
    then (if ((v : string) = "_") then (g, p)
           else (case Assoc_List.lookup Stringa.equal_literal (vars g) v
                  of NONE => (raise Fail "Unknown variable") (fn _ => (g, p))
                  | SOME x =>
                    (vars_update
                       (fn _ =>
                         Assoc_List.update Stringa.equal_literal v
                           (editVar x idx vala) (vars g))
                       g,
                      p)))
    else (case Assoc_List.lookup Stringa.equal_literal (varsa p) v
           of NONE => (raise Fail "Unknown variable") (fn _ => (g, p))
           | SOME x =>
             (g, vars_updatea
                   (fn _ =>
                     Assoc_List.update Stringa.equal_literal v
                       (editVar x idx vala) (varsa p))
                   p)));

fun liftVar f (VarRef (gl, v, idx)) arg g p =
  f gl v (Option.map (exprArith g p) idx) arg g p;

fun setVar x = liftVar setVara x;

fun reset_I (GState_ext (v, ch, t, p, GState_I_ext (hs, hsd, uu, uv, ()))) =
  GState_ext
    (v, ch, false, p,
      GState_I_ext
        (Arith.zero_nat,
          (if not (Arith.equal_nat hs Arith.zero_nat) then hsd else []),
          Arith.zero_nat, false, ()));

fun handshake
  (GState_ext
    (vars, channels, timeout, procs,
      GState_I_ext (handshake, hsdata, exclusive, elsea, more)))
  = handshake;

fun hsdata
  (GState_ext
    (vars, channels, timeout, procs,
      GState_I_ext (handshake, hsdata, exclusive, elsea, more)))
  = hsdata;

fun elsea
  (GState_ext
    (vars, channels, timeout, procs,
      GState_I_ext (handshake, hsdata, exclusive, elsea, more)))
  = elsea;

fun withChannela (ChanRef v) = liftVar withChannel v;

fun evalCond ECTrue uu uv = true
  | evalCond ECFalse uw ux = false
  | evalCond (ECExpr e) g l = not (((exprArith g l e) : IntInf.int) = 0)
  | evalCond (ECRun uy) g l =
    Arith.less_nat (List.size_list (procs g))
      (Arith.nat_of_integer (255 : IntInf.int))
  | evalCond ECElse g l = elsea g
  | evalCond (ECSend v) g l =
    withChannela v
      (fn _ => fn a =>
        (case a
          of Channel (cap, _, q) =>
            IntInf.< (Arith.integer_of_nat (List.size_list q), cap)
          | HSChannel _ => true))
      g l
  | evalCond (ECRecv (v, rs, srt)) g l =
    withChannela v
      (fn _ => fn c =>
        (case c of Channel (_, _, _) => pollCheck g l c rs srt
          | HSChannel _ =>
            not (Arith.equal_nat (handshake g) Arith.zero_nat) andalso
              recvArgsCheck g l rs (hsdata g)
          | InvChannel => pollCheck g l c rs srt))
      g l;

val assertVar : varRef = VarRef (true, "__assert__", NONE);

fun proc_names
  (Program_ext (processes, labels, states, proc_names, proc_data, more)) =
  proc_names;

fun pid (PState_ext (pid, vars, pc, channels, idx, more)) = pid;

fun idx (PState_ext (pid, vars, pc, channels, idx, more)) = idx;

fun procDescr f prog p =
  let
    val name = String.explode (IArray.sub (proc_names prog) (idx p));
    val id = f (Arith.integer_of_nat (pid p));
  in
    name @ [#" ", #"("] @ id @ [#")"]
  end;

fun exclusive_update exclusivea
  (GState_ext
    (vars, channels, timeout, procs,
      GState_I_ext (handshake, hsdata, exclusive, elsea, more)))
  = GState_ext
      (vars, channels, timeout, procs,
        GState_I_ext (handshake, hsdata, exclusivea exclusive, elsea, more));

fun pc_update pca (PState_ext (pid, vars, pc, channels, idx, more)) =
  PState_ext (pid, vars, pca pc, channels, idx, more);

fun states
  (Program_ext (processes, labels, states, proc_names, proc_data, more)) =
  states;

fun effect (Edge_ext (cond, effect, target, prio, atomic, more)) = effect;

fun pc (PState_ext (pid, vars, pc, channels, idx, more)) = pc;

fun removeProcs ps =
  List.foldr
    (fn p => fn (dead, (sd, (psa, dcs))) =>
      (if dead andalso Arith.equal_nat (pc p) Arith.zero_nat
        then (true, (true, (psa, channelsa p @ dcs)))
        else (false, (sd, (p :: psa, dcs)))))
    ps (true, (false, ([], [])));

fun cleanChans dchans cs =
  Product_Type.snd
    (List.foldl
      (fn (i, csa) => fn c =>
        (if List.member Arith.equal_integer dchans i
          then (IntInf.+ (i, (1 : IntInf.int)), csa @ [InvChannel])
          else (IntInf.+ (i, (1 : IntInf.int)), csa @ [c])))
      (0, []) cs);

fun checkDeadProcs g =
  (case removeProcs (procs g)
    of (_, (true, (procsa, dchans))) =>
      channels_update (fn _ => cleanChans dchans (channels g))
        (procs_update (fn _ => procsa) g)
    | (_, (false, (procsa, dchans))) => g);

fun handshake_update handshakea
  (GState_ext
    (vars, channels, timeout, procs,
      GState_I_ext (handshake, hsdata, exclusive, elsea, more)))
  = GState_ext
      (vars, channels, timeout, procs,
        GState_I_ext (handshakea handshake, hsdata, exclusive, elsea, more));

fun hsdata_update hsdataa
  (GState_ext
    (vars, channels, timeout, procs,
      GState_I_ext (handshake, hsdata, exclusive, elsea, more)))
  = GState_ext
      (vars, channels, timeout, procs,
        GState_I_ext (handshake, hsdataa hsdata, exclusive, elsea, more));

fun mkVarChannelProc v g p =
  let
    val va =
      (case v of ProcVarDeclNum (a, b, c, d, e) => VarDeclNum (a, b, c, d, e)
        | ProcVarDeclChan (name, siz) => VarDeclChan (name, siz, NONE));
    val (_, (_, _)) = toVariable g p va;
  in
    mkVarChannel va (Product_Type.apsnd o vars_updatea) g p
  end;

fun evalRecvArgs [] [] g l = (g, l)
  | evalRecvArgs (v :: va) [] g l =
    (raise Fail "Length mismatch on receiving.") (fn _ => (g, l))
  | evalRecvArgs [] (v :: va) g l =
    (raise Fail "Length mismatch on receiving.") (fn _ => (g, l))
  | evalRecvArgs (r :: rs) (v :: vs) g l =
    let
      val (a, b) =
        (case r of RecvArgVar var => setVar var v g l | RecvArgEval _ => (g, l)
          | RecvArgConst _ => (g, l) | RecvArgMConst (_, _) => (g, l));
    in
      evalRecvArgs rs vs a b
    end;

fun find_remove p (x :: xs) =
  (if p x then (SOME x, xs)
    else Product_Type.apsnd (fn a => x :: a) (find_remove p xs))
  | find_remove p [] = (NONE, []);

fun evalEffect EEEnd uu g l = (g, l)
  | evalEffect EEId uv g l = (g, l)
  | evalEffect EEGoto uw g l = (g, l)
  | evalEffect (EEAssign (v, e)) ux g l = setVar v (exprArith g l e) g l
  | evalEffect (EEDecl d) uy g l = mkVarChannelProc d g l
  | evalEffect (EERun (name, args)) prog g l = runProc name args prog g l
  | evalEffect (EEAssert e) uz g l =
    (if (((exprArith g l e) : IntInf.int) = 0)
      then setVar assertVar (1 : IntInf.int) g l else (g, l))
  | evalEffect (EESend (v, es, srt)) va g l =
    withChannela v
      (fn i => fn c =>
        let
          val aborta =
            (fn _ =>
              (raise Fail "Length mismatch on sending.") (fn _ => (g, l)));
          val esa = List.map (exprArith g l) es;
        in
          (if not (for_all
                    (fn x =>
                      IntInf.<= (min_var_value, x) andalso
                        IntInf.<= (x, max_var_value))
                    esa)
            then (raise Fail "Inv Channel") (fn _ => (g, l))
            else (case c
                   of Channel (cap, ts, q) =>
                     (if not (Arith.equal_nat (List.size_list ts)
                               (List.size_list esa)) orelse
                           not (Arith.less_nat (List.size_list q)
                                 (max_array_size Arith.numeral_nat))
                       then aborta ()
                       else let
                              val qa =
                                (if not srt then q @ [esa]
                                  else List.insort_key
 (List_lexord.linorder_list (Arith.equal_integer, Arith.linorder_integer))
 (fn x => x) esa q);
                              val ga =
                                channels_update
                                  (fn cs =>
                                    List.list_update cs i
                                      (Channel (cap, ts, qa)))
                                  g;
                            in
                              (ga, l)
                            end)
                   | HSChannel ts =>
                     (if not (Arith.equal_nat (List.size_list ts)
                               (List.size_list esa))
                       then aborta ()
                       else (handshake_update (fn _ => i)
                               (hsdata_update (fn _ => esa) g),
                              l))
                   | InvChannel => (raise Fail "INVALID") (fn _ => (g, l))))
        end)
      g l
  | evalEffect (EERecv (v, rs, srt, rem)) vb g l =
    withChannela v
      (fn i => fn a =>
        (case a
          of Channel (cap, ts, qs) =>
            (if List.null qs
              then (raise Fail "Recv from empty channel") (fn _ => (g, l))
              else let
                     val (q, qsa) =
                       (if not srt then (List.hd qs, List.tl qs)
                         else Product_Type.apfst Option.the
                                (find_remove (recvArgsCheck g l rs) qs));
                     val (ga, la) = evalRecvArgs rs q g l;
                     val gb =
                       (if rem
                         then channels_update
                                (fn cs =>
                                  List.list_update cs i
                                    (Channel (cap, ts, qsa)))
                                ga
                         else ga);
                   in
                     (gb, la)
                   end)
          | HSChannel _ =>
            let
              val (ga, la) = evalRecvArgs rs (hsdata g) g l;
              val gb =
                hsdata_update (fn _ => [])
                  (handshake_update (fn _ => Arith.zero_nat) ga);
            in
              (gb, la)
            end
          | InvChannel => (raise Fail "INVALID") (fn _ => (g, l))))
      g l;

fun applyEdge_impl prog e p g =
  let
    val (x, xa) = evalEffect (effect e) prog g p;
    val xaa =
      (case target e
        of Index t =>
          (if Arith.less_nat t
                (IArray.length (IArray.sub (states prog) (idx xa)))
            then pc_update (fn _ => t) xa
            else (raise Fail "Invalid program") (fn _ => xa))
        | LabelJump (_, _) => (raise Fail "Invalid program") (fn _ => xa));
    val xb =
      procs_update
        (fn _ =>
          List.list_update (procs x) (Arith.minus_nat (pid xaa) Arith.one_nata)
            xaa)
        x;
    val xc =
      (if isAtomic e andalso Arith.equal_nat (handshake xb) Arith.zero_nat
        then exclusive_update (fn _ => pid xaa) xb else xb);
    val xd =
      (if Arith.equal_nat (pc xaa) Arith.zero_nat then checkDeadProcs xc
        else xc);
  in
    xd
  end;

fun apply_triv prog g ep =
  applyEdge_impl prog (Product_Type.fst ep) (Product_Type.snd ep) (reset_I g);

fun cond (Edge_ext (cond, effect, target, prio, atomic, more)) = cond;

fun evalHandshake (ECRecv (v, uu, uv)) h g l =
  Arith.equal_nat h Arith.zero_nat orelse
    withChannela v
      (fn i => fn a =>
        (case a of Channel (_, _, _) => false
          | HSChannel _ => Arith.equal_nat i h))
      g l
  | evalHandshake ECElse h ux uy = Arith.equal_nat h Arith.zero_nat
  | evalHandshake ECTrue h ux uy = Arith.equal_nat h Arith.zero_nat
  | evalHandshake ECFalse h ux uy = Arith.equal_nat h Arith.zero_nat
  | evalHandshake (ECExpr v) h ux uy = Arith.equal_nat h Arith.zero_nat
  | evalHandshake (ECRun v) h ux uy = Arith.equal_nat h Arith.zero_nat
  | evalHandshake (ECSend v) h ux uy = Arith.equal_nat h Arith.zero_nat;

fun getChoices g p =
  List.foldl
    (fn e => fn ea =>
      (if evalHandshake (cond ea) (handshake g) g p andalso
            evalCond (cond ea) g p
        then (ea, p) :: e else e))
    [];

fun timeout_update timeouta (GState_ext (vars, channels, timeout, procs, more))
  = GState_ext (vars, channels, timeouta timeout, procs, more);

fun exclusive
  (GState_ext
    (vars, channels, timeout, procs,
      GState_I_ext (handshake, hsdata, exclusive, elsea, more)))
  = exclusive;

fun else_update elseaa
  (GState_ext
    (vars, channels, timeout, procs,
      GState_I_ext (handshake, hsdata, exclusive, elsea, more)))
  = GState_ext
      (vars, channels, timeout, procs,
        GState_I_ext (handshake, hsdata, exclusive, elseaa elsea, more));

fun sort_by_pri min_pri edges =
  List.foldl
    (fn es => fn e =>
      let
        val idx = Arith.nat_of_integer (Arith.abs_integer (prio e));
      in
        (if Arith.less_nat min_pri idx then (raise Fail "UGH") (fn _ => es)
          else let
                 val a = e :: List.nth es idx;
               in
                 List.list_update es idx a
               end)
      end)
    (List.replicate (Arith.plus_nata min_pri Arith.one_nata) []) edges;

fun executable_impl s g =
  let
    val x = procs g;
  in
    Foldi.foldli x (fn _ => true)
      (fn xa => fn xaa =>
        (if Arith.equal_nat (exclusive g) Arith.zero_nat orelse
              Arith.equal_nat (exclusive g) (pid xa)
          then let
                 val (xb, xc) = IArray.sub (IArray.sub s (idx xa)) (pc xa);
                 val (xd, (_, _)) =
                   (if ((xb : IntInf.int) = 0)
                     then While_Combinator.whilea
                            (fn (e, (brk, _)) =>
                              List.null e andalso
                                Arith.equal_nat brk Arith.zero_nat)
                            (fn (_, (_, xab)) =>
                              let
                                val xba = else_update (fn _ => xab) g;
                                val xd = getChoices xba xa xc;
                              in
                                (if List.null xd
                                  then (if not xab
 then (xd, (Arith.zero_nat, true)) else (xd, (Arith.one_nata, false)))
                                  else (xd, (Arith.one_nata, xab)))
                              end)
                            ([], (Arith.zero_nat, false))
                     else let
                            val xab =
                              Arith.nat_of_integer (Arith.abs_integer xb);
                            val xba = sort_by_pri xab xc;
                            val xbb = Vector.fromList xba;
                          in
                            While_Combinator.whilea
                              (fn (e, (pri, _)) =>
                                List.null e andalso Arith.less_eq_nat pri xab)
                              (fn (_, (xac, xca)) =>
                                let
                                  val xbc = IArray.sub xbb xac;
                                  val xd = else_update (fn _ => xca) g;
                                  val xe = getChoices xd xa xbc;
                                in
                                  (if List.null xe
                                    then (if not xca then (xe, (xac, true))
   else (xe, (Arith.plus_nata xac Arith.one_nata, false)))
                                    else (xe, (xac, xca)))
                                end)
                              ([], (Arith.zero_nat, false))
                          end);
               in
                 xd @ xaa
               end
          else xaa))
      []
  end;

fun nexts_code_0 A_ prog b x =
  Refine_Det.dbind (Refine_Det.DRETURN (executable_impl (states prog) x))
    (fn xa =>
      (if List.null xa
        then (if not (Arith.equal_nat (handshake x) Arith.zero_nat)
               then Refine_Det.DRETURN Dlist.empty
               else (if not (Arith.equal_nat (exclusive x) Arith.zero_nat)
                      then Refine_Det.DRETURN
                             (ListSetImpl.g_sng_ls_basic_ops A_ (b x))
                      else (if not (timeout x)
                             then nexts_code_0 A_ prog b
                                    (timeout_update (fn _ => true) x)
                             else Refine_Det.DRETURN
                                    (ListSetImpl.g_sng_ls_basic_ops A_
                                      (b (reset_I x))))))
        else let
               val xb = reset_I x;
             in
               Foldi.foldli xa
                 (fn a =>
                   (case a of Refine_Det.DSUCCEEDi => false
                     | Refine_Det.DFAILi => false
                     | Refine_Det.DRETURN _ => true))
                 (fn xaa => fn s =>
                   Refine_Det.dbind s
                     (fn xba =>
                       let
                         val (xab, xc) = xaa;
                       in
                         Refine_Det.dbind
                           (Refine_Det.DRETURN (applyEdge_impl prog xab xc xb))
                           (fn xd =>
                             (if not (Arith.equal_nat (handshake xd)
                                       Arith.zero_nat) orelse
                                   isAtomic xab
                               then Refine_Det.dbind (nexts_code_0 A_ prog b xd)
                                      (fn xac =>
(if ListSetImpl.g_isEmpty_ls_basic_ops xac andalso
      Arith.equal_nat (handshake xd) Arith.zero_nat
  then Refine_Det.DRETURN (Dlist.insert A_ (b xd) xba)
  else Refine_Det.DRETURN (ListSetImpl.g_union_ls_basic_ops A_ xac xba)))
                               else Refine_Det.DRETURN
                                      (Dlist.insert A_ (b xd) xba)))
                       end))
                 (Refine_Det.DRETURN Dlist.empty)
             end));

fun nexts_code A_ prog f g =
  let
    val x = f o from_I;
    val xa = to_I g;
  in
    Refine_Det.dbind (nexts_code_0 A_ prog x xa)
      (fn xb =>
        (if ListSetImpl.g_isEmpty_ls_basic_ops xb
          then Refine_Det.DRETURN (ListSetImpl.g_sng_ls_basic_ops A_ (x xa))
          else Refine_Det.DRETURN xb))
  end;

fun equal_varTypea VTChan (VTBounded (integer1, integer2)) = false
  | equal_varTypea (VTBounded (integer1, integer2)) VTChan = false
  | equal_varTypea (VTBounded (integer1a, integer2a))
    (VTBounded (integer1, integer2)) =
    ((integer1a : IntInf.int) = integer1) andalso
      ((integer2a : IntInf.int) = integer2)
  | equal_varTypea VTChan VTChan = true;

fun equal_variablea (VArray (varTypea, nat, iarray)) (Var (varType, integer)) =
  false
  | equal_variablea (Var (varTypea, integer)) (VArray (varType, nat, iarray)) =
    false
  | equal_variablea (VArray (varTypea, nata, iarraya))
    (VArray (varType, nat, iarray)) =
    equal_varTypea varTypea varType andalso
      (Arith.equal_nat nata nat andalso
        IArray.equal_iarray Arith.equal_integer iarraya iarray)
  | equal_variablea (Var (varTypea, integera)) (Var (varType, integer)) =
    equal_varTypea varTypea varType andalso ((integera : IntInf.int) = integer);

val equal_variable = {equal = equal_variablea} : variable HOL.equal;

fun equal_pState_exta A_ (PState_ext (pida, varsa, pca, channelsa, idxa, morea))
  (PState_ext (pid, vars, pc, channels, idx, more)) =
  Arith.equal_nat pida pid andalso
    (Assoc_List.equal_assoc_list Stringa.equal_literal equal_variable varsa
       vars andalso
      (Arith.equal_nat pca pc andalso
        (List.equal_lista Arith.equal_integer channelsa channels andalso
          (Arith.equal_nat idxa idx andalso HOL.eq A_ morea more))));

fun equal_pState_ext A_ = {equal = equal_pState_exta A_} :
  'a pState_ext HOL.equal;

val equal_varType = {equal = equal_varTypea} : varType HOL.equal;

fun equal_channela InvChannel (HSChannel lista) = false
  | equal_channela (HSChannel lista) InvChannel = false
  | equal_channela InvChannel (Channel (integer, list1, list2)) = false
  | equal_channela (Channel (integer, list1, list2)) InvChannel = false
  | equal_channela (HSChannel lista) (Channel (integer, list1, list2)) = false
  | equal_channela (Channel (integer, list1, list2)) (HSChannel lista) = false
  | equal_channela (HSChannel listaa) (HSChannel lista) =
    List.equal_lista equal_varType listaa lista
  | equal_channela (Channel (integera, list1a, list2a))
    (Channel (integer, list1, list2)) =
    ((integera : IntInf.int) = integer) andalso
      (List.equal_lista equal_varType list1a list1 andalso
        List.equal_lista (List.equal_list Arith.equal_integer) list2a list2)
  | equal_channela InvChannel InvChannel = true;

val equal_channel = {equal = equal_channela} : channel HOL.equal;

fun equal_gState_exta A_
  (GState_ext (varsa, channelsa, timeouta, procsa, morea))
  (GState_ext (vars, channels, timeout, procs, more)) =
  Assoc_List.equal_assoc_list Stringa.equal_literal equal_variable varsa
    vars andalso
    (List.equal_lista equal_channel channelsa channels andalso
      (Product_Type.equal_bool timeouta timeout andalso
        (List.equal_lista (equal_pState_ext Product_Type.equal_unit) procsa
           procs andalso
          HOL.eq A_ morea more)));

fun equal_gState_ext A_ = {equal = equal_gState_exta A_} :
  'a gState_ext HOL.equal;

fun nexts_triv prog g =
  nexts_code (equal_gState_ext Product_Type.equal_unit) prog Fun.id g;

fun printList f xs l r sep =
  let
    val fa =
      (fn str => fn x => (if List.null str then f x else str @ sep @ f x));
  in
    l @ List.foldl fa [] xs @ r
  end;

fun printBinOp BinOpAdd = [#"+"]
  | printBinOp BinOpSub = [#"-"]
  | printBinOp BinOpMul = [#"*"]
  | printBinOp BinOpDiv = [#"/"]
  | printBinOp BinOpMod = [#"m", #"o", #"d"]
  | printBinOp BinOpGr = [#">"]
  | printBinOp BinOpLe = [#"<"]
  | printBinOp BinOpGEq = [#">", #"="]
  | printBinOp BinOpLEq = [#"=", #"<"]
  | printBinOp BinOpEq = [#"=", #"="]
  | printBinOp BinOpNEq = [#"!", #"="]
  | printBinOp BinOpAnd = [#"&", #"&"]
  | printBinOp BinOpOr = [#"|", #"|"];

fun printUnOp UnOpMinus = [#"-"]
  | printUnOp UnOpNeg = [#"!"];

fun printExpr f ExprTimeOut = [#"t", #"i", #"m", #"e", #"o", #"u", #"t"]
  | printExpr f (ExprBinOp (binOp, left, right)) =
    printExpr f left @ [#" "] @ printBinOp binOp @ [#" "] @ printExpr f right
  | printExpr f (ExprUnOp (unOp, e)) = printUnOp unOp @ printExpr f e
  | printExpr f (ExprVarRef varRef) = printVarRef f varRef
  | printExpr f (ExprConst i) = f i
  | printExpr f (ExprMConst (i, m)) = String.explode m
  | printExpr f (ExprCond (c, l, r)) =
    [#"(", #" ", #"(", #"(", #" "] @
      printExpr f c @
        [#" ", #")", #")", #" ", #"-", #">", #" "] @
          printExpr f l @ [#" ", #":", #" "] @ printExpr f r @ [#" ", #")"]
  | printExpr f (ExprLen chan) = printFun f [#"l", #"e", #"n"] chan
  | printExpr f (ExprEmpty chan) =
    printFun f [#"e", #"m", #"p", #"t", #"y"] chan
  | printExpr f (ExprFull chan) = printFun f [#"f", #"u", #"l", #"l"] chan
  | printExpr f (ExprPoll (chan, es, srt)) =
    let
      val p = (if srt then [#"?", #"?"] else [#"?"]);
    in
      printChanRef f chan @
        p @ printList (printRecvArg f) es [#"["] [#"]"] [#",", #" "]
    end
and printVarRef uu (VarRef (uv, name, NONE)) = String.explode name
  | printVarRef f (VarRef (uw, name, SOME indx)) =
    String.explode name @ [#"["] @ printExpr f indx @ [#"]"]
and printChanRef f (ChanRef v) = printVarRef f v
and printFun f funa var = funa @ [#"("] @ printChanRef f var @ [#")"]
and printRecvArg f (RecvArgVar v) = printVarRef f v
  | printRecvArg f (RecvArgConst c) = f c
  | printRecvArg f (RecvArgMConst (ux, m)) = String.explode m
  | printRecvArg f (RecvArgEval e) =
    [#"e", #"v", #"a", #"l", #"("] @ printExpr f e @ [#")"];

fun printVarDecl f (ProcVarDeclNum (uu, uv, n, NONE, NONE)) =
  String.explode n @ [#" ", #"=", #" ", #"0"]
  | printVarDecl f (ProcVarDeclNum (uw, ux, n, NONE, SOME e)) =
    String.explode n @ [#" ", #"=", #" "] @ printExpr f e
  | printVarDecl f (ProcVarDeclNum (uy, uz, n, SOME i, NONE)) =
    String.explode n @ [#"["] @ f i @ [#"]", #" ", #"=", #" ", #"0"]
  | printVarDecl f (ProcVarDeclNum (va, vb, n, SOME i, SOME e)) =
    String.explode n @ [#"["] @ f i @ [#"]", #" ", #"=", #" "] @ printExpr f e
  | printVarDecl f (ProcVarDeclChan (n, NONE)) =
    [#"c", #"h", #"a", #"n", #" "] @ String.explode n
  | printVarDecl f (ProcVarDeclChan (n, SOME i)) =
    [#"c", #"h", #"a", #"n", #" "] @ String.explode n @ [#"["] @ f i @ [#"]"];

fun printEffect f EEEnd = [#"-", #"-", #" ", #"e", #"n", #"d", #" ", #"-", #"-"]
  | printEffect f EEId = [#"I", #"D"]
  | printEffect f EEGoto = [#"g", #"o", #"t", #"o"]
  | printEffect f (EEAssert e) =
    [#"a", #"s", #"s", #"e", #"r", #"t", #"("] @ printExpr f e @ [#")"]
  | printEffect f (EERun (n, uu)) =
    [#"r", #"u", #"n", #" "] @ String.explode n @ [#"(", #".", #".", #".", #")"]
  | printEffect f (EEAssign (v, expr)) =
    printVarRef f v @ [#" ", #"=", #" "] @ printExpr f expr
  | printEffect f (EEDecl d) = printVarDecl f d
  | printEffect f (EESend (v, es, srt)) =
    let
      val s = (if srt then [#"!", #"!"] else [#"!"]);
    in
      printChanRef f v @
        s @ printList (printExpr f) es [#"("] [#")"] [#",", #" "]
    end
  | printEffect f (EERecv (v, rs, srt, rem)) =
    let
      val p = (if srt then [#"?", #"?"] else [#"?"]);
      val (l, r) = (if rem then ([#"("], [#")"]) else ([#"<"], [#">"]));
    in
      printChanRef f v @ p @ printList (printRecvArg f) rs l r [#",", #" "]
    end;

fun printIndex f (Index pos) = f (Arith.integer_of_nat pos)
  | printIndex uu (LabelJump (l, uv)) = String.explode l;

fun printCond f ECElse = [#"e", #"l", #"s", #"e"]
  | printCond f ECTrue = [#"t", #"r", #"u", #"e"]
  | printCond f ECFalse = [#"f", #"a", #"l", #"s", #"e"]
  | printCond f (ECRun n) =
    [#"r", #"u", #"n", #" "] @ String.explode n @ [#"(", #".", #".", #".", #")"]
  | printCond f (ECExpr e) = printExpr f e
  | printCond f (ECSend c) = printChanRef f c @ [#"!", #" ", #".", #".", #"."]
  | printCond f (ECRecv (c, uu, uv)) =
    printChanRef f c @ [#"?", #" ", #".", #".", #"."];

fun printEdge f indx e =
  let
    val tStr = printIndex f (target e);
    val pStr =
      (if IntInf.< (prio e, 0)
        then [#" ", #"P", #"r", #"i", #"o", #":", #" "] @ f (prio e) else []);
    val atom =
      (if isAtomic e then (fn x => x @ [#" ", #"{", #"A", #"}"]) else Fun.id);
    val pEff = (fn _ => atom (printEffect f (effect e)));
    val contStr =
      (case cond e
        of ECElse =>
          atom ([#"(", #"(", #" "] @ printCond f (cond e) @ [#" ", #")", #")"])
        | ECTrue => pEff () | ECFalse => pEff ()
        | ECExpr _ =>
          atom ([#"(", #"(", #" "] @ printCond f (cond e) @ [#" ", #")", #")"])
        | ECRun _ =>
          atom ([#"(", #"(", #" "] @ printCond f (cond e) @ [#" ", #")", #")"])
        | ECSend _ => pEff () | ECRecv (_, _, _) => pEff ());
  in
    f (Arith.integer_of_nat indx) @
      [#" ", #"-", #"-", #"-", #">", #" "] @
        tStr @ [#" ", #"=", #">", #" "] @ contStr @ pStr
  end;

fun printInitial f prog g_0 =
  let
    val a = printList (procDescr f prog) (procs g_0) [] [] [#" ", #" "];
  in
    [#"I", #"n", #"i", #"t", #"i", #"a", #"l", #"l", #"y", #" ", #"r", #"u",
      #"n", #"n", #"i", #"n", #"g", #":", #" "] @
      a
  end;

fun replay_code_0 prog a x =
  Refine_Det.dbind (Refine_Det.DRETURN (executable_impl (states prog) x))
    (fn xa =>
      (if List.null xa
        then (if a x then Refine_Det.DRETURN []
               else (if not (timeout x)
                      then replay_code_0 prog a
                             (timeout_update (fn _ => true) x)
                      else (raise Fail "Stuttering should not occur on replay")
                             (fn _ => Refine_Det.DRETURN [])))
        else let
               val xb = reset_I x;
             in
               Foldi.foldli xa
                 (fn aa =>
                   (case aa of Refine_Det.DSUCCEEDi => false
                     | Refine_Det.DFAILi => false
                     | Refine_Det.DRETURN ab => List.null ab))
                 (fn xaa => fn s =>
                   Refine_Det.dbind s
                     (fn _ =>
                       let
                         val (xab, xba) = xaa;
                       in
                         Refine_Det.dbind
                           let
                             val (xc, xbb) =
                               evalEffect (effect xab) prog xb xba;
                             val xbc =
                               (case target xab
                                 of Index t =>
                                   (if Arith.less_nat t
 (IArray.length (IArray.sub (states prog) (idx xbb)))
                                     then pc_update (fn _ => t) xbb
                                     else (raise Fail "Invalid program")
    (fn _ => xbb))
                                 | LabelJump (_, _) =>
                                   (raise Fail "Invalid program")
                                     (fn _ => xbb));
                             val xd =
                               procs_update
                                 (fn _ =>
                                   List.list_update (procs xc)
                                     (Arith.minus_nat (pid xbc) Arith.one_nata)
                                     xbc)
                                 xc;
                             val xe =
                               (if isAtomic xab andalso
                                     Arith.equal_nat (handshake xd)
                                       Arith.zero_nat
                                 then exclusive_update (fn _ => pid xbc) xd
                                 else xd);
                             val aa =
                               (if Arith.equal_nat (pc xbc) Arith.zero_nat
                                 then checkDeadProcs xe else xe);
                           in
                             Refine_Det.DRETURN aa
                           end
                           (fn xc =>
                             (if not (Arith.equal_nat (handshake xc)
                                       Arith.zero_nat) orelse
                                   isAtomic xab
                               then Refine_Det.dbind (replay_code_0 prog a xc)
                                      (fn xca =>
(if List.null xca
  then (if a xc then Refine_Det.DRETURN [(xab, xba)] else Refine_Det.DRETURN [])
  else Refine_Det.DRETURN ((xab, xba) :: xca)))
                               else (if a xc
                                      then Refine_Det.DRETURN [(xab, xba)]
                                      else Refine_Det.DRETURN [])))
                       end))
                 (Refine_Det.DRETURN [])
             end));

fun replay_code prog g_1 g_2 =
  Refine_Transfer.the_res
    let
      val x = to_I g_1;
      val xa =
        (fn g => equal_gState_exta Product_Type.equal_unit (from_I g) g_2);
    in
      replay_code_0 prog xa x
    end;

fun printConfig f prog NONE g_0 = printInitial f prog g_0
  | printConfig f prog (SOME g_0) g_1 =
    let
      val eps = replay_code prog g_0 g_1;
      val print =
        (fn (e, p) => procDescr f prog p @ [#":", #" "] @ printEdge f (pc p) e);
    in
      (if List.null eps andalso
            equal_gState_exta Product_Type.equal_unit g_1 g_0
        then [#" ", #" ", #" ", #" ", #"-", #"-", #" ", #"s", #"t", #"u", #"t",
               #"t", #"e", #"r", #" ", #"-", #"-"]
        else printList print eps [] [] [#"\n", #" ", #" ", #" ", #" "])
    end;

fun executable_triv prog g = executable_impl (Product_Type.snd prog) g;

fun decr v =
  StmntAssign
    (v, ExprBinOp (BinOpSub, ExprVarRef v, ExprConst (1 : IntInf.int)));

fun incr v =
  StmntAssign
    (v, ExprBinOp (BinOpAdd, ExprVarRef v, ExprConst (1 : IntInf.int)));

fun labels
  (Program_ext (processes, labels, states, proc_names, proc_data, more)) =
  labels;

fun ppVarType PromelaAST.VarTypeBit = VTBounded (0, (1 : IntInf.int))
  | ppVarType PromelaAST.VarTypeBool = VTBounded (0, (1 : IntInf.int))
  | ppVarType PromelaAST.VarTypeByte = VTBounded (0, (255 : IntInf.int))
  | ppVarType PromelaAST.VarTypePid = VTBounded (0, (255 : IntInf.int))
  | ppVarType PromelaAST.VarTypeShort =
    VTBounded
      (IntInf.~
         (Arith.power Arith.power_integer (2 : IntInf.int)
           (Arith.nat_of_integer (15 : IntInf.int))),
        IntInf.- (Arith.power Arith.power_integer (2 : IntInf.int)
                    (Arith.nat_of_integer (15 : IntInf.int)), (1 : IntInf.int)))
  | ppVarType PromelaAST.VarTypeInt =
    VTBounded
      (IntInf.~
         (Arith.power Arith.power_integer (2 : IntInf.int)
           (Arith.nat_of_integer (31 : IntInf.int))),
        IntInf.- (Arith.power Arith.power_integer (2 : IntInf.int)
                    (Arith.nat_of_integer (31 : IntInf.int)), (1 : IntInf.int)))
  | ppVarType PromelaAST.VarTypeMType =
    VTBounded ((1 : IntInf.int), (255 : IntInf.int))
  | ppVarType PromelaAST.VarTypeChan = VTChan
  | ppVarType PromelaAST.VarTypeUnsigned = PromelaUtils.usc "VarTypeUnsigned"
  | ppVarType (PromelaAST.VarTypeCustom uu) = PromelaUtils.usc "VarTypeCustom";

fun enforceChan (Sum_Type.Inl uu) =
  PromelaUtils.err "Channel expected. Got normal variable."
  | enforceChan (Sum_Type.Inr c) = c;

fun dealWithVar cvm n fC fV fM =
  let
    val (c, (v, (m, a))) = cvm;
    val (na, idx) =
      (case Assoc_List.lookup Stringa.equal_literal a n of NONE => (n, NONE)
        | SOME (VarRef (_, aa, b)) => (aa, b));
  in
    (case Assoc_List.lookup Stringa.equal_literal m na
      of NONE =>
        (case Assoc_List.lookup Stringa.equal_literal v na
          of NONE =>
            (case Assoc_List.lookup Stringa.equal_literal c na
              of NONE =>
                PromelaUtils.err
                  (String.implode
                    ([#"U", #"n", #"k", #"n", #"o", #"w", #"n", #" ", #"v",
                       #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" ", #"r",
                       #"e", #"f", #"e", #"r", #"e", #"n", #"c", #"e", #"d",
                       #":", #" "] @
                      String.explode na))
              | SOME g => fC na g idx)
          | SOME g => fV na g idx)
      | SOME i =>
        (case idx of NONE => fM i
          | SOME _ =>
            PromelaUtils.err "Array subscript used on MType (via alias)."))
  end;

fun resolveIdx NONE NONE = NONE
  | resolveIdx (SOME v) NONE = SOME v
  | resolveIdx NONE (SOME v) = SOME v
  | resolveIdx (SOME v) (SOME va) =
    PromelaUtils.err "Array subscript used twice (via alias).";

fun liftChan (Sum_Type.Inl v) = v
  | liftChan (Sum_Type.Inr (ChanRef v)) = v;

fun ppBinOp PromelaAST.BinOpAdd = BinOpAdd
  | ppBinOp PromelaAST.BinOpSub = BinOpSub
  | ppBinOp PromelaAST.BinOpMul = BinOpMul
  | ppBinOp PromelaAST.BinOpDiv = BinOpDiv
  | ppBinOp PromelaAST.BinOpMod = BinOpMod
  | ppBinOp PromelaAST.BinOpGr = BinOpGr
  | ppBinOp PromelaAST.BinOpLe = BinOpLe
  | ppBinOp PromelaAST.BinOpGEq = BinOpGEq
  | ppBinOp PromelaAST.BinOpLEq = BinOpLEq
  | ppBinOp PromelaAST.BinOpEq = BinOpEq
  | ppBinOp PromelaAST.BinOpNEq = BinOpNEq
  | ppBinOp PromelaAST.BinOpAnd = BinOpAnd
  | ppBinOp PromelaAST.BinOpOr = BinOpOr
  | ppBinOp PromelaAST.BinOpBitAnd = PromelaUtils.usc "BinOpBitAnd"
  | ppBinOp PromelaAST.BinOpBitXor = PromelaUtils.usc "BinOpBitXor"
  | ppBinOp PromelaAST.BinOpBitOr = PromelaUtils.usc "BinOpBitOr"
  | ppBinOp PromelaAST.BinOpShiftL = PromelaUtils.usc "BinOpShiftL"
  | ppBinOp PromelaAST.BinOpShiftR = PromelaUtils.usc "BinOpShiftR";

fun ppUnOp PromelaAST.UnOpMinus = UnOpMinus
  | ppUnOp PromelaAST.UnOpNeg = UnOpNeg
  | ppUnOp PromelaAST.UnOpComp = PromelaUtils.usc "UnOpComp";

fun ppExpr cvm PromelaAST.ExprTimeOut = ExprTimeOut
  | ppExpr cvm (PromelaAST.ExprConst c) = ExprConst c
  | ppExpr cvm (PromelaAST.ExprBinOp (bo, l, r)) =
    ExprBinOp (ppBinOp bo, ppExpr cvm l, ppExpr cvm r)
  | ppExpr cvm (PromelaAST.ExprUnOp (uo, e)) =
    ExprUnOp (ppUnOp uo, ppExpr cvm e)
  | ppExpr cvm (PromelaAST.ExprCond (c, t, f)) =
    ExprCond (ppExpr cvm c, ppExpr cvm t, ppExpr cvm f)
  | ppExpr cvm (PromelaAST.ExprLen v) = ExprLen (enforceChan (ppVarRef cvm v))
  | ppExpr cvm (PromelaAST.ExprFull v) = ExprFull (enforceChan (ppVarRef cvm v))
  | ppExpr cvm (PromelaAST.ExprEmpty v) =
    ExprEmpty (enforceChan (ppVarRef cvm v))
  | ppExpr cvm (PromelaAST.ExprNFull v) =
    ExprUnOp (UnOpNeg, ExprFull (enforceChan (ppVarRef cvm v)))
  | ppExpr cvm (PromelaAST.ExprNEmpty v) =
    ExprUnOp (UnOpNeg, ExprEmpty (enforceChan (ppVarRef cvm v)))
  | ppExpr cvm (PromelaAST.ExprVarRef v) =
    let
      val to_exp = (fn _ => ExprVarRef (liftChan (ppVarRef cvm v)));
    in
      (case v
        of PromelaAST.VarRef (name, NONE, NONE) =>
          dealWithVar cvm name (fn _ => fn _ => fn _ => to_exp ())
            (fn _ => fn _ => fn _ => to_exp ()) (fn i => ExprMConst (i, name))
        | PromelaAST.VarRef (name, NONE, SOME _) => to_exp ()
        | PromelaAST.VarRef (name, SOME _, option2) => to_exp ())
    end
  | ppExpr cvm (PromelaAST.ExprPoll (v, es)) =
    ExprPoll (enforceChan (ppVarRef cvm v), List.map (ppRecvArg cvm) es, false)
  | ppExpr cvm (PromelaAST.ExprRndPoll (v, es)) =
    ExprPoll (enforceChan (ppVarRef cvm v), List.map (ppRecvArg cvm) es, true)
  | ppExpr cvm PromelaAST.ExprNP = PromelaUtils.usc "ExprNP"
  | ppExpr cvm (PromelaAST.ExprEnabled ux) = PromelaUtils.usc "ExprEnabled"
  | ppExpr cvm (PromelaAST.ExprPC uy) = PromelaUtils.usc "ExprPC"
  | ppExpr cvm (PromelaAST.ExprRemoteRef (uz, va, vb)) =
    PromelaUtils.usc "ExprRemoteRef"
  | ppExpr cvm (PromelaAST.ExprGetPrio vc) = PromelaUtils.usc "ExprGetPrio"
  | ppExpr cvm (PromelaAST.ExprSetPrio (vd, ve)) =
    PromelaUtils.usc "ExprSetPrio"
and ppVarRef cvm (PromelaAST.VarRef (name, idx, NONE)) =
  dealWithVar cvm name
    (fn namea => fn (_, g) => fn aIdx =>
      let
        val idxa = Option.map (ppExpr cvm) idx;
      in
        Sum_Type.Inr (ChanRef (VarRef (g, namea, resolveIdx idxa aIdx)))
      end)
    (fn namea => fn (_, g) => fn aIdx =>
      let
        val idxa = Option.map (ppExpr cvm) idx;
      in
        Sum_Type.Inl (VarRef (g, namea, resolveIdx idxa aIdx))
      end)
    (fn _ => PromelaUtils.err "Variable expected. Got MType.")
  | ppVarRef cvm (PromelaAST.VarRef (uu, uv, SOME uw)) =
    PromelaUtils.usc "next operation on variables"
and ppRecvArg cvm (PromelaAST.RecvArgVar v) =
  let
    val to_ra = (fn _ => RecvArgVar (liftChan (ppVarRef cvm v)));
  in
    (case v
      of PromelaAST.VarRef (name, NONE, NONE) =>
        dealWithVar cvm name (fn _ => fn _ => fn _ => to_ra ())
          (fn _ => fn _ => fn _ => to_ra ()) (fn i => RecvArgMConst (i, name))
      | PromelaAST.VarRef (name, NONE, SOME _) => to_ra ()
      | PromelaAST.VarRef (name, SOME _, option2) => to_ra ())
  end
  | ppRecvArg cvm (PromelaAST.RecvArgEval e) = RecvArgEval (ppExpr cvm e)
  | ppRecvArg cvm (PromelaAST.RecvArgConst c) = RecvArgConst c;

fun ppVarDecl va vb vc (PromelaAST.VarDeclUnsigned (vd, ve, vf)) =
  PromelaUtils.usc "VarDeclUnsigned"
  | ppVarDecl uy VTChan g (PromelaAST.VarDeclMType (name, sze, init)) =
    PromelaUtils.err "Assiging num to non-num"
  | ppVarDecl (c, (v, (m, a))) (VTBounded (l, h)) g
    (PromelaAST.VarDeclMType (name, sze, init)) =
    let
      val inita =
        Option.map
          (fn mty =>
            (case Assoc_List.lookup Stringa.equal_literal m mty
              of NONE =>
                PromelaUtils.err
                  (String.implode
                    ([#"U", #"n", #"k", #"n", #"o", #"w", #"n", #" ", #"M",
                       #"T", #"y", #"p", #"e", #" "] @
                      String.explode mty))
              | SOME mval => ExprMConst (mval, mty)))
          init;
    in
      (case Assoc_List.lookup Stringa.equal_literal c name
        of NONE =>
          (case Assoc_List.lookup Stringa.equal_literal a name
            of NONE =>
              ((c, (Assoc_List.update Stringa.equal_literal name (sze, g) v,
                     (m, a))),
                VarDeclNum (l, h, name, sze, inita))
            | SOME _ =>
              PromelaUtils.err
                (String.implode
                  ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" ", #"n",
                     #"a", #"m", #"e", #" ", #"c", #"l", #"a", #"s", #"h", #"e",
                     #"s", #" ", #"w", #"i", #"t", #"h", #" ", #"a", #"l", #"i",
                     #"a", #"s", #":", #" "] @
                    String.explode name)))
        | SOME _ =>
          PromelaUtils.err
            (String.implode
              ([#"D", #"u", #"p", #"l", #"i", #"c", #"a", #"t", #"e", #" ",
                 #"v", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" "] @
                String.explode name)))
    end
  | ppVarDecl uw (VTBounded (v, va)) g
    (PromelaAST.VarDeclChan (name, sze, init)) =
    PromelaUtils.err "Assiging chan to non-chan"
  | ppVarDecl (c, (v, (m, a))) VTChan g
    (PromelaAST.VarDeclChan (name, sze, cap)) =
    let
      val capa = Option.map (Product_Type.apsnd (List.map ppVarType)) cap;
    in
      (case Assoc_List.lookup Stringa.equal_literal c name
        of NONE =>
          (case Assoc_List.lookup Stringa.equal_literal a name
            of NONE =>
              ((Assoc_List.update Stringa.equal_literal name (sze, g) c,
                 (v, (m, a))),
                VarDeclChan (name, sze, capa))
            | SOME _ =>
              PromelaUtils.err
                (String.implode
                  ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" ", #"n",
                     #"a", #"m", #"e", #" ", #"c", #"l", #"a", #"s", #"h", #"e",
                     #"s", #" ", #"w", #"i", #"t", #"h", #" ", #"a", #"l", #"i",
                     #"a", #"s", #":", #" "] @
                    String.explode name)))
        | SOME _ =>
          PromelaUtils.err
            (String.implode
              ([#"D", #"u", #"p", #"l", #"i", #"c", #"a", #"t", #"e", #" ",
                 #"v", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" "] @
                String.explode name)))
    end
  | ppVarDecl uu VTChan g (PromelaAST.VarDeclNum (name, sze, init)) =
    PromelaUtils.err "Assiging num to non-num"
  | ppVarDecl (c, (v, (m, a))) (VTBounded (l, h)) g
    (PromelaAST.VarDeclNum (name, sze, init)) =
    (case Assoc_List.lookup Stringa.equal_literal v name
      of NONE =>
        (case Assoc_List.lookup Stringa.equal_literal a name
          of NONE =>
            ((c, (Assoc_List.update Stringa.equal_literal name (sze, g) v,
                   (m, a))),
              VarDeclNum
                (l, h, name, sze, Option.map (ppExpr (c, (v, (m, a)))) init))
          | SOME _ =>
            PromelaUtils.err
              (String.implode
                ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" ", #"n",
                   #"a", #"m", #"e", #" ", #"c", #"l", #"a", #"s", #"h", #"e",
                   #"s", #" ", #"w", #"i", #"t", #"h", #" ", #"a", #"l", #"i",
                   #"a", #"s", #":", #" "] @
                  String.explode name)))
      | SOME _ =>
        PromelaUtils.err
          (String.implode
            ([#"D", #"u", #"p", #"l", #"i", #"c", #"a", #"t", #"e", #" ", #"v",
               #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" "] @
              String.explode name)));

fun cvm_fold g cvm ss =
  List.foldl
    (fn (cvma, ssa) => fn s =>
      Product_Type.apsnd (fn sa => ssa @ [sa]) (g cvma s))
    (cvm, []) ss;

fun liftDecl f g cvm (PromelaAST.Decl (vis, t, decls)) =
  let
    val _ =
      (case vis of NONE => ()
        | SOME _ =>
          PromelaUtils.warn
            "Visibility in declarations not supported. Ignored.");
    val ta = ppVarType t;
  in
    cvm_fold (fn cvma => f cvma ta g) cvm decls
  end;

fun ppDecl x = liftDecl ppVarDecl x;

fun ppProcVarDecl cvm ty g v =
  (case ppVarDecl cvm ty g v
    of (cvma, VarDeclNum (l, h, name, sze, init)) =>
      (cvma, ProcVarDeclNum (l, h, name, sze, init))
    | (cvma, VarDeclChan (name, sze, NONE)) =>
      (cvma, ProcVarDeclChan (name, sze))
    | (cvma, VarDeclChan (name, sze, SOME _)) =>
      PromelaUtils.err
        "Channel initilizations only allowed at the beginning of proctypes.");

fun ppDeclProc x = liftDecl ppProcVarDecl false x;

fun forInArray i n steps =
  let
    val loop_pre = StepStmnt (StmntAssign (i, ExprConst 0), NONE);
    val loop_cond =
      StepStmnt
        (StmntCond (ExprBinOp (BinOpLe, ExprVarRef i, ExprConst n)), NONE);
    val loop_incr = StepStmnt (incr i, NONE);
    val loop_body = loop_cond :: steps @ [loop_incr];
    val loop_abort =
      [StepStmnt (StmntElse, NONE), StepStmnt (StmntBreak, NONE)];
    val loop = StepStmnt (StmntDo [loop_body, loop_abort], NONE);
  in
    StmntSeq [loop_pre, loop]
  end;

fun forInChan msg c steps =
  let
    val tmpStr = ":tmp:";
    val loop_pre =
      StepDecl
        [ProcVarDeclNum
           (0, (255 : IntInf.int), tmpStr, NONE, SOME (ExprConst 0))];
    val tmp = VarRef (false, tmpStr, NONE);
    val loop_cond =
      StepStmnt
        (StmntCond (ExprBinOp (BinOpLe, ExprVarRef tmp, ExprLen c)), NONE);
    val loop_incr = StepStmnt (incr tmp, NONE);
    val recv = StepStmnt (StmntRecv (c, [RecvArgVar msg], false, true), NONE);
    val send = StepStmnt (StmntSend (c, [ExprVarRef msg], false), NONE);
    val loop_body = [loop_cond, recv, send] @ steps @ [loop_incr];
    val loop_abort =
      [StepStmnt (StmntElse, NONE), StepStmnt (StmntBreak, NONE)];
    val loop = StepStmnt (StmntDo [loop_body, loop_abort], NONE);
  in
    StmntSeq [loop_pre, loop]
  end;

fun forFromTo i lb ub steps =
  let
    val loop_pre = StepStmnt (StmntAssign (i, lb), NONE);
    val loop_cond =
      StepStmnt (StmntCond (ExprBinOp (BinOpLEq, ExprVarRef i, ub)), NONE);
    val loop_incr = StepStmnt (incr i, NONE);
    val loop_body = loop_cond :: steps @ [loop_incr];
    val loop_abort =
      [StepStmnt (StmntElse, NONE), StepStmnt (StmntBreak, NONE)];
    val loop = StepStmnt (StmntDo [loop_body, loop_abort], NONE);
  in
    StmntSeq [loop_pre, loop]
  end;

fun select i lb ub =
  let
    val pre = StepStmnt (StmntAssign (i, lb), NONE);
    val cond =
      StepStmnt (StmntCond (ExprBinOp (BinOpLe, ExprVarRef i, ub)), NONE);
    val incra = StepStmnt (incr i, NONE);
    val loop_body = [cond, incra];
    val loop_abort = [StepStmnt (StmntBreak, NONE)];
    val loop = StepStmnt (StmntDo [loop_body, loop_abort], NONE);
  in
    StmntSeq [pre, loop]
  end;

fun ppStep cvm (PromelaAST.StepStmnt (s, u)) =
  let
    val (cvma, sa) = ppStmnt cvm s;
  in
    (case u of NONE => (cvma, StepStmnt (sa, NONE))
      | SOME ua =>
        let
          val (cvmb, ub) = ppStmnt cvma ua;
        in
          (cvmb, StepStmnt (sa, SOME ub))
        end)
  end
  | ppStep (false, (ps, (i, cvm))) (PromelaAST.StepDecl d) =
    Product_Type.map_pair (fn cvma => (false, (ps, (i, cvma)))) StepDecl
      (ppDeclProc cvm d)
  | ppStep (true, (ps, (i, cvm))) (PromelaAST.StepDecl d) =
    let
      val (cvma, psa) = ppDecl false cvm d;
    in
      ((true, (ps @ psa, (i, cvma))), StepSkip)
    end
  | ppStep (uu, cvm) (PromelaAST.StepXR uv) =
    let
      val _ = PromelaUtils.warn "StepXR not supported. Ignored.";
    in
      ((false, cvm), StepSkip)
    end
  | ppStep (uw, cvm) (PromelaAST.StepXS ux) =
    let
      val _ = PromelaUtils.warn "StepXS not supported. Ignored.";
    in
      ((false, cvm), StepSkip)
    end
and ppStmnt cvm (PromelaAST.StmntDStep we) = PromelaUtils.usc "StmntDStep"
  | ppStmnt (wd, (ps, (inl, cvm))) (PromelaAST.StmntCall (macro, args)) =
    let
      val argsa = List.map (liftChan o ppVarRef cvm) args;
      val (c, (v, (m, a))) = cvm;
    in
      (case Assoc_List.lookup Stringa.equal_literal inl macro
        of NONE =>
          PromelaUtils.err
            (String.implode
              ([#"C", #"a", #"l", #"l", #"i", #"n", #"g", #" ", #"u", #"n",
                 #"k", #"n", #"o", #"w", #"n", #" ", #"m", #"a", #"c", #"r",
                 #"o", #" "] @
                String.explode macro))
        | SOME (names, sF) =>
          (if not (Arith.equal_nat (List.size_list names)
                    (List.size_list argsa))
            then PromelaUtils.err "Called macro with wrong number of arguments."
            else let
                   val aa =
                     List.foldl
                       (fn aa => fn (k, va) =>
                         Assoc_List.update Stringa.equal_literal k va aa)
                       a (List.zip names argsa);
                   val (b, ca) = sF (c, (v, (m, aa)));
                 in
                   let
                     val (cb, (va, (ma, _))) = b;
                   in
                     (fn steps =>
                       ((false, (ps, (inl, (cb, (va, (ma, a)))))),
                         StmntSeq steps))
                   end
                     ca
                 end))
    end
  | ppStmnt (wa, cvm) (PromelaAST.StmntSelect (PromelaAST.RangeIn (wb, wc))) =
    PromelaUtils.err "\"in\" not allowed in select"
  | ppStmnt (vz, (ps, (inl, cvm)))
    (PromelaAST.StmntSelect (PromelaAST.RangeFromTo (i, lb, ub))) =
    let
      val ia = liftChan (ppVarRef cvm i);
      val (lba, uba) = (ppExpr cvm lb, ppExpr cvm ub);
    in
      ((false, (ps, (inl, cvm))), select ia lba uba)
    end
  | ppStmnt (vy, (ps, (inl, cvm)))
    (PromelaAST.StmntFor (PromelaAST.RangeIn (i, v), steps)) =
    let
      val ia = liftChan (ppVarRef cvm i);
      val (cvma, stepsa) = cvm_fold ppStep (false, (ps, (inl, cvm))) steps;
    in
      (case ppVarRef cvm v
        of Sum_Type.Inl (VarRef (_, xa, NONE)) =>
          let
            val (_, (va, _)) = cvm;
          in
            (case Product_Type.fst
                    (Option.the (Assoc_List.lookup Stringa.equal_literal va xa))
              of NONE => PromelaUtils.err "Iterating over non-array variable."
              | SOME n => (cvma, forInArray ia n stepsa))
          end
        | Sum_Type.Inl (VarRef (_, xa, SOME _)) =>
          PromelaUtils.err "Iterating over array-member."
        | Sum_Type.Inr c => (cvma, forInChan ia c stepsa))
    end
  | ppStmnt (vx, (ps, (inl, cvm)))
    (PromelaAST.StmntFor (PromelaAST.RangeFromTo (i, lb, ub), steps)) =
    let
      val ia = liftChan (ppVarRef cvm i);
      val (lba, uba) = (ppExpr cvm lb, ppExpr cvm ub);
    in
      Product_Type.apsnd (forFromTo ia lba uba)
        (cvm_fold ppStep (false, (ps, (inl, cvm))) steps)
    end
  | ppStmnt (vv, cvm) (PromelaAST.StmntPrintM vw) =
    let
      val _ = PromelaUtils.warn "PrintM ignored";
    in
      ((false, cvm), StmntSkip)
    end
  | ppStmnt (vs, cvm) (PromelaAST.StmntPrintF (vt, vu)) =
    let
      val _ = PromelaUtils.warn "PrintF ignored";
    in
      ((false, cvm), StmntSkip)
    end
  | ppStmnt (vr, (ps, (i, cvm))) (PromelaAST.StmntDecr v) =
    ((false, (ps, (i, cvm))), decr (liftChan (ppVarRef cvm v)))
  | ppStmnt (vq, (ps, (i, cvm))) (PromelaAST.StmntIncr v) =
    ((false, (ps, (i, cvm))), incr (liftChan (ppVarRef cvm v)))
  | ppStmnt (vp, cvm) (PromelaAST.StmntDo sss) =
    Product_Type.apsnd StmntDo (cvm_fold (cvm_fold ppStep) (false, cvm) sss)
  | ppStmnt (vo, cvm) (PromelaAST.StmntIf sss) =
    Product_Type.apsnd StmntIf (cvm_fold (cvm_fold ppStep) (false, cvm) sss)
  | ppStmnt (vn, cvm) (PromelaAST.StmntAtomic ss) =
    Product_Type.apsnd StmntAtomic (cvm_fold ppStep (false, cvm) ss)
  | ppStmnt (vm, cvm) (PromelaAST.StmntSeq ss) =
    Product_Type.apsnd StmntSeq (cvm_fold ppStep (false, cvm) ss)
  | ppStmnt (vl, (ps, (i, cvm))) (PromelaAST.StmntRun (n, es, p)) =
    let
      val _ =
        (case p of NONE => ()
          | SOME _ =>
            PromelaUtils.warn "Priorities for 'run' not supported. Ignored.");
    in
      ((false, (ps, (i, cvm))), StmntRun (n, List.map (ppExpr cvm) es))
    end
  | ppStmnt (vk, (ps, (i, cvm))) (PromelaAST.StmntRndRecvX (v, rs)) =
    ((false, (ps, (i, cvm))),
      StmntRecv
        (enforceChan (ppVarRef cvm v), List.map (ppRecvArg cvm) rs, true,
          false))
  | ppStmnt (vj, (ps, (i, cvm))) (PromelaAST.StmntRndRecv (v, rs)) =
    ((false, (ps, (i, cvm))),
      StmntRecv
        (enforceChan (ppVarRef cvm v), List.map (ppRecvArg cvm) rs, true, true))
  | ppStmnt (vi, (ps, (i, cvm))) (PromelaAST.StmntRecvX (v, rs)) =
    ((false, (ps, (i, cvm))),
      StmntRecv
        (enforceChan (ppVarRef cvm v), List.map (ppRecvArg cvm) rs, false,
          false))
  | ppStmnt (vh, (ps, (i, cvm))) (PromelaAST.StmntRecv (v, rs)) =
    ((false, (ps, (i, cvm))),
      StmntRecv
        (enforceChan (ppVarRef cvm v), List.map (ppRecvArg cvm) rs, false,
          true))
  | ppStmnt (vg, (ps, (i, cvm))) (PromelaAST.StmntSortSend (v, es)) =
    ((false, (ps, (i, cvm))),
      StmntSend (enforceChan (ppVarRef cvm v), List.map (ppExpr cvm) es, true))
  | ppStmnt (vf, (ps, (i, cvm))) (PromelaAST.StmntSend (v, es)) =
    ((false, (ps, (i, cvm))),
      StmntSend (enforceChan (ppVarRef cvm v), List.map (ppExpr cvm) es, false))
  | ppStmnt (ve, (ps, (i, cvm))) (PromelaAST.StmntAssign (v, e)) =
    ((false, (ps, (i, cvm))),
      StmntAssign (liftChan (ppVarRef cvm v), ppExpr cvm e))
  | ppStmnt (vd, (ps, (i, cvm))) (PromelaAST.StmntAssert e) =
    ((false, (ps, (i, cvm))), StmntAssert (ppExpr cvm e))
  | ppStmnt (vc, (ps, (i, cvm))) (PromelaAST.StmntCond e) =
    ((false, (ps, (i, cvm))), StmntCond (ppExpr cvm e))
  | ppStmnt (vb, cvm) (PromelaAST.StmntLabeled (l, s)) =
    Product_Type.apsnd (fn a => StmntLabeled (l, a)) (ppStmnt (false, cvm) s)
  | ppStmnt (va, cvm) (PromelaAST.StmntGoTo l) = ((false, cvm), StmntGoTo l)
  | ppStmnt (uz, cvm) PromelaAST.StmntElse = ((false, cvm), StmntElse)
  | ppStmnt (uy, cvm) PromelaAST.StmntBreak = ((false, cvm), StmntBreak);

fun ppProcArg vm vn vo (PromelaAST.VarDeclUnsigned (vp, vq, vr)) =
  PromelaUtils.usc "VarDeclUnsigned"
  | ppProcArg vg vh vi (PromelaAST.VarDeclMType (vj, vk, SOME v)) =
    PromelaUtils.err "Invalid proctype arguments"
  | ppProcArg vg vh vi (PromelaAST.VarDeclMType (vj, SOME v, vl)) =
    PromelaUtils.err "Invalid proctype arguments"
  | ppProcArg vg VTChan vi (PromelaAST.VarDeclMType (vj, vk, vl)) =
    PromelaUtils.err "Invalid proctype arguments"
  | ppProcArg (c, (v, (m, a))) (VTBounded (l, h)) g
    (PromelaAST.VarDeclMType (name, NONE, NONE)) =
    (case Assoc_List.lookup Stringa.equal_literal v name
      of NONE =>
        (case Assoc_List.lookup Stringa.equal_literal a name
          of NONE =>
            ((c, (Assoc_List.update Stringa.equal_literal name (NONE, g) v,
                   (m, a))),
              ProcArg (VTBounded (l, h), name))
          | SOME _ =>
            PromelaUtils.err
              (String.implode
                ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" ", #"n",
                   #"a", #"m", #"e", #" ", #"c", #"l", #"a", #"s", #"h", #"e",
                   #"s", #" ", #"w", #"i", #"t", #"h", #" ", #"a", #"l", #"i",
                   #"a", #"s", #":", #" "] @
                  String.explode name)))
      | SOME _ =>
        PromelaUtils.err
          (String.implode
            ([#"D", #"u", #"p", #"l", #"i", #"c", #"a", #"t", #"e", #" ", #"v",
               #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" "] @
              String.explode name)))
  | ppProcArg va vb vc (PromelaAST.VarDeclChan (vd, ve, SOME v)) =
    PromelaUtils.err "Invalid proctype arguments"
  | ppProcArg va vb vc (PromelaAST.VarDeclChan (vd, SOME v, vf)) =
    PromelaUtils.err "Invalid proctype arguments"
  | ppProcArg va (VTBounded (v, vg)) vc (PromelaAST.VarDeclChan (vd, ve, vf)) =
    PromelaUtils.err "Invalid proctype arguments"
  | ppProcArg (c, (v, (m, a))) VTChan g
    (PromelaAST.VarDeclChan (name, NONE, NONE)) =
    (case Assoc_List.lookup Stringa.equal_literal c name
      of NONE =>
        (case Assoc_List.lookup Stringa.equal_literal a name
          of NONE =>
            ((Assoc_List.update Stringa.equal_literal name (NONE, g) c,
               (v, (m, a))),
              ProcArg (VTChan, name))
          | SOME _ =>
            PromelaUtils.err
              (String.implode
                ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" ", #"n",
                   #"a", #"m", #"e", #" ", #"c", #"l", #"a", #"s", #"h", #"e",
                   #"s", #" ", #"w", #"i", #"t", #"h", #" ", #"a", #"l", #"i",
                   #"a", #"s", #":", #" "] @
                  String.explode name)))
      | SOME _ =>
        PromelaUtils.err
          (String.implode
            ([#"D", #"u", #"p", #"l", #"i", #"c", #"a", #"t", #"e", #" ", #"v",
               #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" "] @
              String.explode name)))
  | ppProcArg uu uv uw (PromelaAST.VarDeclNum (ux, uy, SOME v)) =
    PromelaUtils.err "Invalid proctype arguments"
  | ppProcArg uu uv uw (PromelaAST.VarDeclNum (ux, SOME v, uz)) =
    PromelaUtils.err "Invalid proctype arguments"
  | ppProcArg uu VTChan uw (PromelaAST.VarDeclNum (ux, uy, uz)) =
    PromelaUtils.err "Invalid proctype arguments"
  | ppProcArg (c, (v, (m, a))) (VTBounded (l, h)) g
    (PromelaAST.VarDeclNum (name, NONE, NONE)) =
    (case Assoc_List.lookup Stringa.equal_literal v name
      of NONE =>
        (case Assoc_List.lookup Stringa.equal_literal a name
          of NONE =>
            ((c, (Assoc_List.update Stringa.equal_literal name (NONE, g) v,
                   (m, a))),
              ProcArg (VTBounded (l, h), name))
          | SOME _ =>
            PromelaUtils.err
              (String.implode
                ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" ", #"n",
                   #"a", #"m", #"e", #" ", #"c", #"l", #"a", #"s", #"h", #"e",
                   #"s", #" ", #"w", #"i", #"t", #"h", #" ", #"a", #"l", #"i",
                   #"a", #"s", #":", #" "] @
                  String.explode name)))
      | SOME _ =>
        PromelaUtils.err
          (String.implode
            ([#"D", #"u", #"p", #"l", #"i", #"c", #"a", #"t", #"e", #" ", #"v",
               #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" "] @
              String.explode name)));

fun ppDeclProcArg x = liftDecl ppProcArg false x;

fun ppModule (cvm, inl)
  (PromelaAST.ProcType (act, name, args, prio, prov, steps)) =
  let
    val _ =
      (case prio of NONE => ()
        | SOME _ =>
          PromelaUtils.warn "Priorities for procs not supported. Ignored.");
    val _ =
      (case prov of NONE => ()
        | SOME _ =>
          PromelaUtils.warn "Priov (??) for procs not supported. Ignored.");
    val (cvma, argsa) = cvm_fold ppDeclProcArg cvm args;
    val (a, b) = cvm_fold ppStep (true, ([], (inl, cvma))) steps;
  in
    let
      val (_, (vars, (_, _))) = a;
    in
      (fn stepsa =>
        (cvm, (inl, Sum_Type.Inr
                      (Sum_Type.Inl
                        (ProcType
                          (act, name, List.concat argsa, vars, stepsa))))))
    end
      b
  end
  | ppModule (cvm, inl) (PromelaAST.Init (prio, steps)) =
    let
      val _ =
        (case prio of NONE => ()
          | SOME _ =>
            PromelaUtils.warn "Priorities for procs not supported. Ignored.");
      val (a, b) = cvm_fold ppStep (true, ([], (inl, cvm))) steps;
    in
      let
        val (_, (vars, (_, _))) = a;
      in
        (fn stepsa =>
          (cvm, (inl, Sum_Type.Inr (Sum_Type.Inl (Init (vars, stepsa))))))
      end
        b
    end
  | ppModule (cvm, inl) (PromelaAST.Ltl (name, formula)) =
    (cvm, (inl, Sum_Type.Inr (Sum_Type.Inr (name, formula))))
  | ppModule (cvm, inl) (PromelaAST.ModuDecl decl) =
    Product_Type.apsnd (fn ds => (inl, Sum_Type.Inl ds)) (ppDecl true cvm decl)
  | ppModule (cvm, inl) (PromelaAST.MType mtys) =
    let
      val (c, (v, (m, a))) = cvm;
      val num =
        IntInf.+ (Arith.integer_of_nat
                    (ListMapImpl.g_size_lm_basic_ops m), (1 : IntInf.int));
      val (ma, _) =
        List.foldr
          (fn mty => fn (ma, numa) =>
            let
              val mb = Assoc_List.update Stringa.equal_literal mty numa ma;
            in
              (mb, IntInf.+ (numa, (1 : IntInf.int)))
            end)
          mtys (m, num);
    in
      ((c, (v, (ma, a))), (inl, Sum_Type.Inl []))
    end
  | ppModule (cvm, inl) (PromelaAST.Inline (name, args, steps)) =
    let
      val stepF =
        (fn cvma =>
          let
            val (a, b) = cvm_fold ppStep (false, ([], (inl, cvma))) steps;
          in
            let
              val (_, (_, (_, aa))) = a;
            in
              (fn ba => (aa, ba))
            end
              b
          end);
      val inla = Assoc_List.update Stringa.equal_literal name (args, stepF) inl;
    in
      (cvm, (inla, Sum_Type.Inl []))
    end
  | ppModule cvm (PromelaAST.DProcType (uu, uv, uw, ux, uy, uz)) =
    PromelaUtils.usc "DProcType"
  | ppModule cvm (PromelaAST.Never va) = PromelaUtils.usc "Never"
  | ppModule cvm (PromelaAST.Trace vb) = PromelaUtils.usc "Trace"
  | ppModule cvm (PromelaAST.NoTrace vc) = PromelaUtils.usc "NoTrace"
  | ppModule cvm (PromelaAST.TypeDef (vd, ve)) = PromelaUtils.usc "TypeDef";

fun preprocess ms =
  let
    val dflt_vars =
      [("_pid", (NONE, false)), ("__assert__", (NONE, true)),
        ("_", (NONE, true))];
    val cvm =
      (Assoc_List.empty,
        (ListMapImpl.g_list_to_map_lm_basic_ops Stringa.equal_literal dflt_vars,
          (Assoc_List.empty, Assoc_List.empty)));
    val (_, (_, pr)) =
      List.foldl
        (fn (cvma, (inl, (vs, (ps, ls)))) => fn m =>
          (case ppModule (cvma, inl) m
            of (cvmb, (inla, Sum_Type.Inl v)) =>
              (cvmb, (inla, (vs @ v, (ps, ls))))
            | (cvmb, (inla, Sum_Type.Inr (Sum_Type.Inl p))) =>
              (cvmb, (inla, (vs, (ps @ [p], ls))))
            | (cvmb, (inla, Sum_Type.Inr (Sum_Type.Inr l))) =>
              (cvmb, (inla, (vs, (ps, ls @ [l]))))))
        (cvm, (Assoc_List.empty, ([], ([], [])))) ms;
  in
    pr
  end;

fun printEdges f es =
  List.maps
    (fn n => List.map (printEdge f n) (Product_Type.snd (IArray.sub es n)))
    (List.rev (List.upt Arith.zero_nat (IArray.length es)));

fun printLabels f ls =
  ListMapImpl.iteratei_map_op_list_it_lm_ops ls (fn _ => true)
    (fn (k, l) =>
      (fn a =>
        ([#"L", #"a", #"b", #"e", #"l", #" "] @
          String.explode k @ [#":", #" "] @ f (Arith.integer_of_nat l)) ::
          a))
    [];

fun printProcesses f prog =
  ListMapImpl.iteratei_map_op_list_it_lm_ops (proc_data prog) (fn _ => true)
    (fn (k, idx) => fn res =>
      let
        val (_, (start, (_, _))) = IArray.sub (processes prog) idx;
      in
        [] :: ([#"P", #"r", #"o", #"c", #"e", #"s", #"s", #" "] @
                String.explode k) ::
                [] :: printEdges f (IArray.sub (states prog) idx) @
                        [[#"S", #"T", #"A", #"R", #"T", #" ", #"-", #"-", #"-",
                           #">", #" "] @
                           printIndex f start,
                          []] @
                          printLabels f (IArray.sub (labels prog) idx) @ res
      end)
    [];

end; (*struct Promela*)
