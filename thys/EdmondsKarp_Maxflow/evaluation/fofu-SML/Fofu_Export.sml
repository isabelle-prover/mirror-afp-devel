
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


    structure stat = struct
      val outer_c = ref 0;
      fun outer_c_incr () = (outer_c := !outer_c + 1; ())
      val inner_c = ref 0;
      fun inner_c_incr () = (inner_c := !inner_c + 1; ())
    end
    

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





    fun array_blit src si dst di len = 
      ArraySlice.copy {
        di=di,
        src = ArraySlice.slice (src,si,SOME len),
        dst=dst}

    fun array_nth_oo v a i () = Array.sub(a,i) handle Subscript => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,i,x); a) handle Subscript => f ()

    


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
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)

structure Fofu : sig
  datatype int = Int_of_integer of IntInf.int
  val integer_of_int : int -> IntInf.int
  type nat
  val integer_of_nat : nat -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  val prepareNet :
    (nat * (nat * int)) list ->
      nat -> nat -> ((nat * nat -> int) * ((nat -> nat list) * nat)) option
  val edka_imp_tabulate :
    (nat * nat -> int) ->
      nat -> (nat -> nat list) -> (unit -> (int array * (nat list) array))
  val edka_imp_run :
    nat -> nat -> nat -> int array -> (nat list) array -> (unit -> (int array))
  val edka_imp :
    (nat * nat -> int) ->
      nat -> nat -> nat -> (nat -> nat list) -> (unit -> (int array))
  val edmonds_karp :
    (nat * (nat * int)) list ->
      nat ->
        nat ->
          (unit ->
            (((nat * nat -> int) *
               ((nat -> nat list) * (nat * int array))) option))
  val compute_flow_val_imp :
    (nat * nat -> int) ->
      nat -> nat -> (nat -> nat list) -> int array -> (unit -> int)
  val edmonds_karp_val :
    (nat * (nat * int)) list -> nat -> nat -> (unit -> (int option))
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

datatype typerepa = Typerep of string * typerepa list;

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a itself = Type;

fun typerep_inta t = Typerep ("Int.int", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_int = {} : int countable;

val typerep_int = {typerep = typerep_inta} : int typerep;

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} :
  int heap;

fun times_inta k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_int = {times = times_inta} : int times;

val dvd_int = {times_dvd = times_int} : int dvd;

fun uminus_inta k = Int_of_integer (IntInf.~ (integer_of_int k));

val zero_inta : int = Int_of_integer (0 : IntInf.int);

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun abs_inta i = (if less_int i zero_inta then uminus_inta i else i);

type 'a abs = {abs : 'a -> 'a};
val abs = #abs : 'a abs -> 'a -> 'a;

val abs_int = {abs = abs_inta} : int abs;

val one_inta : int = Int_of_integer (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

fun sgn_inta i =
  (if equal_inta i zero_inta then zero_inta
    else (if less_int zero_inta i then Int_of_integer (1 : IntInf.int)
           else uminus_inta (Int_of_integer (1 : IntInf.int))));

type 'a sgn = {sgn : 'a -> 'a};
val sgn = #sgn : 'a sgn -> 'a -> 'a;

val sgn_int = {sgn = sgn_inta} : int sgn;

fun minus_inta k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

fun plus_inta k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a comm_semiring_1_cancel_crossproduct =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
     'a comm_semiring_1_cancel};
val comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
  #comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
  'a comm_semiring_1_cancel_crossproduct -> 'a comm_semiring_1_cancel;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors
  : 'a semiring_no_zero_divisors -> 'a semiring_0;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};
val semiring_1_semiring_1_no_zero_divisors =
  #semiring_1_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_1;
val semiring_no_zero_divisors_semiring_1_no_zero_divisors =
  #semiring_no_zero_divisors_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_no_zero_divisors;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
  #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
  'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add,
    minus_group_add : 'a minus, monoid_add_group_add : 'a monoid_add,
    uminus_group_add : 'a uminus};
val cancel_semigroup_add_group_add = #cancel_semigroup_add_group_add :
  'a group_add -> 'a cancel_semigroup_add;
val minus_group_add = #minus_group_add : 'a group_add -> 'a minus;
val monoid_add_group_add = #monoid_add_group_add :
  'a group_add -> 'a monoid_add;
val uminus_group_add = #uminus_group_add : 'a group_add -> 'a uminus;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add,
    group_add_ab_group_add : 'a group_add};
val cancel_comm_monoid_add_ab_group_add = #cancel_comm_monoid_add_ab_group_add :
  'a ab_group_add -> 'a cancel_comm_monoid_add;
val group_add_ab_group_add = #group_add_ab_group_add :
  'a ab_group_add -> 'a group_add;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add,
    semiring_0_cancel_ring : 'a semiring_0_cancel};
val ab_group_add_ring = #ab_group_add_ring : 'a ring -> 'a ab_group_add;
val semiring_0_cancel_ring = #semiring_0_cancel_ring :
  'a ring -> 'a semiring_0_cancel;

type 'a ring_no_zero_divisors =
  {ring_ring_no_zero_divisors : 'a ring,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
      'a semiring_no_zero_divisors_cancel};
val ring_ring_no_zero_divisors = #ring_ring_no_zero_divisors :
  'a ring_no_zero_divisors -> 'a ring;
val semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
  #semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
  'a ring_no_zero_divisors -> 'a semiring_no_zero_divisors_cancel;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add, numeral_neg_numeral : 'a numeral};
val group_add_neg_numeral = #group_add_neg_numeral :
  'a neg_numeral -> 'a group_add;
val numeral_neg_numeral = #numeral_neg_numeral : 'a neg_numeral -> 'a numeral;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral, ring_ring_1 : 'a ring,
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};
val neg_numeral_ring_1 = #neg_numeral_ring_1 : 'a ring_1 -> 'a neg_numeral;
val ring_ring_1 = #ring_ring_1 : 'a ring_1 -> 'a ring;
val semiring_1_cancel_ring_1 = #semiring_1_cancel_ring_1 :
  'a ring_1 -> 'a semiring_1_cancel;

type 'a ring_1_no_zero_divisors =
  {ring_1_ring_1_no_zero_divisors : 'a ring_1,
    ring_no_zero_divisors_ring_1_no_zero_divisors : 'a ring_no_zero_divisors,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
      'a semiring_1_no_zero_divisors};
val ring_1_ring_1_no_zero_divisors = #ring_1_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a ring_1;
val ring_no_zero_divisors_ring_1_no_zero_divisors =
  #ring_no_zero_divisors_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a ring_no_zero_divisors;
val semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
  #semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a semiring_1_no_zero_divisors;

type 'a comm_ring =
  {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel,
    ring_comm_ring : 'a ring};
val comm_semiring_0_cancel_comm_ring = #comm_semiring_0_cancel_comm_ring :
  'a comm_ring -> 'a comm_semiring_0_cancel;
val ring_comm_ring = #ring_comm_ring : 'a comm_ring -> 'a ring;

type 'a comm_ring_1 =
  {comm_ring_comm_ring_1 : 'a comm_ring,
    comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel,
    ring_1_comm_ring_1 : 'a ring_1};
val comm_ring_comm_ring_1 = #comm_ring_comm_ring_1 :
  'a comm_ring_1 -> 'a comm_ring;
val comm_semiring_1_cancel_comm_ring_1 = #comm_semiring_1_cancel_comm_ring_1 :
  'a comm_ring_1 -> 'a comm_semiring_1_cancel;
val ring_1_comm_ring_1 = #ring_1_comm_ring_1 : 'a comm_ring_1 -> 'a ring_1;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel,
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;

type 'a idom =
  {comm_ring_1_idom : 'a comm_ring_1,
    ring_1_no_zero_divisors_idom : 'a ring_1_no_zero_divisors,
    semidom_idom : 'a semidom,
    comm_semiring_1_cancel_crossproduct_idom :
      'a comm_semiring_1_cancel_crossproduct};
val comm_ring_1_idom = #comm_ring_1_idom : 'a idom -> 'a comm_ring_1;
val ring_1_no_zero_divisors_idom = #ring_1_no_zero_divisors_idom :
  'a idom -> 'a ring_1_no_zero_divisors;
val semidom_idom = #semidom_idom : 'a idom -> 'a semidom;
val comm_semiring_1_cancel_crossproduct_idom =
  #comm_semiring_1_cancel_crossproduct_idom :
  'a idom -> 'a comm_semiring_1_cancel_crossproduct;

val plus_int = {plus = plus_inta} : int plus;

val semigroup_add_int = {plus_semigroup_add = plus_int} : int semigroup_add;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  int cancel_semigroup_add;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : int ab_semigroup_add;

val minus_int = {minus = minus_inta} : int minus;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int,
    minus_cancel_ab_semigroup_add = minus_int}
  : int cancel_ab_semigroup_add;

val zero_int = {zero = zero_inta} : int zero;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  int monoid_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : int comm_monoid_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : int cancel_comm_monoid_add;

val mult_zero_int = {times_mult_zero = times_int, zero_mult_zero = zero_int} :
  int mult_zero;

val semigroup_mult_int = {times_semigroup_mult = times_int} :
  int semigroup_mult;

val semiring_int =
  {ab_semigroup_add_semiring = ab_semigroup_add_int,
    semigroup_mult_semiring = semigroup_mult_int}
  : int semiring;

val semiring_0_int =
  {comm_monoid_add_semiring_0 = comm_monoid_add_int,
    mult_zero_semiring_0 = mult_zero_int, semiring_semiring_0 = semiring_int}
  : int semiring_0;

val semiring_0_cancel_int =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int,
    semiring_0_semiring_0_cancel = semiring_0_int}
  : int semiring_0_cancel;

val ab_semigroup_mult_int =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
  int ab_semigroup_mult;

val comm_semiring_int =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int,
    semiring_comm_semiring = semiring_int}
  : int comm_semiring;

val comm_semiring_0_int =
  {comm_semiring_comm_semiring_0 = comm_semiring_int,
    semiring_0_comm_semiring_0 = semiring_0_int}
  : int comm_semiring_0;

val comm_semiring_0_cancel_int =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
  : int comm_semiring_0_cancel;

val power_int = {one_power = one_int, times_power = times_int} : int power;

val monoid_mult_int =
  {semigroup_mult_monoid_mult = semigroup_mult_int,
    power_monoid_mult = power_int}
  : int monoid_mult;

val numeral_int =
  {one_numeral = one_int, semigroup_add_numeral = semigroup_add_int} :
  int numeral;

val semiring_numeral_int =
  {monoid_mult_semiring_numeral = monoid_mult_int,
    numeral_semiring_numeral = numeral_int,
    semiring_semiring_numeral = semiring_int}
  : int semiring_numeral;

val zero_neq_one_int =
  {one_zero_neq_one = one_int, zero_zero_neq_one = zero_int} : int zero_neq_one;

val semiring_1_int =
  {semiring_numeral_semiring_1 = semiring_numeral_int,
    semiring_0_semiring_1 = semiring_0_int,
    zero_neq_one_semiring_1 = zero_neq_one_int}
  : int semiring_1;

val semiring_1_cancel_int =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int,
    semiring_1_semiring_1_cancel = semiring_1_int}
  : int semiring_1_cancel;

val comm_monoid_mult_int =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int,
    monoid_mult_comm_monoid_mult = monoid_mult_int,
    dvd_comm_monoid_mult = dvd_int}
  : int comm_monoid_mult;

val comm_semiring_1_int =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_int,
    semiring_1_comm_semiring_1 = semiring_1_int}
  : int comm_semiring_1;

val comm_semiring_1_cancel_int =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
  : int comm_semiring_1_cancel;

val comm_semiring_1_cancel_crossproduct_int =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
     comm_semiring_1_cancel_int}
  : int comm_semiring_1_cancel_crossproduct;

val semiring_no_zero_divisors_int =
  {semiring_0_semiring_no_zero_divisors = semiring_0_int} :
  int semiring_no_zero_divisors;

val semiring_1_no_zero_divisors_int =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_int,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_int}
  : int semiring_1_no_zero_divisors;

val semiring_no_zero_divisors_cancel_int =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_int}
  : int semiring_no_zero_divisors_cancel;

val uminus_int = {uminus = uminus_inta} : int uminus;

val group_add_int =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_int,
    minus_group_add = minus_int, monoid_add_group_add = monoid_add_int,
    uminus_group_add = uminus_int}
  : int group_add;

val ab_group_add_int =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int,
    group_add_ab_group_add = group_add_int}
  : int ab_group_add;

val ring_int =
  {ab_group_add_ring = ab_group_add_int,
    semiring_0_cancel_ring = semiring_0_cancel_int}
  : int ring;

val ring_no_zero_divisors_int =
  {ring_ring_no_zero_divisors = ring_int,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
      semiring_no_zero_divisors_cancel_int}
  : int ring_no_zero_divisors;

val neg_numeral_int =
  {group_add_neg_numeral = group_add_int, numeral_neg_numeral = numeral_int} :
  int neg_numeral;

val ring_1_int =
  {neg_numeral_ring_1 = neg_numeral_int, ring_ring_1 = ring_int,
    semiring_1_cancel_ring_1 = semiring_1_cancel_int}
  : int ring_1;

val ring_1_no_zero_divisors_int =
  {ring_1_ring_1_no_zero_divisors = ring_1_int,
    ring_no_zero_divisors_ring_1_no_zero_divisors = ring_no_zero_divisors_int,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
      semiring_1_no_zero_divisors_int}
  : int ring_1_no_zero_divisors;

val comm_ring_int =
  {comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_int,
    ring_comm_ring = ring_int}
  : int comm_ring;

val comm_ring_1_int =
  {comm_ring_comm_ring_1 = comm_ring_int,
    comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_int,
    ring_1_comm_ring_1 = ring_1_int}
  : int comm_ring_1;

val semidom_int =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int}
  : int semidom;

val idom_int =
  {comm_ring_1_idom = comm_ring_1_int,
    ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_int,
    semidom_idom = semidom_int,
    comm_semiring_1_cancel_crossproduct_idom =
      comm_semiring_1_cancel_crossproduct_int}
  : int idom;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

type 'a abs_if =
  {abs_abs_if : 'a abs, minus_abs_if : 'a minus, uminus_abs_if : 'a uminus,
    zero_abs_if : 'a zero, ord_abs_if : 'a ord};
val abs_abs_if = #abs_abs_if : 'a abs_if -> 'a abs;
val minus_abs_if = #minus_abs_if : 'a abs_if -> 'a minus;
val uminus_abs_if = #uminus_abs_if : 'a abs_if -> 'a uminus;
val zero_abs_if = #zero_abs_if : 'a abs_if -> 'a zero;
val ord_abs_if = #ord_abs_if : 'a abs_if -> 'a ord;

val ord_int = {less_eq = less_eq_int, less = less_int} : int ord;

val abs_if_int =
  {abs_abs_if = abs_int, minus_abs_if = minus_int, uminus_abs_if = uminus_int,
    zero_abs_if = zero_int, ord_abs_if = ord_int}
  : int abs_if;

type 'a semiring_char_0 = {semiring_1_semiring_char_0 : 'a semiring_1};
val semiring_1_semiring_char_0 = #semiring_1_semiring_char_0 :
  'a semiring_char_0 -> 'a semiring_1;

type 'a ring_char_0 =
  {semiring_char_0_ring_char_0 : 'a semiring_char_0,
    ring_1_ring_char_0 : 'a ring_1};
val semiring_char_0_ring_char_0 = #semiring_char_0_ring_char_0 :
  'a ring_char_0 -> 'a semiring_char_0;
val ring_1_ring_char_0 = #ring_1_ring_char_0 : 'a ring_char_0 -> 'a ring_1;

val semiring_char_0_int = {semiring_1_semiring_char_0 = semiring_1_int} :
  int semiring_char_0;

val ring_char_0_int =
  {semiring_char_0_ring_char_0 = semiring_char_0_int,
    ring_1_ring_char_0 = ring_1_int}
  : int ring_char_0;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : int preorder;

val order_int = {preorder_order = preorder_int} : int order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : int linorder;

type 'a idom_abs_sgn =
  {abs_idom_abs_sgn : 'a abs, sgn_idom_abs_sgn : 'a sgn,
    idom_idom_abs_sgn : 'a idom};
val abs_idom_abs_sgn = #abs_idom_abs_sgn : 'a idom_abs_sgn -> 'a abs;
val sgn_idom_abs_sgn = #sgn_idom_abs_sgn : 'a idom_abs_sgn -> 'a sgn;
val idom_idom_abs_sgn = #idom_idom_abs_sgn : 'a idom_abs_sgn -> 'a idom;

val idom_abs_sgn_int =
  {abs_idom_abs_sgn = abs_int, sgn_idom_abs_sgn = sgn_int,
    idom_idom_abs_sgn = idom_int}
  : int idom_abs_sgn;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add,
    order_ordered_ab_semigroup_add : 'a order};
val ab_semigroup_add_ordered_ab_semigroup_add =
  #ab_semigroup_add_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a ab_semigroup_add;
val order_ordered_ab_semigroup_add = #order_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a order;

type 'a ordered_comm_monoid_add =
  {comm_monoid_add_ordered_comm_monoid_add : 'a comm_monoid_add,
    ordered_ab_semigroup_add_ordered_comm_monoid_add :
      'a ordered_ab_semigroup_add};
val comm_monoid_add_ordered_comm_monoid_add =
  #comm_monoid_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a comm_monoid_add;
val ordered_ab_semigroup_add_ordered_comm_monoid_add =
  #ordered_ab_semigroup_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_semiring =
  {ordered_comm_monoid_add_ordered_semiring : 'a ordered_comm_monoid_add,
    semiring_ordered_semiring : 'a semiring};
val ordered_comm_monoid_add_ordered_semiring =
  #ordered_comm_monoid_add_ordered_semiring :
  'a ordered_semiring -> 'a ordered_comm_monoid_add;
val semiring_ordered_semiring = #semiring_ordered_semiring :
  'a ordered_semiring -> 'a semiring;

type 'a ordered_semiring_0 =
  {ordered_semiring_ordered_semiring_0 : 'a ordered_semiring,
    semiring_0_ordered_semiring_0 : 'a semiring_0};
val ordered_semiring_ordered_semiring_0 = #ordered_semiring_ordered_semiring_0 :
  'a ordered_semiring_0 -> 'a ordered_semiring;
val semiring_0_ordered_semiring_0 = #semiring_0_ordered_semiring_0 :
  'a ordered_semiring_0 -> 'a semiring_0;

type 'a ordered_cancel_semiring =
  {ordered_semiring_0_ordered_cancel_semiring : 'a ordered_semiring_0,
    semiring_0_cancel_ordered_cancel_semiring : 'a semiring_0_cancel};
val ordered_semiring_0_ordered_cancel_semiring =
  #ordered_semiring_0_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a ordered_semiring_0;
val semiring_0_cancel_ordered_cancel_semiring =
  #semiring_0_cancel_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a semiring_0_cancel;

type 'a strict_ordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add};
val ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
  'a strict_ordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_ab_semigroup_add =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
     'a cancel_ab_semigroup_add,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
      'a strict_ordered_ab_semigroup_add};
val cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a cancel_ab_semigroup_add;
val strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_ab_semigroup_add_imp_le =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
     'a ordered_cancel_ab_semigroup_add};
val ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
  #ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
  'a ordered_ab_semigroup_add_imp_le -> 'a ordered_cancel_ab_semigroup_add;

type 'a strict_ordered_comm_monoid_add =
  {comm_monoid_add_strict_ordered_comm_monoid_add : 'a comm_monoid_add,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
      'a strict_ordered_ab_semigroup_add};
val comm_monoid_add_strict_ordered_comm_monoid_add =
  #comm_monoid_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a comm_monoid_add;
val strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
  #strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_cancel_comm_monoid_add =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
     'a ordered_cancel_ab_semigroup_add,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a ordered_comm_monoid_add,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a strict_ordered_comm_monoid_add};
val ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
  #ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_cancel_ab_semigroup_add;
val ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_comm_monoid_add;
val strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a strict_ordered_comm_monoid_add;

type 'a ordered_ab_semigroup_monoid_add_imp_le =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
     'a cancel_comm_monoid_add,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_ab_semigroup_add_imp_le,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_cancel_comm_monoid_add};
val cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le -> 'a cancel_comm_monoid_add;
val ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_ab_semigroup_add_imp_le;
val ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_cancel_comm_monoid_add;

type 'a ordered_ab_group_add =
  {ab_group_add_ordered_ab_group_add : 'a ab_group_add,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
      'a ordered_ab_semigroup_monoid_add_imp_le};
val ab_group_add_ordered_ab_group_add = #ab_group_add_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ab_group_add;
val ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
  #ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ordered_ab_semigroup_monoid_add_imp_le;

type 'a ordered_ring =
  {ordered_ab_group_add_ordered_ring : 'a ordered_ab_group_add,
    ordered_cancel_semiring_ordered_ring : 'a ordered_cancel_semiring,
    ring_ordered_ring : 'a ring};
val ordered_ab_group_add_ordered_ring = #ordered_ab_group_add_ordered_ring :
  'a ordered_ring -> 'a ordered_ab_group_add;
val ordered_cancel_semiring_ordered_ring = #ordered_cancel_semiring_ordered_ring
  : 'a ordered_ring -> 'a ordered_cancel_semiring;
val ring_ordered_ring = #ring_ordered_ring : 'a ordered_ring -> 'a ring;

val ordered_ab_semigroup_add_int =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_int,
    order_ordered_ab_semigroup_add = order_int}
  : int ordered_ab_semigroup_add;

val ordered_comm_monoid_add_int =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_int,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_int}
  : int ordered_comm_monoid_add;

val ordered_semiring_int =
  {ordered_comm_monoid_add_ordered_semiring = ordered_comm_monoid_add_int,
    semiring_ordered_semiring = semiring_int}
  : int ordered_semiring;

val ordered_semiring_0_int =
  {ordered_semiring_ordered_semiring_0 = ordered_semiring_int,
    semiring_0_ordered_semiring_0 = semiring_0_int}
  : int ordered_semiring_0;

val ordered_cancel_semiring_int =
  {ordered_semiring_0_ordered_cancel_semiring = ordered_semiring_0_int,
    semiring_0_cancel_ordered_cancel_semiring = semiring_0_cancel_int}
  : int ordered_cancel_semiring;

val strict_ordered_ab_semigroup_add_int =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
     ordered_ab_semigroup_add_int}
  : int strict_ordered_ab_semigroup_add;

val ordered_cancel_ab_semigroup_add_int =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
     cancel_ab_semigroup_add_int,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
      strict_ordered_ab_semigroup_add_int}
  : int ordered_cancel_ab_semigroup_add;

val ordered_ab_semigroup_add_imp_le_int =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
     ordered_cancel_ab_semigroup_add_int}
  : int ordered_ab_semigroup_add_imp_le;

val strict_ordered_comm_monoid_add_int =
  {comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_int,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
      strict_ordered_ab_semigroup_add_int}
  : int strict_ordered_comm_monoid_add;

val ordered_cancel_comm_monoid_add_int =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
     ordered_cancel_ab_semigroup_add_int,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      ordered_comm_monoid_add_int,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      strict_ordered_comm_monoid_add_int}
  : int ordered_cancel_comm_monoid_add;

val ordered_ab_semigroup_monoid_add_imp_le_int =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
     cancel_comm_monoid_add_int,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_ab_semigroup_add_imp_le_int,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_cancel_comm_monoid_add_int}
  : int ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_group_add_int =
  {ab_group_add_ordered_ab_group_add = ab_group_add_int,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
      ordered_ab_semigroup_monoid_add_imp_le_int}
  : int ordered_ab_group_add;

val ordered_ring_int =
  {ordered_ab_group_add_ordered_ring = ordered_ab_group_add_int,
    ordered_cancel_semiring_ordered_ring = ordered_cancel_semiring_int,
    ring_ordered_ring = ring_int}
  : int ordered_ring;

type 'a zero_less_one =
  {one_zero_less_one : 'a one, zero_zero_less_one : 'a zero,
    order_zero_less_one : 'a order};
val one_zero_less_one = #one_zero_less_one : 'a zero_less_one -> 'a one;
val zero_zero_less_one = #zero_zero_less_one : 'a zero_less_one -> 'a zero;
val order_zero_less_one = #order_zero_less_one : 'a zero_less_one -> 'a order;

val zero_less_one_int =
  {one_zero_less_one = one_int, zero_zero_less_one = zero_int,
    order_zero_less_one = order_int}
  : int zero_less_one;

type 'a linordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add,
    linorder_linordered_ab_semigroup_add : 'a linorder};
val ordered_ab_semigroup_add_linordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_linordered_ab_semigroup_add :
  'a linordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;
val linorder_linordered_ab_semigroup_add = #linorder_linordered_ab_semigroup_add
  : 'a linordered_ab_semigroup_add -> 'a linorder;

type 'a linordered_cancel_ab_semigroup_add =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
     'a linordered_ab_semigroup_add,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
      'a ordered_ab_semigroup_add_imp_le};
val linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
  #linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a linordered_ab_semigroup_add;
val ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
  #ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a ordered_ab_semigroup_add_imp_le;

type 'a linordered_semiring =
  {linordered_cancel_ab_semigroup_add_linordered_semiring :
     'a linordered_cancel_ab_semigroup_add,
    ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring :
      'a ordered_ab_semigroup_monoid_add_imp_le,
    ordered_cancel_semiring_linordered_semiring : 'a ordered_cancel_semiring};
val linordered_cancel_ab_semigroup_add_linordered_semiring =
  #linordered_cancel_ab_semigroup_add_linordered_semiring :
  'a linordered_semiring -> 'a linordered_cancel_ab_semigroup_add;
val ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring =
  #ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring :
  'a linordered_semiring -> 'a ordered_ab_semigroup_monoid_add_imp_le;
val ordered_cancel_semiring_linordered_semiring =
  #ordered_cancel_semiring_linordered_semiring :
  'a linordered_semiring -> 'a ordered_cancel_semiring;

type 'a linordered_semiring_strict =
  {linordered_semiring_linordered_semiring_strict : 'a linordered_semiring};
val linordered_semiring_linordered_semiring_strict =
  #linordered_semiring_linordered_semiring_strict :
  'a linordered_semiring_strict -> 'a linordered_semiring;

type 'a linordered_semiring_1 =
  {linordered_semiring_linordered_semiring_1 : 'a linordered_semiring,
    semiring_1_linordered_semiring_1 : 'a semiring_1};
val linordered_semiring_linordered_semiring_1 =
  #linordered_semiring_linordered_semiring_1 :
  'a linordered_semiring_1 -> 'a linordered_semiring;
val semiring_1_linordered_semiring_1 = #semiring_1_linordered_semiring_1 :
  'a linordered_semiring_1 -> 'a semiring_1;

type 'a linordered_semiring_1_strict =
  {linordered_semiring_1_linordered_semiring_1_strict :
     'a linordered_semiring_1,
    linordered_semiring_strict_linordered_semiring_1_strict :
      'a linordered_semiring_strict};
val linordered_semiring_1_linordered_semiring_1_strict =
  #linordered_semiring_1_linordered_semiring_1_strict :
  'a linordered_semiring_1_strict -> 'a linordered_semiring_1;
val linordered_semiring_strict_linordered_semiring_1_strict =
  #linordered_semiring_strict_linordered_semiring_1_strict :
  'a linordered_semiring_1_strict -> 'a linordered_semiring_strict;

type 'a ordered_ab_group_add_abs =
  {abs_ordered_ab_group_add_abs : 'a abs,
    ordered_ab_group_add_ordered_ab_group_add_abs : 'a ordered_ab_group_add};
val abs_ordered_ab_group_add_abs = #abs_ordered_ab_group_add_abs :
  'a ordered_ab_group_add_abs -> 'a abs;
val ordered_ab_group_add_ordered_ab_group_add_abs =
  #ordered_ab_group_add_ordered_ab_group_add_abs :
  'a ordered_ab_group_add_abs -> 'a ordered_ab_group_add;

type 'a linordered_ab_group_add =
  {linordered_cancel_ab_semigroup_add_linordered_ab_group_add :
     'a linordered_cancel_ab_semigroup_add,
    ordered_ab_group_add_linordered_ab_group_add : 'a ordered_ab_group_add};
val linordered_cancel_ab_semigroup_add_linordered_ab_group_add =
  #linordered_cancel_ab_semigroup_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a linordered_cancel_ab_semigroup_add;
val ordered_ab_group_add_linordered_ab_group_add =
  #ordered_ab_group_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a ordered_ab_group_add;

type 'a linordered_ring =
  {linordered_ab_group_add_linordered_ring : 'a linordered_ab_group_add,
    ordered_ab_group_add_abs_linordered_ring : 'a ordered_ab_group_add_abs,
    abs_if_linordered_ring : 'a abs_if,
    linordered_semiring_linordered_ring : 'a linordered_semiring,
    ordered_ring_linordered_ring : 'a ordered_ring};
val linordered_ab_group_add_linordered_ring =
  #linordered_ab_group_add_linordered_ring :
  'a linordered_ring -> 'a linordered_ab_group_add;
val ordered_ab_group_add_abs_linordered_ring =
  #ordered_ab_group_add_abs_linordered_ring :
  'a linordered_ring -> 'a ordered_ab_group_add_abs;
val abs_if_linordered_ring = #abs_if_linordered_ring :
  'a linordered_ring -> 'a abs_if;
val linordered_semiring_linordered_ring = #linordered_semiring_linordered_ring :
  'a linordered_ring -> 'a linordered_semiring;
val ordered_ring_linordered_ring = #ordered_ring_linordered_ring :
  'a linordered_ring -> 'a ordered_ring;

type 'a linordered_ring_strict =
  {linordered_ring_linordered_ring_strict : 'a linordered_ring,
    linordered_semiring_strict_linordered_ring_strict :
      'a linordered_semiring_strict,
    ring_no_zero_divisors_linordered_ring_strict : 'a ring_no_zero_divisors};
val linordered_ring_linordered_ring_strict =
  #linordered_ring_linordered_ring_strict :
  'a linordered_ring_strict -> 'a linordered_ring;
val linordered_semiring_strict_linordered_ring_strict =
  #linordered_semiring_strict_linordered_ring_strict :
  'a linordered_ring_strict -> 'a linordered_semiring_strict;
val ring_no_zero_divisors_linordered_ring_strict =
  #ring_no_zero_divisors_linordered_ring_strict :
  'a linordered_ring_strict -> 'a ring_no_zero_divisors;

type 'a ordered_comm_semiring =
  {comm_semiring_0_ordered_comm_semiring : 'a comm_semiring_0,
    ordered_semiring_ordered_comm_semiring : 'a ordered_semiring};
val comm_semiring_0_ordered_comm_semiring =
  #comm_semiring_0_ordered_comm_semiring :
  'a ordered_comm_semiring -> 'a comm_semiring_0;
val ordered_semiring_ordered_comm_semiring =
  #ordered_semiring_ordered_comm_semiring :
  'a ordered_comm_semiring -> 'a ordered_semiring;

type 'a ordered_cancel_comm_semiring =
  {comm_semiring_0_cancel_ordered_cancel_comm_semiring :
     'a comm_semiring_0_cancel,
    ordered_cancel_semiring_ordered_cancel_comm_semiring :
      'a ordered_cancel_semiring,
    ordered_comm_semiring_ordered_cancel_comm_semiring :
      'a ordered_comm_semiring};
val comm_semiring_0_cancel_ordered_cancel_comm_semiring =
  #comm_semiring_0_cancel_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a comm_semiring_0_cancel;
val ordered_cancel_semiring_ordered_cancel_comm_semiring =
  #ordered_cancel_semiring_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a ordered_cancel_semiring;
val ordered_comm_semiring_ordered_cancel_comm_semiring =
  #ordered_comm_semiring_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a ordered_comm_semiring;

type 'a linordered_comm_semiring_strict =
  {linordered_semiring_strict_linordered_comm_semiring_strict :
     'a linordered_semiring_strict,
    ordered_cancel_comm_semiring_linordered_comm_semiring_strict :
      'a ordered_cancel_comm_semiring};
val linordered_semiring_strict_linordered_comm_semiring_strict =
  #linordered_semiring_strict_linordered_comm_semiring_strict :
  'a linordered_comm_semiring_strict -> 'a linordered_semiring_strict;
val ordered_cancel_comm_semiring_linordered_comm_semiring_strict =
  #ordered_cancel_comm_semiring_linordered_comm_semiring_strict :
  'a linordered_comm_semiring_strict -> 'a ordered_cancel_comm_semiring;

type 'a linordered_nonzero_semiring =
  {linorder_linordered_nonzero_semiring : 'a linorder,
    comm_semiring_1_linordered_nonzero_semiring : 'a comm_semiring_1,
    ordered_comm_semiring_linordered_nonzero_semiring :
      'a ordered_comm_semiring,
    zero_less_one_linordered_nonzero_semiring : 'a zero_less_one};
val linorder_linordered_nonzero_semiring = #linorder_linordered_nonzero_semiring
  : 'a linordered_nonzero_semiring -> 'a linorder;
val comm_semiring_1_linordered_nonzero_semiring =
  #comm_semiring_1_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a comm_semiring_1;
val ordered_comm_semiring_linordered_nonzero_semiring =
  #ordered_comm_semiring_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a ordered_comm_semiring;
val zero_less_one_linordered_nonzero_semiring =
  #zero_less_one_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a zero_less_one;

type 'a linordered_semidom =
  {semiring_char_0_linordered_semidom : 'a semiring_char_0,
    linordered_comm_semiring_strict_linordered_semidom :
      'a linordered_comm_semiring_strict,
    linordered_nonzero_semiring_linordered_semidom :
      'a linordered_nonzero_semiring,
    semidom_linordered_semidom : 'a semidom};
val semiring_char_0_linordered_semidom = #semiring_char_0_linordered_semidom :
  'a linordered_semidom -> 'a semiring_char_0;
val linordered_comm_semiring_strict_linordered_semidom =
  #linordered_comm_semiring_strict_linordered_semidom :
  'a linordered_semidom -> 'a linordered_comm_semiring_strict;
val linordered_nonzero_semiring_linordered_semidom =
  #linordered_nonzero_semiring_linordered_semidom :
  'a linordered_semidom -> 'a linordered_nonzero_semiring;
val semidom_linordered_semidom = #semidom_linordered_semidom :
  'a linordered_semidom -> 'a semidom;

type 'a ordered_comm_ring =
  {comm_ring_ordered_comm_ring : 'a comm_ring,
    ordered_cancel_comm_semiring_ordered_comm_ring :
      'a ordered_cancel_comm_semiring,
    ordered_ring_ordered_comm_ring : 'a ordered_ring};
val comm_ring_ordered_comm_ring = #comm_ring_ordered_comm_ring :
  'a ordered_comm_ring -> 'a comm_ring;
val ordered_cancel_comm_semiring_ordered_comm_ring =
  #ordered_cancel_comm_semiring_ordered_comm_ring :
  'a ordered_comm_ring -> 'a ordered_cancel_comm_semiring;
val ordered_ring_ordered_comm_ring = #ordered_ring_ordered_comm_ring :
  'a ordered_comm_ring -> 'a ordered_ring;

type 'a ordered_ring_abs =
  {ordered_ab_group_add_abs_ordered_ring_abs : 'a ordered_ab_group_add_abs,
    ordered_ring_ordered_ring_abs : 'a ordered_ring};
val ordered_ab_group_add_abs_ordered_ring_abs =
  #ordered_ab_group_add_abs_ordered_ring_abs :
  'a ordered_ring_abs -> 'a ordered_ab_group_add_abs;
val ordered_ring_ordered_ring_abs = #ordered_ring_ordered_ring_abs :
  'a ordered_ring_abs -> 'a ordered_ring;

type 'a linordered_idom =
  {ring_char_0_linordered_idom : 'a ring_char_0,
    idom_abs_sgn_linordered_idom : 'a idom_abs_sgn,
    linordered_ring_strict_linordered_idom : 'a linordered_ring_strict,
    linordered_semidom_linordered_idom : 'a linordered_semidom,
    linordered_semiring_1_strict_linordered_idom :
      'a linordered_semiring_1_strict,
    ordered_comm_ring_linordered_idom : 'a ordered_comm_ring,
    ordered_ring_abs_linordered_idom : 'a ordered_ring_abs};
val ring_char_0_linordered_idom = #ring_char_0_linordered_idom :
  'a linordered_idom -> 'a ring_char_0;
val idom_abs_sgn_linordered_idom = #idom_abs_sgn_linordered_idom :
  'a linordered_idom -> 'a idom_abs_sgn;
val linordered_ring_strict_linordered_idom =
  #linordered_ring_strict_linordered_idom :
  'a linordered_idom -> 'a linordered_ring_strict;
val linordered_semidom_linordered_idom = #linordered_semidom_linordered_idom :
  'a linordered_idom -> 'a linordered_semidom;
val linordered_semiring_1_strict_linordered_idom =
  #linordered_semiring_1_strict_linordered_idom :
  'a linordered_idom -> 'a linordered_semiring_1_strict;
val ordered_comm_ring_linordered_idom = #ordered_comm_ring_linordered_idom :
  'a linordered_idom -> 'a ordered_comm_ring;
val ordered_ring_abs_linordered_idom = #ordered_ring_abs_linordered_idom :
  'a linordered_idom -> 'a ordered_ring_abs;

val linordered_ab_semigroup_add_int =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add =
     ordered_ab_semigroup_add_int,
    linorder_linordered_ab_semigroup_add = linorder_int}
  : int linordered_ab_semigroup_add;

val linordered_cancel_ab_semigroup_add_int =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
     linordered_ab_semigroup_add_int,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
      ordered_ab_semigroup_add_imp_le_int}
  : int linordered_cancel_ab_semigroup_add;

val linordered_semiring_int =
  {linordered_cancel_ab_semigroup_add_linordered_semiring =
     linordered_cancel_ab_semigroup_add_int,
    ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring =
      ordered_ab_semigroup_monoid_add_imp_le_int,
    ordered_cancel_semiring_linordered_semiring = ordered_cancel_semiring_int}
  : int linordered_semiring;

val linordered_semiring_strict_int =
  {linordered_semiring_linordered_semiring_strict = linordered_semiring_int} :
  int linordered_semiring_strict;

val linordered_semiring_1_int =
  {linordered_semiring_linordered_semiring_1 = linordered_semiring_int,
    semiring_1_linordered_semiring_1 = semiring_1_int}
  : int linordered_semiring_1;

val linordered_semiring_1_strict_int =
  {linordered_semiring_1_linordered_semiring_1_strict =
     linordered_semiring_1_int,
    linordered_semiring_strict_linordered_semiring_1_strict =
      linordered_semiring_strict_int}
  : int linordered_semiring_1_strict;

val ordered_ab_group_add_abs_int =
  {abs_ordered_ab_group_add_abs = abs_int,
    ordered_ab_group_add_ordered_ab_group_add_abs = ordered_ab_group_add_int}
  : int ordered_ab_group_add_abs;

val linordered_ab_group_add_int =
  {linordered_cancel_ab_semigroup_add_linordered_ab_group_add =
     linordered_cancel_ab_semigroup_add_int,
    ordered_ab_group_add_linordered_ab_group_add = ordered_ab_group_add_int}
  : int linordered_ab_group_add;

val linordered_ring_int =
  {linordered_ab_group_add_linordered_ring = linordered_ab_group_add_int,
    ordered_ab_group_add_abs_linordered_ring = ordered_ab_group_add_abs_int,
    abs_if_linordered_ring = abs_if_int,
    linordered_semiring_linordered_ring = linordered_semiring_int,
    ordered_ring_linordered_ring = ordered_ring_int}
  : int linordered_ring;

val linordered_ring_strict_int =
  {linordered_ring_linordered_ring_strict = linordered_ring_int,
    linordered_semiring_strict_linordered_ring_strict =
      linordered_semiring_strict_int,
    ring_no_zero_divisors_linordered_ring_strict = ring_no_zero_divisors_int}
  : int linordered_ring_strict;

val ordered_comm_semiring_int =
  {comm_semiring_0_ordered_comm_semiring = comm_semiring_0_int,
    ordered_semiring_ordered_comm_semiring = ordered_semiring_int}
  : int ordered_comm_semiring;

val ordered_cancel_comm_semiring_int =
  {comm_semiring_0_cancel_ordered_cancel_comm_semiring =
     comm_semiring_0_cancel_int,
    ordered_cancel_semiring_ordered_cancel_comm_semiring =
      ordered_cancel_semiring_int,
    ordered_comm_semiring_ordered_cancel_comm_semiring =
      ordered_comm_semiring_int}
  : int ordered_cancel_comm_semiring;

val linordered_comm_semiring_strict_int =
  {linordered_semiring_strict_linordered_comm_semiring_strict =
     linordered_semiring_strict_int,
    ordered_cancel_comm_semiring_linordered_comm_semiring_strict =
      ordered_cancel_comm_semiring_int}
  : int linordered_comm_semiring_strict;

val linordered_nonzero_semiring_int =
  {linorder_linordered_nonzero_semiring = linorder_int,
    comm_semiring_1_linordered_nonzero_semiring = comm_semiring_1_int,
    ordered_comm_semiring_linordered_nonzero_semiring =
      ordered_comm_semiring_int,
    zero_less_one_linordered_nonzero_semiring = zero_less_one_int}
  : int linordered_nonzero_semiring;

val linordered_semidom_int =
  {semiring_char_0_linordered_semidom = semiring_char_0_int,
    linordered_comm_semiring_strict_linordered_semidom =
      linordered_comm_semiring_strict_int,
    linordered_nonzero_semiring_linordered_semidom =
      linordered_nonzero_semiring_int,
    semidom_linordered_semidom = semidom_int}
  : int linordered_semidom;

val ordered_comm_ring_int =
  {comm_ring_ordered_comm_ring = comm_ring_int,
    ordered_cancel_comm_semiring_ordered_comm_ring =
      ordered_cancel_comm_semiring_int,
    ordered_ring_ordered_comm_ring = ordered_ring_int}
  : int ordered_comm_ring;

val ordered_ring_abs_int =
  {ordered_ab_group_add_abs_ordered_ring_abs = ordered_ab_group_add_abs_int,
    ordered_ring_ordered_ring_abs = ordered_ring_int}
  : int ordered_ring_abs;

val linordered_idom_int =
  {ring_char_0_linordered_idom = ring_char_0_int,
    idom_abs_sgn_linordered_idom = idom_abs_sgn_int,
    linordered_ring_strict_linordered_idom = linordered_ring_strict_int,
    linordered_semidom_linordered_idom = linordered_semidom_int,
    linordered_semiring_1_strict_linordered_idom =
      linordered_semiring_1_strict_int,
    ordered_comm_ring_linordered_idom = ordered_comm_ring_int,
    ordered_ring_abs_linordered_idom = ordered_ring_abs_int}
  : int linordered_idom;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

val one_nata : nat = Nat (1 : IntInf.int);

val one_nat = {one = one_nata} : nat one;

val zero_nata : nat = Nat (0 : IntInf.int);

val zero_nat = {zero = zero_nata} : nat zero;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun def_hashmap_size_nat x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun hashcode_nat n = uint32_of_int (int_of_nat n);

val hashable_nat =
  {hashcode = hashcode_nat, def_hashmap_size = def_hashmap_size_nat} :
  nat hashable;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun def_hashmap_size_prod A_ B_ =
  (fn _ => plus_nat (def_hashmap_size A_ Type) (def_hashmap_size B_ Type));

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun hashcode_prod A_ B_ x =
  Word32.+ (Word32.* (hashcode A_
                        (fst x), Word32.fromLargeInt (IntInf.toLarge (33 : IntInf.int))), hashcode
            B_ (snd x));

fun hashable_prod A_ B_ =
  {hashcode = hashcode_prod A_ B_,
    def_hashmap_size = def_hashmap_size_prod A_ B_}
  : ('a * 'b) hashable;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype 'a dres = DSUCCEEDi | DFAILi | DRETURN of 'a;

datatype ('a, 'b) hashmapa =
  HashMapa of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype ('b, 'a) hashmap = HashMap of ('b, 'a) hashmapa;

datatype ('a, 'b) hashmapb =
  HashMapb of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype ('a, 'b, 'c, 'd) gen_g_impl_ext = Gen_g_impl_ext of 'a * 'b * 'c * 'd;

datatype ('a, 'b) pre_network_ext =
  Pre_network_ext of
    ((nat * nat), 'a) hashmap * (nat, unit) hashmap *
      (nat, (nat list)) hashmap * (nat, (nat list)) hashmap *
      (nat, (nat list)) hashmap * bool * bool * 'b;

datatype ('a, 'b, 'c) simple_state_nos_impl_ext =
  Simple_state_nos_impl_ext of 'a * 'b * 'c;

fun len A_ a = (fn () => let
                           val i = (fn () => Array.length a) ();
                         in
                           nat_of_integer i
                         end);

fun new A_ = (fn a => fn b => (fn () => Array.array (a, b))) o integer_of_nat;

fun nth A_ a n = (fn () => Array.sub (a, integer_of_nat n));

fun upd A_ i x a =
  (fn () => let
              val _ = (fn () => Array.update (a, integer_of_nat i, x)) ();
            in
              a
            end);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun make A_ n f =
  (fn () => Array.tabulate (integer_of_nat n, f o nat_of_integer));

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if eq A_ (fst p) k then (k, v) :: ps else p :: update A_ k v ps);

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun hd (x21 :: x22) = x21;

fun maxa A_ (Set (x :: xs)) =
  fold (max ((ord_preorder o preorder_order o order_linorder) A_)) xs x;

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

fun ln_N el =
  plus_nat
    (maxa linorder_nat
      (sup_set equal_nat (image fst (Set el)) (image (fst o snd) (Set el))))
    one_nata;

fun pn_t_node_update A_ pn_t_nodea
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_nodea pn_t_node,
        more);

fun pn_s_node_update A_ pn_s_nodea
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_nodea pn_s_node, pn_t_node,
        more);

fun pn_adjmap_update A_ pn_adjmapa
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succ, pn_pred, pn_adjmapa pn_adjmap, pn_s_node, pn_t_node,
        more);

fun pn_succ_update A_ pn_succa
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succa pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node,
        more);

fun pn_pred_update A_ pn_preda
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succ, pn_preda pn_pred, pn_adjmap, pn_s_node, pn_t_node,
        more);

fun pn_c_update A_ pn_ca
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_ca pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node,
        more);

fun pn_V_update A_ pn_Va
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_Va pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node,
        more);

fun pn_t_node A_
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = pn_t_node;

fun pn_s_node A_
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = pn_s_node;

fun pn_adjmap A_
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = pn_adjmap;

fun new_array v = FArray.IsabelleMapping.new_array v o integer_of_nat;

fun new_hashmap_with A_ size = HashMapa (new_array [] size, zero_nata);

fun ahm_emptya A_ = (fn _ => new_hashmap_with A_ (def_hashmap_size A_ Type));

fun ahm_empty_const A_ = HashMap (ahm_emptya A_ ());

fun ahm_empty A_ = (fn _ => ahm_empty_const A_);

fun empty_ahm_basic_ops A_ = ahm_empty A_;

fun pn_succ A_
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = pn_succ;

fun pn_pred A_
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = pn_pred;

fun sgn_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else (if IntInf.< (k, (0 : IntInf.int)) then (~1 : IntInf.int)
           else (1 : IntInf.int)));

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if ((l : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => IntInf.* (a, b)) o sgn_integer) l
                  (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = (0 : IntInf.int))
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (IntInf.abs l, s)))
                         end)));

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun nat_of_hashcode x = nat_of_uint32 x;

fun bounded_hashcode_nat A_ n x =
  modulo_nat (nat_of_hashcode (hashcode A_ x)) n;

fun array_length x = (nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun array_set a = FArray.IsabelleMapping.array_set a o integer_of_nat;

fun array_get a = FArray.IsabelleMapping.array_get a o integer_of_nat;

fun is_none (SOME x) = false
  | is_none NONE = true;

fun ahm_update_aux (A1_, A2_) (HashMapa (a, n)) k v =
  let
    val h = bounded_hashcode_nat A2_ (array_length a) k;
    val m = array_get a h;
    val insert = is_none (map_of A1_ m k);
  in
    HashMapa
      (array_set a h (update A1_ k v m),
        (if insert then plus_nat n one_nata else n))
  end;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun idx_iteratei_aux_array_get sz i l c f sigma =
  (if equal_nata i zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux_array_get sz (minus_nat i one_nata) l c f
           (f (array_get l (minus_nat sz i)) sigma));

fun idx_iteratei_array_length_array_get l c f sigma =
  idx_iteratei_aux_array_get (array_length l) (array_length l) l c f sigma;

fun ahm_iteratei_aux A_ a c f sigma =
  idx_iteratei_array_length_array_get a c (fn x => foldli x c f) sigma;

fun ahm_rehash_auxa A_ n kv a = let
                                  val h = bounded_hashcode_nat A_ n (fst kv);
                                in
                                  array_set a h (kv :: array_get a h)
                                end;

fun ahm_rehash_aux A_ a sz =
  ahm_iteratei_aux A_ a (fn _ => true) (ahm_rehash_auxa A_ sz)
    (new_array [] sz);

fun ahm_rehash A_ (HashMapa (a, n)) sz = HashMapa (ahm_rehash_aux A_ a sz, n);

val load_factor : nat = nat_of_integer (75 : IntInf.int);

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun ahm_filled A_ (HashMapa (a, n)) =
  less_eq_nat (times_nat (array_length a) load_factor)
    (times_nat n (nat_of_integer (100 : IntInf.int)));

fun hm_grow A_ (HashMapa (a, n)) =
  plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) (array_length a))
    (nat_of_integer (3 : IntInf.int));

fun ahm_updatea (A1_, A2_) k v hm =
  let
    val hma = ahm_update_aux (A1_, A2_) hm k v;
  in
    (if ahm_filled A2_ hma then ahm_rehash A2_ hma (hm_grow A2_ hma) else hma)
  end;

fun impl_of B_ (HashMap x) = x;

fun ahm_update (A1_, A2_) k v hm =
  HashMap (ahm_updatea (A1_, A2_) k v (impl_of A2_ hm));

fun ins_ahm_basic_ops (A1_, A2_) x s = ahm_update (A1_, A2_) x () s;

fun pn_c A_
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = pn_c;

fun pn_V A_
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_adjmap, pn_s_node, pn_t_node, more))
  = pn_V;

fun ahm_alpha_aux (A1_, A2_) a k =
  map_of A1_ (array_get a (bounded_hashcode_nat A2_ (array_length a) k)) k;

fun ahm_alpha (A1_, A2_) (HashMapa (a, uu)) = ahm_alpha_aux (A1_, A2_) a;

fun ahm_lookupa (A1_, A2_) k hm = ahm_alpha (A1_, A2_) hm k;

fun ahm_lookup (A1_, A2_) k hm = ahm_lookupa (A1_, A2_) k (impl_of A2_ hm);

fun the_default uu (SOME x) = x
  | the_default x NONE = x;

fun ahm_ld (B1_, B2_) a ahm k = the_default a (ahm_lookup (B1_, B2_) k ahm);

fun read (A1_, A2_) [] uu uv =
  SOME (Pre_network_ext
         (ahm_empty (hashable_prod hashable_nat hashable_nat) (),
           empty_ahm_basic_ops hashable_nat (), ahm_empty hashable_nat (),
           ahm_empty hashable_nat (), ahm_empty hashable_nat (), false, false,
           ()))
  | read (A1_, A2_) ((u, (v, c)) :: es) s t =
    (case read (A1_, A2_) es s t of NONE => NONE
      | SOME x =>
        (if eq A1_
              (ahm_ld
                (equal_prod equal_nat equal_nat,
                  hashable_prod hashable_nat hashable_nat)
                (zero ((zero_abs_if o abs_if_linordered_ring o
                         linordered_ring_linordered_ring_strict o
                         linordered_ring_strict_linordered_idom)
                        A2_))
                (pn_c A2_ x) (u, v))
              (zero ((zero_abs_if o abs_if_linordered_ring o
                       linordered_ring_linordered_ring_strict o
                       linordered_ring_strict_linordered_idom)
                      A2_)) andalso
              (eq A1_
                 (ahm_ld
                   (equal_prod equal_nat equal_nat,
                     hashable_prod hashable_nat hashable_nat)
                   (zero ((zero_abs_if o abs_if_linordered_ring o
                            linordered_ring_linordered_ring_strict o
                            linordered_ring_strict_linordered_idom)
                           A2_))
                   (pn_c A2_ x) (v, u))
                 (zero ((zero_abs_if o abs_if_linordered_ring o
                          linordered_ring_linordered_ring_strict o
                          linordered_ring_strict_linordered_idom)
                         A2_)) andalso
                less ((ord_abs_if o abs_if_linordered_ring o
                        linordered_ring_linordered_ring_strict o
                        linordered_ring_strict_linordered_idom)
                       A2_)
                  (zero ((zero_abs_if o abs_if_linordered_ring o
                           linordered_ring_linordered_ring_strict o
                           linordered_ring_strict_linordered_idom)
                          A2_))
                  c)
          then (if equal_nata u v orelse (equal_nata v s orelse equal_nata u t)
                 then NONE
                 else SOME (pn_t_node_update A2_
                             (fn _ => pn_t_node A2_ x orelse equal_nata v t)
                             (pn_s_node_update A2_
                               (fn _ => pn_s_node A2_ x orelse equal_nata u s)
                               (pn_adjmap_update A2_
                                 (fn _ =>
                                   ahm_update (equal_nat, hashable_nat) u
                                     (v :: ahm_ld (equal_nat, hashable_nat) []
     (pn_adjmap A2_ x) u)
                                     (ahm_update (equal_nat, hashable_nat) v
                                       (u ::
 ahm_ld (equal_nat, hashable_nat) [] (pn_adjmap A2_ x) v)
                                       (pn_adjmap A2_ x)))
                                 (pn_pred_update A2_
                                   (fn _ =>
                                     ahm_update (equal_nat, hashable_nat) v
                                       (u ::
 ahm_ld (equal_nat, hashable_nat) [] (pn_pred A2_ x) v)
                                       (pn_pred A2_ x))
                                   (pn_succ_update A2_
                                     (fn _ =>
                                       ahm_update (equal_nat, hashable_nat) u
 (v :: ahm_ld (equal_nat, hashable_nat) [] (pn_succ A2_ x) u) (pn_succ A2_ x))
                                     (pn_V_update A2_
                                       (fn _ =>
 ins_ahm_basic_ops (equal_nat, hashable_nat) u
   (ins_ahm_basic_ops (equal_nat, hashable_nat) v (pn_V A2_ x)))
                                       (pn_c_update A2_
 (fn _ =>
   ahm_update
     (equal_prod equal_nat equal_nat, hashable_prod hashable_nat hashable_nat)
     (u, v) c (pn_c A2_ x))
 x))))))))
          else NONE));

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun gen_ball it s p = it s (fn x => x) (fn x => fn _ => p x) true;

fun the (SOME x2) = x2;

fun gen_pick it s =
  the (it s (fn a => (case a of NONE => true | SOME _ => false))
         (fn x => fn _ => SOME x)
        NONE);

fun nth_oo A_ v a = (fn b => array_nth_oo v a b) o integer_of_nat;

fun upd_oo A_ f =
  (fn a => fn b => fn c => array_upd_oo f a b c) o integer_of_nat;

fun gen_equal ss1 ss2 s1 s2 = ss1 s1 s2 andalso ss2 s2 s1;

fun rev_graph_of_impl A_ pn t =
  Gen_g_impl_ext
    ((fn _ => true), ahm_ld (equal_nat, hashable_nat) [] (pn_pred A_ pn), [t],
      ());

fun ssnos_visited_impl_update ssnos_visited_impla
  (Simple_state_nos_impl_ext (ssnos_stack_impl, ssnos_visited_impl, more)) =
  Simple_state_nos_impl_ext
    (ssnos_stack_impl, ssnos_visited_impla ssnos_visited_impl, more);

fun ssnos_stack_impl_update ssnos_stack_impla
  (Simple_state_nos_impl_ext (ssnos_stack_impl, ssnos_visited_impl, more)) =
  Simple_state_nos_impl_ext
    (ssnos_stack_impla ssnos_stack_impl, ssnos_visited_impl, more);

fun ssnos_visited_impl
  (Simple_state_nos_impl_ext (ssnos_stack_impl, ssnos_visited_impl, more)) =
  ssnos_visited_impl;

fun ssnos_stack_impl
  (Simple_state_nos_impl_ext (ssnos_stack_impl, ssnos_visited_impl, more)) =
  ssnos_stack_impl;

fun ras_singleton B_ x = (FArray.IsabelleMapping.array_of_list [x], one B_);

fun ras_is_empty s = equal_nata (snd s) zero_nata;

fun ras_empty B_ uu = (FArray.IsabelleMapping.array_of_list [], zero B_);

fun list_map_update_aux eq k v [] accu = (k, v) :: accu
  | list_map_update_aux eq k v (x :: xs) accu =
    (if eq (fst x) k then (k, v) :: xs @ accu
      else list_map_update_aux eq k v xs (x :: accu));

fun list_map_update eq k v m = list_map_update_aux eq k v m [];

fun list_map_lookup eq uu [] = NONE
  | list_map_lookup eq k (y :: ys) =
    (if eq (fst y) k then SOME (snd y) else list_map_lookup eq k ys);

fun ahm_update_auxa eq bhc (HashMapb (a, n)) k v =
  let
    val h = bhc (array_length a) k;
    val m = array_get a h;
    val insert = is_none (list_map_lookup eq k m);
  in
    HashMapb
      (array_set a h (list_map_update eq k v m),
        (if insert then plus_nat n one_nata else n))
  end;

fun idx_iteratei_aux get sz i l c f sigma =
  (if equal_nata i zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux get sz (minus_nat i one_nata) l c f
           (f (get l (minus_nat sz i)) sigma));

fun idx_iteratei get sz l c f sigma =
  idx_iteratei_aux get (sz l) (sz l) l c f sigma;

fun ahm_iteratei_auxa a c f sigma =
  idx_iteratei array_get array_length a c (fn x => foldli x c f) sigma;

fun ahm_rehash_auxc bhc n kv a = let
                                   val h = bhc n (fst kv);
                                 in
                                   array_set a h (kv :: array_get a h)
                                 end;

fun ahm_rehash_auxb bhc a sz =
  ahm_iteratei_auxa a (fn _ => true) (ahm_rehash_auxc bhc sz) (new_array [] sz);

fun ahm_rehasha bhc (HashMapb (a, n)) sz =
  HashMapb (ahm_rehash_auxb bhc a sz, n);

val load_factora : nat = nat_of_integer (75 : IntInf.int);

fun ahm_filleda (HashMapb (a, n)) =
  less_eq_nat (times_nat (array_length a) load_factora)
    (times_nat n (nat_of_integer (100 : IntInf.int)));

fun hm_growa (HashMapb (a, n)) =
  plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) (array_length a))
    (nat_of_integer (3 : IntInf.int));

fun ahm_updateb eq bhc k v hm =
  let
    val hma = ahm_update_auxa eq bhc hm k v;
  in
    (if ahm_filleda hma then ahm_rehasha bhc hma (hm_growa hma) else hma)
  end;

fun ahm_lookup_aux eq bhc k a =
  list_map_lookup eq k (array_get a (bhc (array_length a) k));

fun ahm_lookupb eq bhc k (HashMapb (a, uu)) = ahm_lookup_aux eq bhc k a;

fun array_growa a = FArray.IsabelleMapping.array_grow a o integer_of_nat;

fun ras_push x s =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if equal_nata n (array_length aa)
        then array_growa aa
               (max ord_nat (nat_of_integer (4 : IntInf.int))
                 (times_nat (nat_of_integer (2 : IntInf.int)) n))
               x
        else aa);
    val ac = array_set ab n x;
  in
    (ac, plus_nat n one_nata)
  end;

fun new_hashmap_witha size = HashMapb (new_array [] size, zero_nata);

fun ahm_emptyb def_size = new_hashmap_witha def_size;

fun gi_V0 (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_V0;

fun ras_top s = let
                  val a = s;
                  val (aa, n) = a;
                in
                  array_get aa (minus_nat n one_nata)
                end;

fun array_shrink a = FArray.IsabelleMapping.array_shrink a o integer_of_nat;

fun ras_shrink s =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if less_eq_nat (times_nat (nat_of_integer (128 : IntInf.int)) n)
            (array_length aa) andalso
            less_nat (nat_of_integer (4 : IntInf.int)) n
        then array_shrink aa n else aa);
  in
    (ab, n)
  end;

fun ras_pop s = let
                  val a = s;
                  val (aa, n) = a;
                in
                  ras_shrink (aa, minus_nat n one_nata)
                end;

fun gi_E (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_E;

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun rev_append [] ac = ac
  | rev_append (x :: xs) ac = rev_append xs (x :: ac);

fun glist_delete_aux eq x [] asa = asa
  | glist_delete_aux eq x (y :: ys) asa =
    (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y :: asa));

fun glist_delete eq x l = glist_delete_aux eq x l [];

fun map2set_insert i k s = i k () s;

fun map2set_memb l k s = (case l k s of NONE => false | SOME _ => true);

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun find_reachable_codeT eq bhc sz gi =
  let
    val a =
      let
        val a =
          let
            val a = ();
          in
            Simple_state_nos_impl_ext (ras_empty zero_nat (), ahm_emptyb sz, a)
          end;
      in
        foldli (gi_V0 gi) (fn _ => not false)
          (fn xa => fn sigma =>
            let
              val _ = sigma;
            in
              (if map2set_memb (ahm_lookupb eq bhc) xa
                    (ssnos_visited_impl sigma)
                then sigma
                else let
                       val aa =
                         let
                           val xc =
                             let
                               val xd =
                                 ssnos_stack_impl_update
                                   (fn _ =>
                                     ras_singleton one_nat (xa, gi_E gi xa))
                                   sigma;
                               val xe =
                                 ssnos_visited_impl_update
                                   (fn _ =>
                                     map2set_insert (ahm_updateb eq bhc) xa
                                       (ssnos_visited_impl xd))
                                   xd;
                             in
                               xe
                             end;
                           val _ = ();
                         in
                           xc
                         end;
                     in
                       whilea
                         (fn xd =>
                           not false andalso
                             not (ras_is_empty (ssnos_stack_impl xd)))
                         (fn xd =>
                           (case let
                                   val ab = ras_top (ssnos_stack_impl xd);
                                   val (ac, b) = ab;
                                 in
                                   (if is_Nil b then (ac, (NONE, xd))
                                     else let
    val xf = gen_pick foldli b;
    val xg = glist_delete eq xf b;
    val xh =
      ssnos_stack_impl_update
        (fn _ => ras_push (ac, xg) (ras_pop (ssnos_stack_impl xd))) xd;
  in
    (ac, (SOME xf, xh))
  end)
                                 end
                             of (_, (NONE, ba)) =>
                               let
                                 val xf =
                                   let
                                     val xg =
                                       ssnos_stack_impl_update
 (fn _ => ras_pop (ssnos_stack_impl ba)) ba;
                                   in
                                     xg
                                   end;
                                 val _ = ();
                               in
                                 xf
                               end
                             | (_, (SOME xf, ba)) =>
                               (if map2set_memb (ahm_lookupb eq bhc) xf
                                     (ssnos_visited_impl ba)
                                 then let
val xg = ba;
val _ = ();
                                      in
xg
                                      end
                                 else let
val xg =
  let
    val xh =
      ssnos_stack_impl_update
        (fn _ => ras_push (xf, gi_E gi xf) (ssnos_stack_impl ba)) ba;
    val xi =
      ssnos_visited_impl_update
        (fn _ => map2set_insert (ahm_updateb eq bhc) xf (ssnos_visited_impl xh))
        xh;
  in
    xi
  end;
val _ = ();
                                      in
xg
                                      end)))
                         aa
                     end)
            end)
          a
      end;
  in
    ssnos_visited_impl a
  end;

fun the_res (DRETURN x) = x;

fun reachable_impl gi =
  the_res
    (DRETURN
      (find_reachable_codeT equal_nata (bounded_hashcode_nat hashable_nat)
        (def_hashmap_size_nat Type) gi));

fun graph_of_impl A_ pn s =
  Gen_g_impl_ext
    ((fn _ => true), ahm_ld (equal_nat, hashable_nat) [] (pn_succ A_ pn), [s],
      ());

fun ahm_iterateia A_ (HashMapa (a, n)) = ahm_iteratei_aux A_ a;

fun ahm_iteratei A_ hm = ahm_iterateia A_ (impl_of A_ hm);

fun iteratei_bset_op_list_it_dflt_basic_ops_ahm_basic_ops A_ s =
  (fn c => fn f => ahm_iteratei A_ s c (f o fst));

fun g_ball_dflt_basic_ops_ahm_basic_ops A_ s p =
  iteratei_bset_op_list_it_dflt_basic_ops_ahm_basic_ops A_ s (fn c => c)
    (fn x => fn _ => p x) true;

fun set_iterator_image g it = (fn c => fn f => it c (fn x => f (g x)));

fun map_iterator_dom it = set_iterator_image fst it;

fun ahm_iterateib (HashMapb (a, n)) = ahm_iteratei_auxa a;

fun memb_ahm_basic_ops (A1_, A2_) x s =
  not (is_none (ahm_lookup (A1_, A2_) x s));

fun it_to_list it s = it s (fn _ => true) (fn x => fn l => l @ [x]) [];

fun gen_subseteq ball1 mem2 s1 s2 = ball1 s1 (fn x => mem2 x s2);

fun sets_eq_impl ai bi =
  gen_equal
    (gen_subseteq (g_ball_dflt_basic_ops_ahm_basic_ops hashable_nat)
      (map2set_memb
        (ahm_lookupb equal_nata (bounded_hashcode_nat hashable_nat))))
    (gen_subseteq
      (gen_ball
        (fn x =>
          foldli
            (it_to_list (map_iterator_dom o (foldli o it_to_list ahm_iterateib))
              x)))
      (memb_ahm_basic_ops (equal_nat, hashable_nat)))
    ai bi;

fun net_alpha (A1_, A2_) B_ (C1_, C2_) (ci, adjmapi) =
  (ahm_ld (A1_, A2_) (zero B_) ci, ahm_ld (C1_, C2_) [] adjmapi);

fun checkNet4 el s t =
  (if equal_nata s t then NONE
    else (case read (equal_int, linordered_idom_int) el s t of NONE => NONE
           | SOME xa =>
             (if pn_s_node linordered_idom_int xa andalso
                   pn_t_node linordered_idom_int xa
               then let
                      val xb =
                        reachable_impl (graph_of_impl linordered_idom_int xa s);
                      val xc =
                        reachable_impl
                          (rev_graph_of_impl linordered_idom_int xa t);
                    in
                      (if sets_eq_impl (pn_V linordered_idom_int xa) xb andalso
                            sets_eq_impl (pn_V linordered_idom_int xa) xc
                        then SOME (net_alpha
                                    (equal_prod equal_nat equal_nat,
                                      hashable_prod hashable_nat hashable_nat)
                                    zero_int (equal_nat, hashable_nat)
                                    (pn_c linordered_idom_int xa,
                                      pn_adjmap linordered_idom_int xa))
                        else NONE)
                    end
               else NONE)));

fun prepareNet el s t =
  bind (checkNet4 el s t) (fn (c, adjmap) => let
       val n = ln_N el;
     in
       SOME (c, (adjmap, n))
     end);

fun array_grow A_ a s x =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nata l s then (fn () => a)
        else (fn f_ => fn () => f_ ((new A_ s x) ()) ())
               (fn aa =>
                 (fn f_ => fn () => f_ ((blit A_ a zero_nata aa zero_nata l) ())
                   ())
                   (fn _ => (fn () => aa))))
        ()
    end);

val iam_initial_size : nat = nat_of_integer (8 : IntInf.int);

fun iam_new_sz A_ sz = new (heap_option A_) sz NONE;

fun iam_new A_ = iam_new_sz A_ iam_initial_size;

fun iam_update A_ k v a =
  upd_oo (heap_option A_)
    (fn () =>
      let
        val l = len (heap_option A_) a ();
      in
        let
          val newsz =
            max ord_nat (plus_nat k one_nata)
              (plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) l)
                (nat_of_integer (3 : IntInf.int)));
        in
          (fn f_ => fn () => f_ ((array_grow (heap_option A_) a newsz NONE) ())
            ())
            (upd (heap_option A_) k (SOME v))
        end
          ()
      end)
    k (SOME v) a;

fun init_state_impl srci =
  (fn () => let
              val x = iam_new heap_nat ();
              val xa = iam_update heap_nat srci srci x ();
            in
              (false, (xa, ([srci], ([], zero_nata))))
            end);

fun op_list_prepend x = (fn a => x :: a);

fun iam_lookup A_ k a = nth_oo (heap_option A_) NONE a k;

fun bfs_impl_1 si a2 x =
  (if let
        val (a1a, _) = x;
      in
        not (equal_nata a1a si)
      end
    then (fn () =>
           let
             val xa =
               let
                 val (a1a, a2a) = x;
               in
                 (fn f_ => fn () => f_ ((iam_lookup heap_nat a1a a2) ()) ())
                   (fn xa => let
                               val x_f = the xa;
                             in
                               (fn () => (x_f, op_list_prepend (x_f, a1a) a2a))
                             end)
               end
                 ();
           in
             bfs_impl_1 si a2 xa ()
           end)
    else (fn () => x));

fun is_None a = (case a of NONE => true | SOME _ => false);

fun contains_key_iam_lookup A_ k m = (fn () => let
         val r = iam_lookup A_ k m ();
       in
         not (is_None r)
       end);

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun imp_nfoldli (x :: ls) c f s =
  (fn () =>
    let
      val b = c s ();
    in
      (if b then (fn f_ => fn () => f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
        else (fn () => s))
        ()
    end)
  | imp_nfoldli [] c f s = (fn () => s);

fun bfs_impl_0 succ_impl ci ti x =
  (if let
        val (a1, (_, (a1b, (_, _)))) = x;
      in
        equal_bool a1 false andalso not (is_Nil a1b)
      end
    then (fn () =>
           let
             val xa =
               let
                 val (_, (a1a, (a1b, (a1c, a2c)))) = x;
                 val x_b = hd a1b;
                 val x_c = glist_delete equal_nata x_b a1b;
               in
                 (fn f_ => fn () => f_ ((succ_impl ci x_b) ()) ())
                   (fn x_e =>
                     (fn f_ => fn () => f_
                       ((imp_nfoldli x_e
                          (fn (a1d, (_, _)) => (fn () => (not a1d)))
                          (fn xg => fn (a1d, (a1e, a2e)) =>
                            (fn f_ => fn () => f_ (stat.inner_c_incr ()) ())
                              (fn _ =>
                                (fn f_ => fn () => f_
                                  ((contains_key_iam_lookup heap_nat xg a1e) ())
                                  ())
                                  (fn x_h =>
                                    (if x_h then (fn () => (a1d, (a1e, a2e)))
                                      else (fn f_ => fn () => f_
     ((iam_update heap_nat xg x_b a1e) ()) ())
     (fn x_i => (fn () => (equal_nata xg ti, (x_i, xg :: a2e))))))))
                          (false, (a1a, a1c)))
                       ()) ())
                       (fn (a1d, (a1e, a2e)) =>
                         (fn () =>
                           (if a1d
                             then (a1d, (a1e,
  (x_c, (a2e, plus_nat a2c one_nata))))
                             else (if is_Nil x_c
                                    then (a1d,
   (a1e, (a2e, ([], plus_nat a2c one_nata))))
                                    else (a1d, (a1e, (x_c, (a2e, a2c)))))))))
               end
                 ();
           in
             bfs_impl_0 succ_impl ci ti xa ()
           end)
    else (fn () => x));

fun bfs_impl succ_impl ci si ti =
  (if equal_nata si ti then (fn () => (SOME []))
    else (fn () =>
           let
             val x_a = init_state_impl si ();
             val x_b = bfs_impl_0 succ_impl ci ti x_a ();
           in
             (case (case x_b of (true, (a1a, (_, (_, a2c)))) => SOME (a2c, a1a)
                     | (false, (_, (_, (_, _)))) => NONE)
               of NONE => (fn () => NONE)
               | SOME (_, a2) =>
                 (fn f_ => fn () => f_ ((bfs_impl_1 si a2 (ti, [])) ()) ())
                   (fn x_e => (fn () => (SOME let
        val (_, b) = x_e;
      in
        b
      end))))
               ()
           end));

fun mtx_get A_ m mtx e = nth A_ mtx (plus_nat (times_nat (fst e) m) (snd e));

fun succ_imp_0 n cfi ui x =
  (case x of ([], a2) => (fn () => a2)
    | (x_b :: l, a2) =>
      (fn () =>
        let
          val xa = mtx_get heap_int n cfi (ui, x_b) ();
        in
          succ_imp_0 n cfi ui
            (l, (if less_int zero_inta xa then op_list_prepend x_b a2 else a2))
            ()
        end));

fun ps_get_imp A_ psi u = nth A_ psi u;

val op_list_empty : 'a list = [];

fun succ_imp n psi cfi ui =
  (fn () => let
              val x = ps_get_imp (heap_list heap_nat) psi ui ();
            in
              succ_imp_0 n cfi ui (x, op_list_empty) ()
            end);

fun bfsi n s t psi cfi = bfs_impl (fn (a, b) => succ_imp n a b) (psi, cfi) s t;

fun swap p = (snd p, fst p);

fun min A_ a b = (if less_eq A_ a b then a else b);

fun get_am am v = am v;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun mtx_new A_ n m c =
  make A_ (times_nat n m) (fn i => c (divide_nat i m, modulo_nat i m));

fun init_cf_impl c n = mtx_new heap_int n n c;

fun edka_imp_tabulate c n am =
  (fn () => let
              val x = init_cf_impl c n ();
              val x_a = make (heap_list heap_nat) n am ();
            in
              (x, x_a)
            end);

fun mtx_set A_ m mtx e v =
  upd A_ (plus_nat (times_nat (fst e) m) (snd e)) v mtx;

fun augment_imp_0 n bi x =
  (case x of ([], a2) => (fn () => a2)
    | (x_a :: l, a2) =>
      (fn () =>
        let
          val xa = mtx_get heap_int n a2 x_a ();
          val xb = mtx_set heap_int n a2 x_a (minus_inta xa bi) ();
          val x_b =
            let
              val x_d = swap x_a;
            in
              (fn f_ => fn () => f_ ((mtx_get heap_int n xb x_d) ()) ())
                (fn x_f => mtx_set heap_int n xb x_d (plus_inta x_f bi))
            end
              ();
        in
          augment_imp_0 n bi (l, x_b) ()
        end));

fun augment_imp n = (fn ai => fn bia => fn bi => augment_imp_0 n bi (bia, ai));

fun resCap_imp n cfi pi =
  (case pi of [] => (fn () => zero_inta)
    | x :: l =>
      (fn () =>
        let
          val xa = mtx_get heap_int n cfi x ();
        in
          imp_nfoldli l (fn _ => (fn () => true))
            (fn xb => fn sigma =>
              (fn f_ => fn () => f_ ((mtx_get heap_int n cfi xb) ()) ())
                (fn x_c => (fn () => (min ord_int x_c sigma))))
            xa ()
        end));

fun edka_imp_run_0 s t n f brk =
  (fn () =>
    let
      val _ = stat.outer_c_incr ();
    in
      (if let
            val (_, a) = brk;
          in
            not a
          end
        then (fn f_ => fn () => f_
               (let
                  val (a1, _) = brk;
                in
                  (fn f_ => fn () => f_ ((bfsi n s t f a1) ()) ())
                    (fn a =>
                      (case a of NONE => (fn () => (a1, true))
                        | SOME x_b =>
                          (fn f_ => fn () => f_ ((resCap_imp n a1 x_b) ()) ())
                            (fn x_c =>
                              (fn f_ => fn () => f_ ((augment_imp n a1 x_b x_c)
                                ()) ())
                                (fn x_d => (fn () => (x_d, false))))))
                end
               ()) ())
               (edka_imp_run_0 s t n f)
        else (fn () => brk))
        ()
    end);

fun edka_imp_run s t n cfi psi =
  (fn () => let
              val a = edka_imp_run_0 s t n psi (cfi, false) ();
            in
              let
                val (a1, _) = a;
              in
                (fn () => a1)
              end
                ()
            end);

fun edka_imp c s t n am = (fn () => let
                                      val a = edka_imp_tabulate c n am ();
                                    in
                                      let
val (aa, b) = a;
                                      in
edka_imp_run s t n aa b
                                      end
()
                                    end);

fun edmonds_karp el s t =
  (case prepareNet el s t of NONE => (fn () => NONE)
    | SOME (c, (am, n)) => (fn () => let
                                       val f = edka_imp c s t n am ();
                                     in
                                       SOME (c, (am, (n, f)))
                                     end));

fun compute_flow_val_imp c s n am cfi =
  imp_nfoldli (get_am am s) (fn _ => (fn () => true))
    (fn xc => fn sigma => fn () => let
                                     val x = mtx_get heap_int n cfi (s, xc) ();
                                   in
                                     plus_inta sigma (minus_inta (c (s, xc)) x)
                                   end)
    zero_inta;

fun edmonds_karp_val el s t =
  (fn () =>
    let
      val a = edmonds_karp el s t ();
    in
      (case a of NONE => (fn () => NONE)
        | SOME (c, (am, (n, cfi))) =>
          (fn f_ => fn () => f_ ((compute_flow_val_imp c s n am cfi) ()) ())
            (fn v => (fn () => (SOME v))))
        ()
    end);

end; (*struct Fofu*)
