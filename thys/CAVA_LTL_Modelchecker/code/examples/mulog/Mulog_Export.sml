
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

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

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

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()

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


    structure PromelaUtils = struct
      exception UnsupportedConstruct of string
      exception StaticError of string
      exception RuntimeError of string
      fun warn msg = TextIO.print ("Warning: " ^ msg ^ "\n")
      fun usc  c   = raise (UnsupportedConstruct c)
      fun err  e   = raise (StaticError e)
      fun abort msg _ = raise (RuntimeError msg)
    end


    structure Gerth_Statistics = struct
      val active = Unsynchronized.ref false
      val data = Unsynchronized.ref (0,0,0)

      fun is_active () = !active
      fun set_data num_states num_init num_acc = (
        active := true;
        data := (num_states, num_init, num_acc)
      )

      fun to_string () = let
        val (num_states, num_init, num_acc) = !data
      in
          "Num states: " ^ IntInf.toString (num_states) ^ "\n"
        ^ "  Num initial: " ^ IntInf.toString num_init ^ "\n"
        ^ "  Num acc-classes: " ^ IntInf.toString num_acc ^ "\n"
      end

      val _ = Statistics.register_stat ("Gerth LTL_to_GBA",is_active,to_string)
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



    structure NDFS_SI_Statistics = struct
      val active = Unsynchronized.ref false
      val cur_limit = Unsynchronized.ref 1000000
      val blue_vis = Unsynchronized.ref 0
      val blue_match = Unsynchronized.ref 0
      val red_vis = Unsynchronized.ref 0
      val time = Unsynchronized.ref Time.zeroTime

      fun is_active () = !active
      fun vis_blue () = (
            if !cur_limit < !blue_vis then (
              TextIO.print("*** " ^ IntInf.toString((!cur_limit) div 1000000) ^ "e+06 states\n");
              cur_limit := !cur_limit + 1000000)
            else ();
            blue_vis := !blue_vis + 1)
      fun match_blue () = blue_match := !blue_match + 1
      fun vis_red () = red_vis := !red_vis + 1

      fun start () = (active := true; time := Time.now ())
      fun stop () = (time := Time.- (Time.now (), !time))

      fun to_string () = let
        val t = Time.toReal (!time)
        val states_per_s = real (!blue_vis) / t
        val realStr = Real.fmt (StringCvt.FIX (SOME 2))

      in
        "Required time  : " ^ realStr t ^ "s\n"
      ^ "States per sec : " ^ realStr states_per_s ^ "\n"
      ^ "Blue states (v): " ^ IntInf.toString (!blue_vis) ^ "\n"
      ^ "Blue states (m): " ^ IntInf.toString (!blue_match) ^ "\n"
      ^ "Blue edges     : " ^ IntInf.toString (!blue_match + !blue_vis) ^ "\n"
      ^ "Red states     : " ^ IntInf.toString (!red_vis) ^ "\n"
      end
        
      val _ = Statistics.register_stat ("NDFS",is_active,to_string)
    end



    structure Gabow_Skeleton_Statistics = struct
      val active = Unsynchronized.ref false
      val num_vis = Unsynchronized.ref 0

      val time = Unsynchronized.ref Time.zeroTime

      fun is_active () = !active
      fun newnode () =
      (
        num_vis := !num_vis + 1;
        if !num_vis mod 10000 = 0 then tracing (IntInf.toString (!num_vis) ^ "\n") else ()
      )

      fun start () = (active := true; time := Time.now ())
      fun stop () = (time := Time.- (Time.now (), !time))

      fun to_string () = let
        val t = Time.toMilliseconds (!time)
        val states_per_ms = real (!num_vis) / real t
        val realStr = Real.fmt (StringCvt.FIX (SOME 2))
      in
        "Required time: " ^ IntInf.toString (t) ^ "ms\n"
      ^ "States per ms: " ^ realStr states_per_ms ^ "\n"
      ^ "# states: " ^ IntInf.toString (!num_vis) ^ "\n"
      end
        
      val _ = Statistics.register_stat ("Gabow-Skeleton",is_active,to_string)

    end


structure Mulog : sig
  type nat
  val nat_of_integer : IntInf.int -> nat
  type exp
  type 'a local_state_impl_ext
  type ('a, 'b, 'c, 'd) pid_global_config_ext
  type 'a global_state_impl_ext
  type 'a ltlc
  type char
  type config_ce
  type ('a, 'b) lasso_ext
  datatype sm_result = TY_ERR | SAT | UNSAT |
    UNSAT_CE of
      ((nat, unit local_state_impl_ext, unit global_state_impl_ext, unit)
         pid_global_config_ext,
        unit)
        lasso_ext
  type config_l2b
  type 'a proc_decl_ext
  type 'a program_ext
  val mulog_program : unit program_ext
  val lasso_reach : ('a, 'b) lasso_ext -> 'a list
  val lasso_cysfx : ('a, 'b) lasso_ext -> 'a list
  val lasso_va : ('a, 'b) lasso_ext -> 'a
  val test : 'a -> sm_result
  val show_ce :
    ((nat, unit local_state_impl_ext, unit global_state_impl_ext, unit)
       pid_global_config_ext,
      unit)
      lasso_ext ->
      string
  val program_to_promela : unit program_ext -> string
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_inta : int = Int_of_integer (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

fun times_inta k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_int = {times = times_inta} : int times;

val power_int = {one_power = one_int, times_power = times_int} : int power;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

val ord_int = {less_eq = less_eq_int, less = less_int} : int ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : int preorder;

val order_int = {preorder_order = preorder_int} : int order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : int linorder;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

val one_nata : nat = Nat (1 : IntInf.int);

val one_nat = {one = one_nata} : nat one;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

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

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nata m n =
  Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

val divide_nat = {divide = divide_nata} : nat divide;

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nata m n =
  Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

type 'a modulo =
  {divide_modulo : 'a divide, dvd_modulo : 'a dvd, modulo : 'a -> 'a -> 'a};
val divide_modulo = #divide_modulo : 'a modulo -> 'a divide;
val dvd_modulo = #dvd_modulo : 'a modulo -> 'a dvd;
val modulo = #modulo : 'a modulo -> 'a -> 'a -> 'a;

val modulo_nat =
  {divide_modulo = divide_nat, dvd_modulo = dvd_nat, modulo = modulo_nata} :
  nat modulo;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

datatype 'a itself = Type;

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

datatype 'a ltln = True_ltln | False_ltln | Prop_ltln of 'a | Nprop_ltln of 'a |
  And_ltln of 'a ltln * 'a ltln | Or_ltln of 'a ltln * 'a ltln |
  Next_ltln of 'a ltln | Until_ltln of 'a ltln * 'a ltln |
  Release_ltln of 'a ltln * 'a ltln;

fun eq A_ a b = equal A_ a b;

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
  | equal_ltlna A_ (Nprop_ltln x4) (Nprop_ltln y4) = eq A_ x4 y4
  | equal_ltlna A_ (Prop_ltln x3) (Prop_ltln y3) = eq A_ x3 y3
  | equal_ltlna A_ False_ltln False_ltln = true
  | equal_ltlna A_ True_ltln True_ltln = true;

fun equal_ltln A_ = {equal = equal_ltlna A_} : 'a ltln equal;

datatype ordera = Eq | Lt | Gt;

fun comparator_of (A1_, A2_) x y =
  (if less ((ord_preorder o preorder_order o order_linorder) A2_) x y then Lt
    else (if eq A1_ x y then Eq else Gt));

fun comparator_ltln comp_a (Release_ltln (x, xa)) (Release_ltln (yi, yj)) =
  (case comparator_ltln comp_a x yi of Eq => comparator_ltln comp_a xa yj
    | Lt => Lt | Gt => Gt)
  | comparator_ltln comp_a (Release_ltln (x, xa)) (Until_ltln (yg, yh)) = Gt
  | comparator_ltln comp_a (Release_ltln (x, xa)) (Next_ltln yf) = Gt
  | comparator_ltln comp_a (Release_ltln (x, xa)) (Or_ltln (yd, ye)) = Gt
  | comparator_ltln comp_a (Release_ltln (x, xa)) (And_ltln (yb, yc)) = Gt
  | comparator_ltln comp_a (Release_ltln (x, xa)) (Nprop_ltln ya) = Gt
  | comparator_ltln comp_a (Release_ltln (x, xa)) (Prop_ltln y) = Gt
  | comparator_ltln comp_a (Release_ltln (x, xa)) False_ltln = Gt
  | comparator_ltln comp_a (Release_ltln (x, xa)) True_ltln = Gt
  | comparator_ltln comp_a (Until_ltln (x, xa)) (Release_ltln (yi, yj)) = Lt
  | comparator_ltln comp_a (Until_ltln (x, xa)) (Until_ltln (yg, yh)) =
    (case comparator_ltln comp_a x yg of Eq => comparator_ltln comp_a xa yh
      | Lt => Lt | Gt => Gt)
  | comparator_ltln comp_a (Until_ltln (x, xa)) (Next_ltln yf) = Gt
  | comparator_ltln comp_a (Until_ltln (x, xa)) (Or_ltln (yd, ye)) = Gt
  | comparator_ltln comp_a (Until_ltln (x, xa)) (And_ltln (yb, yc)) = Gt
  | comparator_ltln comp_a (Until_ltln (x, xa)) (Nprop_ltln ya) = Gt
  | comparator_ltln comp_a (Until_ltln (x, xa)) (Prop_ltln y) = Gt
  | comparator_ltln comp_a (Until_ltln (x, xa)) False_ltln = Gt
  | comparator_ltln comp_a (Until_ltln (x, xa)) True_ltln = Gt
  | comparator_ltln comp_a (Next_ltln x) (Release_ltln (yi, yj)) = Lt
  | comparator_ltln comp_a (Next_ltln x) (Until_ltln (yg, yh)) = Lt
  | comparator_ltln comp_a (Next_ltln x) (Next_ltln yf) =
    comparator_ltln comp_a x yf
  | comparator_ltln comp_a (Next_ltln x) (Or_ltln (yd, ye)) = Gt
  | comparator_ltln comp_a (Next_ltln x) (And_ltln (yb, yc)) = Gt
  | comparator_ltln comp_a (Next_ltln x) (Nprop_ltln ya) = Gt
  | comparator_ltln comp_a (Next_ltln x) (Prop_ltln y) = Gt
  | comparator_ltln comp_a (Next_ltln x) False_ltln = Gt
  | comparator_ltln comp_a (Next_ltln x) True_ltln = Gt
  | comparator_ltln comp_a (Or_ltln (x, xa)) (Release_ltln (yi, yj)) = Lt
  | comparator_ltln comp_a (Or_ltln (x, xa)) (Until_ltln (yg, yh)) = Lt
  | comparator_ltln comp_a (Or_ltln (x, xa)) (Next_ltln yf) = Lt
  | comparator_ltln comp_a (Or_ltln (x, xa)) (Or_ltln (yd, ye)) =
    (case comparator_ltln comp_a x yd of Eq => comparator_ltln comp_a xa ye
      | Lt => Lt | Gt => Gt)
  | comparator_ltln comp_a (Or_ltln (x, xa)) (And_ltln (yb, yc)) = Gt
  | comparator_ltln comp_a (Or_ltln (x, xa)) (Nprop_ltln ya) = Gt
  | comparator_ltln comp_a (Or_ltln (x, xa)) (Prop_ltln y) = Gt
  | comparator_ltln comp_a (Or_ltln (x, xa)) False_ltln = Gt
  | comparator_ltln comp_a (Or_ltln (x, xa)) True_ltln = Gt
  | comparator_ltln comp_a (And_ltln (x, xa)) (Release_ltln (yi, yj)) = Lt
  | comparator_ltln comp_a (And_ltln (x, xa)) (Until_ltln (yg, yh)) = Lt
  | comparator_ltln comp_a (And_ltln (x, xa)) (Next_ltln yf) = Lt
  | comparator_ltln comp_a (And_ltln (x, xa)) (Or_ltln (yd, ye)) = Lt
  | comparator_ltln comp_a (And_ltln (x, xa)) (And_ltln (yb, yc)) =
    (case comparator_ltln comp_a x yb of Eq => comparator_ltln comp_a xa yc
      | Lt => Lt | Gt => Gt)
  | comparator_ltln comp_a (And_ltln (x, xa)) (Nprop_ltln ya) = Gt
  | comparator_ltln comp_a (And_ltln (x, xa)) (Prop_ltln y) = Gt
  | comparator_ltln comp_a (And_ltln (x, xa)) False_ltln = Gt
  | comparator_ltln comp_a (And_ltln (x, xa)) True_ltln = Gt
  | comparator_ltln comp_a (Nprop_ltln x) (Release_ltln (yi, yj)) = Lt
  | comparator_ltln comp_a (Nprop_ltln x) (Until_ltln (yg, yh)) = Lt
  | comparator_ltln comp_a (Nprop_ltln x) (Next_ltln yf) = Lt
  | comparator_ltln comp_a (Nprop_ltln x) (Or_ltln (yd, ye)) = Lt
  | comparator_ltln comp_a (Nprop_ltln x) (And_ltln (yb, yc)) = Lt
  | comparator_ltln comp_a (Nprop_ltln x) (Nprop_ltln ya) = comp_a x ya
  | comparator_ltln comp_a (Nprop_ltln x) (Prop_ltln y) = Gt
  | comparator_ltln comp_a (Nprop_ltln x) False_ltln = Gt
  | comparator_ltln comp_a (Nprop_ltln x) True_ltln = Gt
  | comparator_ltln comp_a (Prop_ltln x) (Release_ltln (yi, yj)) = Lt
  | comparator_ltln comp_a (Prop_ltln x) (Until_ltln (yg, yh)) = Lt
  | comparator_ltln comp_a (Prop_ltln x) (Next_ltln yf) = Lt
  | comparator_ltln comp_a (Prop_ltln x) (Or_ltln (yd, ye)) = Lt
  | comparator_ltln comp_a (Prop_ltln x) (And_ltln (yb, yc)) = Lt
  | comparator_ltln comp_a (Prop_ltln x) (Nprop_ltln ya) = Lt
  | comparator_ltln comp_a (Prop_ltln x) (Prop_ltln y) = comp_a x y
  | comparator_ltln comp_a (Prop_ltln x) False_ltln = Gt
  | comparator_ltln comp_a (Prop_ltln x) True_ltln = Gt
  | comparator_ltln comp_a False_ltln (Release_ltln (yi, yj)) = Lt
  | comparator_ltln comp_a False_ltln (Until_ltln (yg, yh)) = Lt
  | comparator_ltln comp_a False_ltln (Next_ltln yf) = Lt
  | comparator_ltln comp_a False_ltln (Or_ltln (yd, ye)) = Lt
  | comparator_ltln comp_a False_ltln (And_ltln (yb, yc)) = Lt
  | comparator_ltln comp_a False_ltln (Nprop_ltln ya) = Lt
  | comparator_ltln comp_a False_ltln (Prop_ltln y) = Lt
  | comparator_ltln comp_a False_ltln False_ltln = Eq
  | comparator_ltln comp_a False_ltln True_ltln = Gt
  | comparator_ltln comp_a True_ltln (Release_ltln (yi, yj)) = Lt
  | comparator_ltln comp_a True_ltln (Until_ltln (yg, yh)) = Lt
  | comparator_ltln comp_a True_ltln (Next_ltln yf) = Lt
  | comparator_ltln comp_a True_ltln (Or_ltln (yd, ye)) = Lt
  | comparator_ltln comp_a True_ltln (And_ltln (yb, yc)) = Lt
  | comparator_ltln comp_a True_ltln (Nprop_ltln ya) = Lt
  | comparator_ltln comp_a True_ltln (Prop_ltln y) = Lt
  | comparator_ltln comp_a True_ltln False_ltln = Lt
  | comparator_ltln comp_a True_ltln True_ltln = Eq;

fun le_of_comp acomp x y =
  (case acomp x y of Eq => true | Lt => true | Gt => false);

fun less_eq_ltln (A1_, A2_) =
  le_of_comp (comparator_ltln (comparator_of (A1_, A2_)));

fun lt_of_comp acomp x y =
  (case acomp x y of Eq => false | Lt => true | Gt => false);

fun less_ltln (A1_, A2_) =
  lt_of_comp (comparator_ltln (comparator_of (A1_, A2_)));

fun ord_ltln (A1_, A2_) =
  {less_eq = less_eq_ltln (A1_, A2_), less = less_ltln (A1_, A2_)} :
  'a ltln ord;

fun preorder_ltln (A1_, A2_) = {ord_preorder = ord_ltln (A1_, A2_)} :
  'a ltln preorder;

fun order_ltln (A1_, A2_) = {preorder_order = preorder_ltln (A1_, A2_)} :
  'a ltln order;

fun linorder_ltln (A1_, A2_) = {order_linorder = order_ltln (A1_, A2_)} :
  'a ltln linorder;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

fun equal_suma A_ B_ (Inl x1) (Inr x2) = false
  | equal_suma A_ B_ (Inr x2) (Inl x1) = false
  | equal_suma A_ B_ (Inr x2) (Inr y2) = eq B_ x2 y2
  | equal_suma A_ B_ (Inl x1) (Inl y1) = eq A_ x1 y1;

fun equal_sum A_ B_ = {equal = equal_suma A_ B_} : ('a, 'b) sum equal;

datatype bin_op = Bo_plus | Bo_minus | Bo_mul | Bo_div | Bo_mod | Bo_less |
  Bo_less_eq | Bo_eq | Bo_and | Bo_or | Bo_xor;

fun equal_bin_op Bo_or Bo_xor = false
  | equal_bin_op Bo_xor Bo_or = false
  | equal_bin_op Bo_and Bo_xor = false
  | equal_bin_op Bo_xor Bo_and = false
  | equal_bin_op Bo_and Bo_or = false
  | equal_bin_op Bo_or Bo_and = false
  | equal_bin_op Bo_eq Bo_xor = false
  | equal_bin_op Bo_xor Bo_eq = false
  | equal_bin_op Bo_eq Bo_or = false
  | equal_bin_op Bo_or Bo_eq = false
  | equal_bin_op Bo_eq Bo_and = false
  | equal_bin_op Bo_and Bo_eq = false
  | equal_bin_op Bo_less_eq Bo_xor = false
  | equal_bin_op Bo_xor Bo_less_eq = false
  | equal_bin_op Bo_less_eq Bo_or = false
  | equal_bin_op Bo_or Bo_less_eq = false
  | equal_bin_op Bo_less_eq Bo_and = false
  | equal_bin_op Bo_and Bo_less_eq = false
  | equal_bin_op Bo_less_eq Bo_eq = false
  | equal_bin_op Bo_eq Bo_less_eq = false
  | equal_bin_op Bo_less Bo_xor = false
  | equal_bin_op Bo_xor Bo_less = false
  | equal_bin_op Bo_less Bo_or = false
  | equal_bin_op Bo_or Bo_less = false
  | equal_bin_op Bo_less Bo_and = false
  | equal_bin_op Bo_and Bo_less = false
  | equal_bin_op Bo_less Bo_eq = false
  | equal_bin_op Bo_eq Bo_less = false
  | equal_bin_op Bo_less Bo_less_eq = false
  | equal_bin_op Bo_less_eq Bo_less = false
  | equal_bin_op Bo_mod Bo_xor = false
  | equal_bin_op Bo_xor Bo_mod = false
  | equal_bin_op Bo_mod Bo_or = false
  | equal_bin_op Bo_or Bo_mod = false
  | equal_bin_op Bo_mod Bo_and = false
  | equal_bin_op Bo_and Bo_mod = false
  | equal_bin_op Bo_mod Bo_eq = false
  | equal_bin_op Bo_eq Bo_mod = false
  | equal_bin_op Bo_mod Bo_less_eq = false
  | equal_bin_op Bo_less_eq Bo_mod = false
  | equal_bin_op Bo_mod Bo_less = false
  | equal_bin_op Bo_less Bo_mod = false
  | equal_bin_op Bo_div Bo_xor = false
  | equal_bin_op Bo_xor Bo_div = false
  | equal_bin_op Bo_div Bo_or = false
  | equal_bin_op Bo_or Bo_div = false
  | equal_bin_op Bo_div Bo_and = false
  | equal_bin_op Bo_and Bo_div = false
  | equal_bin_op Bo_div Bo_eq = false
  | equal_bin_op Bo_eq Bo_div = false
  | equal_bin_op Bo_div Bo_less_eq = false
  | equal_bin_op Bo_less_eq Bo_div = false
  | equal_bin_op Bo_div Bo_less = false
  | equal_bin_op Bo_less Bo_div = false
  | equal_bin_op Bo_div Bo_mod = false
  | equal_bin_op Bo_mod Bo_div = false
  | equal_bin_op Bo_mul Bo_xor = false
  | equal_bin_op Bo_xor Bo_mul = false
  | equal_bin_op Bo_mul Bo_or = false
  | equal_bin_op Bo_or Bo_mul = false
  | equal_bin_op Bo_mul Bo_and = false
  | equal_bin_op Bo_and Bo_mul = false
  | equal_bin_op Bo_mul Bo_eq = false
  | equal_bin_op Bo_eq Bo_mul = false
  | equal_bin_op Bo_mul Bo_less_eq = false
  | equal_bin_op Bo_less_eq Bo_mul = false
  | equal_bin_op Bo_mul Bo_less = false
  | equal_bin_op Bo_less Bo_mul = false
  | equal_bin_op Bo_mul Bo_mod = false
  | equal_bin_op Bo_mod Bo_mul = false
  | equal_bin_op Bo_mul Bo_div = false
  | equal_bin_op Bo_div Bo_mul = false
  | equal_bin_op Bo_minus Bo_xor = false
  | equal_bin_op Bo_xor Bo_minus = false
  | equal_bin_op Bo_minus Bo_or = false
  | equal_bin_op Bo_or Bo_minus = false
  | equal_bin_op Bo_minus Bo_and = false
  | equal_bin_op Bo_and Bo_minus = false
  | equal_bin_op Bo_minus Bo_eq = false
  | equal_bin_op Bo_eq Bo_minus = false
  | equal_bin_op Bo_minus Bo_less_eq = false
  | equal_bin_op Bo_less_eq Bo_minus = false
  | equal_bin_op Bo_minus Bo_less = false
  | equal_bin_op Bo_less Bo_minus = false
  | equal_bin_op Bo_minus Bo_mod = false
  | equal_bin_op Bo_mod Bo_minus = false
  | equal_bin_op Bo_minus Bo_div = false
  | equal_bin_op Bo_div Bo_minus = false
  | equal_bin_op Bo_minus Bo_mul = false
  | equal_bin_op Bo_mul Bo_minus = false
  | equal_bin_op Bo_plus Bo_xor = false
  | equal_bin_op Bo_xor Bo_plus = false
  | equal_bin_op Bo_plus Bo_or = false
  | equal_bin_op Bo_or Bo_plus = false
  | equal_bin_op Bo_plus Bo_and = false
  | equal_bin_op Bo_and Bo_plus = false
  | equal_bin_op Bo_plus Bo_eq = false
  | equal_bin_op Bo_eq Bo_plus = false
  | equal_bin_op Bo_plus Bo_less_eq = false
  | equal_bin_op Bo_less_eq Bo_plus = false
  | equal_bin_op Bo_plus Bo_less = false
  | equal_bin_op Bo_less Bo_plus = false
  | equal_bin_op Bo_plus Bo_mod = false
  | equal_bin_op Bo_mod Bo_plus = false
  | equal_bin_op Bo_plus Bo_div = false
  | equal_bin_op Bo_div Bo_plus = false
  | equal_bin_op Bo_plus Bo_mul = false
  | equal_bin_op Bo_mul Bo_plus = false
  | equal_bin_op Bo_plus Bo_minus = false
  | equal_bin_op Bo_minus Bo_plus = false
  | equal_bin_op Bo_xor Bo_xor = true
  | equal_bin_op Bo_or Bo_or = true
  | equal_bin_op Bo_and Bo_and = true
  | equal_bin_op Bo_eq Bo_eq = true
  | equal_bin_op Bo_less_eq Bo_less_eq = true
  | equal_bin_op Bo_less Bo_less = true
  | equal_bin_op Bo_mod Bo_mod = true
  | equal_bin_op Bo_div Bo_div = true
  | equal_bin_op Bo_mul Bo_mul = true
  | equal_bin_op Bo_minus Bo_minus = true
  | equal_bin_op Bo_plus Bo_plus = true;

datatype un_op = Uo_minus | Uo_not;

fun equal_un_op Uo_minus Uo_not = false
  | equal_un_op Uo_not Uo_minus = false
  | equal_un_op Uo_not Uo_not = true
  | equal_un_op Uo_minus Uo_minus = true;

datatype exp = E_var of string | E_localvar of string | E_globalvar of string |
  E_const of int | E_bin of bin_op * exp * exp | E_un of un_op * exp;

fun equal_expa (E_bin (x51, x52, x53)) (E_un (x61, x62)) = false
  | equal_expa (E_un (x61, x62)) (E_bin (x51, x52, x53)) = false
  | equal_expa (E_const x4) (E_un (x61, x62)) = false
  | equal_expa (E_un (x61, x62)) (E_const x4) = false
  | equal_expa (E_const x4) (E_bin (x51, x52, x53)) = false
  | equal_expa (E_bin (x51, x52, x53)) (E_const x4) = false
  | equal_expa (E_globalvar x3) (E_un (x61, x62)) = false
  | equal_expa (E_un (x61, x62)) (E_globalvar x3) = false
  | equal_expa (E_globalvar x3) (E_bin (x51, x52, x53)) = false
  | equal_expa (E_bin (x51, x52, x53)) (E_globalvar x3) = false
  | equal_expa (E_globalvar x3) (E_const x4) = false
  | equal_expa (E_const x4) (E_globalvar x3) = false
  | equal_expa (E_localvar x2) (E_un (x61, x62)) = false
  | equal_expa (E_un (x61, x62)) (E_localvar x2) = false
  | equal_expa (E_localvar x2) (E_bin (x51, x52, x53)) = false
  | equal_expa (E_bin (x51, x52, x53)) (E_localvar x2) = false
  | equal_expa (E_localvar x2) (E_const x4) = false
  | equal_expa (E_const x4) (E_localvar x2) = false
  | equal_expa (E_localvar x2) (E_globalvar x3) = false
  | equal_expa (E_globalvar x3) (E_localvar x2) = false
  | equal_expa (E_var x1) (E_un (x61, x62)) = false
  | equal_expa (E_un (x61, x62)) (E_var x1) = false
  | equal_expa (E_var x1) (E_bin (x51, x52, x53)) = false
  | equal_expa (E_bin (x51, x52, x53)) (E_var x1) = false
  | equal_expa (E_var x1) (E_const x4) = false
  | equal_expa (E_const x4) (E_var x1) = false
  | equal_expa (E_var x1) (E_globalvar x3) = false
  | equal_expa (E_globalvar x3) (E_var x1) = false
  | equal_expa (E_var x1) (E_localvar x2) = false
  | equal_expa (E_localvar x2) (E_var x1) = false
  | equal_expa (E_un (x61, x62)) (E_un (y61, y62)) =
    equal_un_op x61 y61 andalso equal_expa x62 y62
  | equal_expa (E_bin (x51, x52, x53)) (E_bin (y51, y52, y53)) =
    equal_bin_op x51 y51 andalso (equal_expa x52 y52 andalso equal_expa x53 y53)
  | equal_expa (E_const x4) (E_const y4) = equal_inta x4 y4
  | equal_expa (E_globalvar x3) (E_globalvar y3) = ((x3 : string) = y3)
  | equal_expa (E_localvar x2) (E_localvar y2) = ((x2 : string) = y2)
  | equal_expa (E_var x1) (E_var y1) = ((x1 : string) = y1);

datatype action = AAssign of exp * string * exp |
  AAssign_local of exp * string * exp | AAssign_global of exp * string * exp |
  ATest of exp | ASkip;

fun equal_actiona (ATest x4) ASkip = false
  | equal_actiona ASkip (ATest x4) = false
  | equal_actiona (AAssign_global (x31, x32, x33)) ASkip = false
  | equal_actiona ASkip (AAssign_global (x31, x32, x33)) = false
  | equal_actiona (AAssign_global (x31, x32, x33)) (ATest x4) = false
  | equal_actiona (ATest x4) (AAssign_global (x31, x32, x33)) = false
  | equal_actiona (AAssign_local (x21, x22, x23)) ASkip = false
  | equal_actiona ASkip (AAssign_local (x21, x22, x23)) = false
  | equal_actiona (AAssign_local (x21, x22, x23)) (ATest x4) = false
  | equal_actiona (ATest x4) (AAssign_local (x21, x22, x23)) = false
  | equal_actiona (AAssign_local (x21, x22, x23))
    (AAssign_global (x31, x32, x33)) = false
  | equal_actiona (AAssign_global (x31, x32, x33))
    (AAssign_local (x21, x22, x23)) = false
  | equal_actiona (AAssign (x11, x12, x13)) ASkip = false
  | equal_actiona ASkip (AAssign (x11, x12, x13)) = false
  | equal_actiona (AAssign (x11, x12, x13)) (ATest x4) = false
  | equal_actiona (ATest x4) (AAssign (x11, x12, x13)) = false
  | equal_actiona (AAssign (x11, x12, x13)) (AAssign_global (x31, x32, x33)) =
    false
  | equal_actiona (AAssign_global (x31, x32, x33)) (AAssign (x11, x12, x13)) =
    false
  | equal_actiona (AAssign (x11, x12, x13)) (AAssign_local (x21, x22, x23)) =
    false
  | equal_actiona (AAssign_local (x21, x22, x23)) (AAssign (x11, x12, x13)) =
    false
  | equal_actiona (ATest x4) (ATest y4) = equal_expa x4 y4
  | equal_actiona (AAssign_global (x31, x32, x33))
    (AAssign_global (y31, y32, y33)) =
    equal_expa x31 y31 andalso
      (((x32 : string) = y32) andalso equal_expa x33 y33)
  | equal_actiona (AAssign_local (x21, x22, x23))
    (AAssign_local (y21, y22, y23)) =
    equal_expa x21 y21 andalso
      (((x22 : string) = y22) andalso equal_expa x23 y23)
  | equal_actiona (AAssign (x11, x12, x13)) (AAssign (y11, y12, y13)) =
    equal_expa x11 y11 andalso
      (((x12 : string) = y12) andalso equal_expa x13 y13)
  | equal_actiona ASkip ASkip = true;

val equal_action = {equal = equal_actiona} : action equal;

datatype cmd = Assign of exp * string * exp | Assign_local of exp * string * exp
  | Assign_global of exp * string * exp | Test of exp | Skip | Seqa of cmd * cmd
  | Or of cmd * cmd | Break | Continue | Iterate of cmd * cmd | Invalid;

fun equal_cmda (Iterate (x101, x102)) Invalid = false
  | equal_cmda Invalid (Iterate (x101, x102)) = false
  | equal_cmda Continue Invalid = false
  | equal_cmda Invalid Continue = false
  | equal_cmda Continue (Iterate (x101, x102)) = false
  | equal_cmda (Iterate (x101, x102)) Continue = false
  | equal_cmda Break Invalid = false
  | equal_cmda Invalid Break = false
  | equal_cmda Break (Iterate (x101, x102)) = false
  | equal_cmda (Iterate (x101, x102)) Break = false
  | equal_cmda Break Continue = false
  | equal_cmda Continue Break = false
  | equal_cmda (Or (x71, x72)) Invalid = false
  | equal_cmda Invalid (Or (x71, x72)) = false
  | equal_cmda (Or (x71, x72)) (Iterate (x101, x102)) = false
  | equal_cmda (Iterate (x101, x102)) (Or (x71, x72)) = false
  | equal_cmda (Or (x71, x72)) Continue = false
  | equal_cmda Continue (Or (x71, x72)) = false
  | equal_cmda (Or (x71, x72)) Break = false
  | equal_cmda Break (Or (x71, x72)) = false
  | equal_cmda (Seqa (x61, x62)) Invalid = false
  | equal_cmda Invalid (Seqa (x61, x62)) = false
  | equal_cmda (Seqa (x61, x62)) (Iterate (x101, x102)) = false
  | equal_cmda (Iterate (x101, x102)) (Seqa (x61, x62)) = false
  | equal_cmda (Seqa (x61, x62)) Continue = false
  | equal_cmda Continue (Seqa (x61, x62)) = false
  | equal_cmda (Seqa (x61, x62)) Break = false
  | equal_cmda Break (Seqa (x61, x62)) = false
  | equal_cmda (Seqa (x61, x62)) (Or (x71, x72)) = false
  | equal_cmda (Or (x71, x72)) (Seqa (x61, x62)) = false
  | equal_cmda Skip Invalid = false
  | equal_cmda Invalid Skip = false
  | equal_cmda Skip (Iterate (x101, x102)) = false
  | equal_cmda (Iterate (x101, x102)) Skip = false
  | equal_cmda Skip Continue = false
  | equal_cmda Continue Skip = false
  | equal_cmda Skip Break = false
  | equal_cmda Break Skip = false
  | equal_cmda Skip (Or (x71, x72)) = false
  | equal_cmda (Or (x71, x72)) Skip = false
  | equal_cmda Skip (Seqa (x61, x62)) = false
  | equal_cmda (Seqa (x61, x62)) Skip = false
  | equal_cmda (Test x4) Invalid = false
  | equal_cmda Invalid (Test x4) = false
  | equal_cmda (Test x4) (Iterate (x101, x102)) = false
  | equal_cmda (Iterate (x101, x102)) (Test x4) = false
  | equal_cmda (Test x4) Continue = false
  | equal_cmda Continue (Test x4) = false
  | equal_cmda (Test x4) Break = false
  | equal_cmda Break (Test x4) = false
  | equal_cmda (Test x4) (Or (x71, x72)) = false
  | equal_cmda (Or (x71, x72)) (Test x4) = false
  | equal_cmda (Test x4) (Seqa (x61, x62)) = false
  | equal_cmda (Seqa (x61, x62)) (Test x4) = false
  | equal_cmda (Test x4) Skip = false
  | equal_cmda Skip (Test x4) = false
  | equal_cmda (Assign_global (x31, x32, x33)) Invalid = false
  | equal_cmda Invalid (Assign_global (x31, x32, x33)) = false
  | equal_cmda (Assign_global (x31, x32, x33)) (Iterate (x101, x102)) = false
  | equal_cmda (Iterate (x101, x102)) (Assign_global (x31, x32, x33)) = false
  | equal_cmda (Assign_global (x31, x32, x33)) Continue = false
  | equal_cmda Continue (Assign_global (x31, x32, x33)) = false
  | equal_cmda (Assign_global (x31, x32, x33)) Break = false
  | equal_cmda Break (Assign_global (x31, x32, x33)) = false
  | equal_cmda (Assign_global (x31, x32, x33)) (Or (x71, x72)) = false
  | equal_cmda (Or (x71, x72)) (Assign_global (x31, x32, x33)) = false
  | equal_cmda (Assign_global (x31, x32, x33)) (Seqa (x61, x62)) = false
  | equal_cmda (Seqa (x61, x62)) (Assign_global (x31, x32, x33)) = false
  | equal_cmda (Assign_global (x31, x32, x33)) Skip = false
  | equal_cmda Skip (Assign_global (x31, x32, x33)) = false
  | equal_cmda (Assign_global (x31, x32, x33)) (Test x4) = false
  | equal_cmda (Test x4) (Assign_global (x31, x32, x33)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) Invalid = false
  | equal_cmda Invalid (Assign_local (x21, x22, x23)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) (Iterate (x101, x102)) = false
  | equal_cmda (Iterate (x101, x102)) (Assign_local (x21, x22, x23)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) Continue = false
  | equal_cmda Continue (Assign_local (x21, x22, x23)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) Break = false
  | equal_cmda Break (Assign_local (x21, x22, x23)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) (Or (x71, x72)) = false
  | equal_cmda (Or (x71, x72)) (Assign_local (x21, x22, x23)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) (Seqa (x61, x62)) = false
  | equal_cmda (Seqa (x61, x62)) (Assign_local (x21, x22, x23)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) Skip = false
  | equal_cmda Skip (Assign_local (x21, x22, x23)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) (Test x4) = false
  | equal_cmda (Test x4) (Assign_local (x21, x22, x23)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) (Assign_global (x31, x32, x33)) =
    false
  | equal_cmda (Assign_global (x31, x32, x33)) (Assign_local (x21, x22, x23)) =
    false
  | equal_cmda (Assign (x11, x12, x13)) Invalid = false
  | equal_cmda Invalid (Assign (x11, x12, x13)) = false
  | equal_cmda (Assign (x11, x12, x13)) (Iterate (x101, x102)) = false
  | equal_cmda (Iterate (x101, x102)) (Assign (x11, x12, x13)) = false
  | equal_cmda (Assign (x11, x12, x13)) Continue = false
  | equal_cmda Continue (Assign (x11, x12, x13)) = false
  | equal_cmda (Assign (x11, x12, x13)) Break = false
  | equal_cmda Break (Assign (x11, x12, x13)) = false
  | equal_cmda (Assign (x11, x12, x13)) (Or (x71, x72)) = false
  | equal_cmda (Or (x71, x72)) (Assign (x11, x12, x13)) = false
  | equal_cmda (Assign (x11, x12, x13)) (Seqa (x61, x62)) = false
  | equal_cmda (Seqa (x61, x62)) (Assign (x11, x12, x13)) = false
  | equal_cmda (Assign (x11, x12, x13)) Skip = false
  | equal_cmda Skip (Assign (x11, x12, x13)) = false
  | equal_cmda (Assign (x11, x12, x13)) (Test x4) = false
  | equal_cmda (Test x4) (Assign (x11, x12, x13)) = false
  | equal_cmda (Assign (x11, x12, x13)) (Assign_global (x31, x32, x33)) = false
  | equal_cmda (Assign_global (x31, x32, x33)) (Assign (x11, x12, x13)) = false
  | equal_cmda (Assign (x11, x12, x13)) (Assign_local (x21, x22, x23)) = false
  | equal_cmda (Assign_local (x21, x22, x23)) (Assign (x11, x12, x13)) = false
  | equal_cmda (Iterate (x101, x102)) (Iterate (y101, y102)) =
    equal_cmda x101 y101 andalso equal_cmda x102 y102
  | equal_cmda (Or (x71, x72)) (Or (y71, y72)) =
    equal_cmda x71 y71 andalso equal_cmda x72 y72
  | equal_cmda (Seqa (x61, x62)) (Seqa (y61, y62)) =
    equal_cmda x61 y61 andalso equal_cmda x62 y62
  | equal_cmda (Test x4) (Test y4) = equal_expa x4 y4
  | equal_cmda (Assign_global (x31, x32, x33)) (Assign_global (y31, y32, y33)) =
    equal_expa x31 y31 andalso
      (((x32 : string) = y32) andalso equal_expa x33 y33)
  | equal_cmda (Assign_local (x21, x22, x23)) (Assign_local (y21, y22, y23)) =
    equal_expa x21 y21 andalso
      (((x22 : string) = y22) andalso equal_expa x23 y23)
  | equal_cmda (Assign (x11, x12, x13)) (Assign (y11, y12, y13)) =
    equal_expa x11 y11 andalso
      (((x12 : string) = y12) andalso equal_expa x13 y13)
  | equal_cmda Invalid Invalid = true
  | equal_cmda Continue Continue = true
  | equal_cmda Break Break = true
  | equal_cmda Skip Skip = true;

val equal_cmd = {equal = equal_cmda} : cmd equal;

val equal_exp = {equal = equal_expa} : exp equal;

fun comparator_bin_op Bo_xor Bo_xor = Eq
  | comparator_bin_op Bo_xor Bo_or = Gt
  | comparator_bin_op Bo_xor Bo_and = Gt
  | comparator_bin_op Bo_xor Bo_eq = Gt
  | comparator_bin_op Bo_xor Bo_less_eq = Gt
  | comparator_bin_op Bo_xor Bo_less = Gt
  | comparator_bin_op Bo_xor Bo_mod = Gt
  | comparator_bin_op Bo_xor Bo_div = Gt
  | comparator_bin_op Bo_xor Bo_mul = Gt
  | comparator_bin_op Bo_xor Bo_minus = Gt
  | comparator_bin_op Bo_xor Bo_plus = Gt
  | comparator_bin_op Bo_or Bo_xor = Lt
  | comparator_bin_op Bo_or Bo_or = Eq
  | comparator_bin_op Bo_or Bo_and = Gt
  | comparator_bin_op Bo_or Bo_eq = Gt
  | comparator_bin_op Bo_or Bo_less_eq = Gt
  | comparator_bin_op Bo_or Bo_less = Gt
  | comparator_bin_op Bo_or Bo_mod = Gt
  | comparator_bin_op Bo_or Bo_div = Gt
  | comparator_bin_op Bo_or Bo_mul = Gt
  | comparator_bin_op Bo_or Bo_minus = Gt
  | comparator_bin_op Bo_or Bo_plus = Gt
  | comparator_bin_op Bo_and Bo_xor = Lt
  | comparator_bin_op Bo_and Bo_or = Lt
  | comparator_bin_op Bo_and Bo_and = Eq
  | comparator_bin_op Bo_and Bo_eq = Gt
  | comparator_bin_op Bo_and Bo_less_eq = Gt
  | comparator_bin_op Bo_and Bo_less = Gt
  | comparator_bin_op Bo_and Bo_mod = Gt
  | comparator_bin_op Bo_and Bo_div = Gt
  | comparator_bin_op Bo_and Bo_mul = Gt
  | comparator_bin_op Bo_and Bo_minus = Gt
  | comparator_bin_op Bo_and Bo_plus = Gt
  | comparator_bin_op Bo_eq Bo_xor = Lt
  | comparator_bin_op Bo_eq Bo_or = Lt
  | comparator_bin_op Bo_eq Bo_and = Lt
  | comparator_bin_op Bo_eq Bo_eq = Eq
  | comparator_bin_op Bo_eq Bo_less_eq = Gt
  | comparator_bin_op Bo_eq Bo_less = Gt
  | comparator_bin_op Bo_eq Bo_mod = Gt
  | comparator_bin_op Bo_eq Bo_div = Gt
  | comparator_bin_op Bo_eq Bo_mul = Gt
  | comparator_bin_op Bo_eq Bo_minus = Gt
  | comparator_bin_op Bo_eq Bo_plus = Gt
  | comparator_bin_op Bo_less_eq Bo_xor = Lt
  | comparator_bin_op Bo_less_eq Bo_or = Lt
  | comparator_bin_op Bo_less_eq Bo_and = Lt
  | comparator_bin_op Bo_less_eq Bo_eq = Lt
  | comparator_bin_op Bo_less_eq Bo_less_eq = Eq
  | comparator_bin_op Bo_less_eq Bo_less = Gt
  | comparator_bin_op Bo_less_eq Bo_mod = Gt
  | comparator_bin_op Bo_less_eq Bo_div = Gt
  | comparator_bin_op Bo_less_eq Bo_mul = Gt
  | comparator_bin_op Bo_less_eq Bo_minus = Gt
  | comparator_bin_op Bo_less_eq Bo_plus = Gt
  | comparator_bin_op Bo_less Bo_xor = Lt
  | comparator_bin_op Bo_less Bo_or = Lt
  | comparator_bin_op Bo_less Bo_and = Lt
  | comparator_bin_op Bo_less Bo_eq = Lt
  | comparator_bin_op Bo_less Bo_less_eq = Lt
  | comparator_bin_op Bo_less Bo_less = Eq
  | comparator_bin_op Bo_less Bo_mod = Gt
  | comparator_bin_op Bo_less Bo_div = Gt
  | comparator_bin_op Bo_less Bo_mul = Gt
  | comparator_bin_op Bo_less Bo_minus = Gt
  | comparator_bin_op Bo_less Bo_plus = Gt
  | comparator_bin_op Bo_mod Bo_xor = Lt
  | comparator_bin_op Bo_mod Bo_or = Lt
  | comparator_bin_op Bo_mod Bo_and = Lt
  | comparator_bin_op Bo_mod Bo_eq = Lt
  | comparator_bin_op Bo_mod Bo_less_eq = Lt
  | comparator_bin_op Bo_mod Bo_less = Lt
  | comparator_bin_op Bo_mod Bo_mod = Eq
  | comparator_bin_op Bo_mod Bo_div = Gt
  | comparator_bin_op Bo_mod Bo_mul = Gt
  | comparator_bin_op Bo_mod Bo_minus = Gt
  | comparator_bin_op Bo_mod Bo_plus = Gt
  | comparator_bin_op Bo_div Bo_xor = Lt
  | comparator_bin_op Bo_div Bo_or = Lt
  | comparator_bin_op Bo_div Bo_and = Lt
  | comparator_bin_op Bo_div Bo_eq = Lt
  | comparator_bin_op Bo_div Bo_less_eq = Lt
  | comparator_bin_op Bo_div Bo_less = Lt
  | comparator_bin_op Bo_div Bo_mod = Lt
  | comparator_bin_op Bo_div Bo_div = Eq
  | comparator_bin_op Bo_div Bo_mul = Gt
  | comparator_bin_op Bo_div Bo_minus = Gt
  | comparator_bin_op Bo_div Bo_plus = Gt
  | comparator_bin_op Bo_mul Bo_xor = Lt
  | comparator_bin_op Bo_mul Bo_or = Lt
  | comparator_bin_op Bo_mul Bo_and = Lt
  | comparator_bin_op Bo_mul Bo_eq = Lt
  | comparator_bin_op Bo_mul Bo_less_eq = Lt
  | comparator_bin_op Bo_mul Bo_less = Lt
  | comparator_bin_op Bo_mul Bo_mod = Lt
  | comparator_bin_op Bo_mul Bo_div = Lt
  | comparator_bin_op Bo_mul Bo_mul = Eq
  | comparator_bin_op Bo_mul Bo_minus = Gt
  | comparator_bin_op Bo_mul Bo_plus = Gt
  | comparator_bin_op Bo_minus Bo_xor = Lt
  | comparator_bin_op Bo_minus Bo_or = Lt
  | comparator_bin_op Bo_minus Bo_and = Lt
  | comparator_bin_op Bo_minus Bo_eq = Lt
  | comparator_bin_op Bo_minus Bo_less_eq = Lt
  | comparator_bin_op Bo_minus Bo_less = Lt
  | comparator_bin_op Bo_minus Bo_mod = Lt
  | comparator_bin_op Bo_minus Bo_div = Lt
  | comparator_bin_op Bo_minus Bo_mul = Lt
  | comparator_bin_op Bo_minus Bo_minus = Eq
  | comparator_bin_op Bo_minus Bo_plus = Gt
  | comparator_bin_op Bo_plus Bo_xor = Lt
  | comparator_bin_op Bo_plus Bo_or = Lt
  | comparator_bin_op Bo_plus Bo_and = Lt
  | comparator_bin_op Bo_plus Bo_eq = Lt
  | comparator_bin_op Bo_plus Bo_less_eq = Lt
  | comparator_bin_op Bo_plus Bo_less = Lt
  | comparator_bin_op Bo_plus Bo_mod = Lt
  | comparator_bin_op Bo_plus Bo_div = Lt
  | comparator_bin_op Bo_plus Bo_mul = Lt
  | comparator_bin_op Bo_plus Bo_minus = Lt
  | comparator_bin_op Bo_plus Bo_plus = Eq;

fun comparator_un_op Uo_not Uo_not = Eq
  | comparator_un_op Uo_not Uo_minus = Gt
  | comparator_un_op Uo_minus Uo_not = Lt
  | comparator_un_op Uo_minus Uo_minus = Eq;

val ord_literal =
  {less_eq = (fn a => fn b => ((a : string) <= b)),
    less = (fn a => fn b => ((a : string) < b))}
  : string ord;

val preorder_literal = {ord_preorder = ord_literal} : string preorder;

val order_literal = {preorder_order = preorder_literal} : string order;

val linorder_literal = {order_linorder = order_literal} : string linorder;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

fun comparator_exp (E_un (x, xa)) (E_un (yg, yh)) =
  (case comparator_un_op x yg of Eq => comparator_exp xa yh | Lt => Lt
    | Gt => Gt)
  | comparator_exp (E_un (x, xa)) (E_bin (yd, ye, yf)) = Gt
  | comparator_exp (E_un (x, xa)) (E_const yc) = Gt
  | comparator_exp (E_un (x, xa)) (E_globalvar yb) = Gt
  | comparator_exp (E_un (x, xa)) (E_localvar ya) = Gt
  | comparator_exp (E_un (x, xa)) (E_var y) = Gt
  | comparator_exp (E_bin (x, xa, xb)) (E_un (yg, yh)) = Lt
  | comparator_exp (E_bin (x, xa, xb)) (E_bin (yd, ye, yf)) =
    (case comparator_bin_op x yd
      of Eq =>
        (case comparator_exp xa ye of Eq => comparator_exp xb yf | Lt => Lt
          | Gt => Gt)
      | Lt => Lt | Gt => Gt)
  | comparator_exp (E_bin (x, xa, xb)) (E_const yc) = Gt
  | comparator_exp (E_bin (x, xa, xb)) (E_globalvar yb) = Gt
  | comparator_exp (E_bin (x, xa, xb)) (E_localvar ya) = Gt
  | comparator_exp (E_bin (x, xa, xb)) (E_var y) = Gt
  | comparator_exp (E_const x) (E_un (yg, yh)) = Lt
  | comparator_exp (E_const x) (E_bin (yd, ye, yf)) = Lt
  | comparator_exp (E_const x) (E_const yc) =
    comparator_of (equal_int, linorder_int) x yc
  | comparator_exp (E_const x) (E_globalvar yb) = Gt
  | comparator_exp (E_const x) (E_localvar ya) = Gt
  | comparator_exp (E_const x) (E_var y) = Gt
  | comparator_exp (E_globalvar x) (E_un (yg, yh)) = Lt
  | comparator_exp (E_globalvar x) (E_bin (yd, ye, yf)) = Lt
  | comparator_exp (E_globalvar x) (E_const yc) = Lt
  | comparator_exp (E_globalvar x) (E_globalvar yb) =
    comparator_of (equal_literal, linorder_literal) x yb
  | comparator_exp (E_globalvar x) (E_localvar ya) = Gt
  | comparator_exp (E_globalvar x) (E_var y) = Gt
  | comparator_exp (E_localvar x) (E_un (yg, yh)) = Lt
  | comparator_exp (E_localvar x) (E_bin (yd, ye, yf)) = Lt
  | comparator_exp (E_localvar x) (E_const yc) = Lt
  | comparator_exp (E_localvar x) (E_globalvar yb) = Lt
  | comparator_exp (E_localvar x) (E_localvar ya) =
    comparator_of (equal_literal, linorder_literal) x ya
  | comparator_exp (E_localvar x) (E_var y) = Gt
  | comparator_exp (E_var x) (E_un (yg, yh)) = Lt
  | comparator_exp (E_var x) (E_bin (yd, ye, yf)) = Lt
  | comparator_exp (E_var x) (E_const yc) = Lt
  | comparator_exp (E_var x) (E_globalvar yb) = Lt
  | comparator_exp (E_var x) (E_localvar ya) = Lt
  | comparator_exp (E_var x) (E_var y) =
    comparator_of (equal_literal, linorder_literal) x y;

fun less_eq_exp x = le_of_comp comparator_exp x;

fun less_exp x = lt_of_comp comparator_exp x;

val ord_exp = {less_eq = less_eq_exp, less = less_exp} : exp ord;

val preorder_exp = {ord_preorder = ord_exp} : exp preorder;

val order_exp = {preorder_order = preorder_exp} : exp order;

val linorder_exp = {order_linorder = order_exp} : exp linorder;

val equal_uint32 = {equal = (fn a => fn b => ((a : Word32.word) = b))} :
  Word32.word equal;

val plus_uint32 = {plus = (fn a => fn b => Word32.+ (a, b))} : Word32.word plus;

val zero_uint32 = {zero = (Word32.fromInt 0)} : Word32.word zero;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

val semigroup_add_uint32 = {plus_semigroup_add = plus_uint32} :
  Word32.word semigroup_add;

val monoid_add_uint32 =
  {semigroup_add_monoid_add = semigroup_add_uint32,
    zero_monoid_add = zero_uint32}
  : Word32.word monoid_add;

fun def_hashmap_size_uint32 t = nat_of_integer (8 : IntInf.int);

fun hashcode_uint32 x = x;

val hashable_uint32 =
  {hashcode = hashcode_uint32, def_hashmap_size = def_hashmap_size_uint32} :
  Word32.word hashable;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

val ab_semigroup_add_uint32 =
  {semigroup_add_ab_semigroup_add = semigroup_add_uint32} :
  Word32.word ab_semigroup_add;

val comm_monoid_add_uint32 =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_uint32,
    monoid_add_comm_monoid_add = monoid_add_uint32}
  : Word32.word comm_monoid_add;

datatype brk_ctd = AIBreak | AIContinue;

fun equal_brk_ctda AIBreak AIContinue = false
  | equal_brk_ctda AIContinue AIBreak = false
  | equal_brk_ctda AIContinue AIContinue = true
  | equal_brk_ctda AIBreak AIBreak = true;

val equal_brk_ctd = {equal = equal_brk_ctda} : brk_ctd equal;

datatype ('a, 'b) phantom = Phantom of 'b;

val finite_UNIV_literala : (string, bool) phantom = Phantom false;

val card_UNIV_literala : (string, nat) phantom = Phantom zero_nata;

type 'a finite_UNIV = {finite_UNIV : ('a, bool) phantom};
val finite_UNIV = #finite_UNIV : 'a finite_UNIV -> ('a, bool) phantom;

type 'a card_UNIV =
  {finite_UNIV_card_UNIV : 'a finite_UNIV, card_UNIV : ('a, nat) phantom};
val finite_UNIV_card_UNIV = #finite_UNIV_card_UNIV :
  'a card_UNIV -> 'a finite_UNIV;
val card_UNIV = #card_UNIV : 'a card_UNIV -> ('a, nat) phantom;

val finite_UNIV_literal = {finite_UNIV = finite_UNIV_literala} :
  string finite_UNIV;

val card_UNIV_literal =
  {finite_UNIV_card_UNIV = finite_UNIV_literal, card_UNIV = card_UNIV_literala}
  : string card_UNIV;

datatype enat = Enat of nat | Infinity_enat;

fun less_eq_enat Infinity_enat (Enat n) = false
  | less_eq_enat q Infinity_enat = true
  | less_eq_enat (Enat m) (Enat n) = less_eq_nat m n;

fun less_enat Infinity_enat q = false
  | less_enat (Enat m) Infinity_enat = true
  | less_enat (Enat m) (Enat n) = less_nat m n;

val ord_enat = {less_eq = less_eq_enat, less = less_enat} : enat ord;

type 'a len0 = {len_of : 'a itself -> nat};
val len_of = #len_of : 'a len0 -> 'a itself -> nat;

type 'a countable = {};

type 'a finite = {countable_finite : 'a countable};
val countable_finite = #countable_finite : 'a finite -> 'a countable;

datatype 'a bit0 = Abs_bit0 of int;

fun len_of_bit0 A_ uu =
  times_nata (nat_of_integer (2 : IntInf.int)) (len_of A_ Type);

type 'a len = {len0_len : 'a len0};
val len0_len = #len0_len : 'a len -> 'a len0;

fun len0_bit0 A_ = {len_of = len_of_bit0 A_} : 'a bit0 len0;

fun len_bit0 A_ = {len0_len = len0_bit0 (len0_len A_)} : 'a bit0 len;

datatype num1 = One_num1;

fun len_of_num1 uu = one_nata;

val len0_num1 = {len_of = len_of_num1} : num1 len0;

val len_num1 = {len0_len = len0_num1} : num1 len;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun def_hashmap_size_prod A_ B_ =
  (fn _ => plus_nata (def_hashmap_size A_ Type) (def_hashmap_size B_ Type));

fun hashcode_prod A_ B_ x =
  Word32.+ (Word32.* (hashcode A_
                        (fst x), Word32.fromLargeInt (IntInf.toLarge (33 : IntInf.int))), hashcode
            B_ (snd x));

fun hashable_prod A_ B_ =
  {hashcode = hashcode_prod A_ B_,
    def_hashmap_size = def_hashmap_size_prod A_ B_}
  : ('a * 'b) hashable;

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit equal;

fun def_hashmap_size_unit x = (fn _ => nat_of_integer (2 : IntInf.int)) x;

fun hashcode_unit u = (Word32.fromInt 0);

val hashable_unit =
  {hashcode = hashcode_unit, def_hashmap_size = def_hashmap_size_unit} :
  unit hashable;

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype ('a, 'b, 'c) local_config_ext = Local_config_ext of 'a * 'b * 'c;

fun equal_local_config_exta A_ B_ C_
  (Local_config_ext (commanda, statea, morea))
  (Local_config_ext (command, state, more)) =
  eq A_ commanda command andalso (eq B_ statea state andalso eq C_ morea more);

fun equal_local_config_ext A_ B_ C_ = {equal = equal_local_config_exta A_ B_ C_}
  : ('a, 'b, 'c) local_config_ext equal;

fun def_hashmap_size_local_config_ext A_ B_ C_ t =
  nat_of_integer (8 : IntInf.int);

fun command (Local_config_ext (command, state, more)) = command;

fun state (Local_config_ext (command, state, more)) = state;

fun more (Local_config_ext (command, state, more)) = more;

fun hashcode_local_config_ext A_ B_ C_ lc =
  Word32.+ (Word32.+ (hashcode A_
                        (command
                          lc), hashcode B_ (state lc)), hashcode C_ (more lc));

fun hashable_local_config_ext A_ B_ C_ =
  {hashcode = hashcode_local_config_ext A_ B_ C_,
    def_hashmap_size = def_hashmap_size_local_config_ext A_ B_ C_}
  : ('a, 'b, 'c) local_config_ext hashable;

datatype color = R | B;

datatype ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;

datatype ('b, 'a) rbt = RBT of ('b, 'a) rbta;

datatype ('a, 'b) mapping = Mapping of ('a, 'b) rbt;

datatype 'a local_state_impl_ext =
  Local_state_impl_ext of (string, Word32.word) mapping * 'a;

fun equal_list A_ [] (x21 :: x22) = false
  | equal_list A_ (x21 :: x22) [] = false
  | equal_list A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_list A_ x22 y22
  | equal_list A_ [] [] = true;

fun gen_entries kvts (Branch (c, l, k, v, r)) =
  gen_entries (((k, v), r) :: kvts) l
  | gen_entries ((kv, t) :: kvts) Empty = kv :: gen_entries kvts t
  | gen_entries [] Empty = [];

fun entriesa x = gen_entries [] x;

fun impl_of B_ (RBT x) = x;

fun entries A_ x = entriesa (impl_of A_ x);

fun equal_mapping (A1_, A2_) B_ (Mapping t1) (Mapping t2) =
  equal_list (equal_prod A1_ B_) (entries A2_ t1) (entries A2_ t2);

fun equal_local_state_impl_exta A_ (Local_state_impl_ext (variablesa, morea))
  (Local_state_impl_ext (variables, more)) =
  equal_mapping (equal_literal, linorder_literal) equal_uint32 variablesa
    variables andalso
    eq A_ morea more;

fun equal_local_state_impl_ext A_ = {equal = equal_local_state_impl_exta A_} :
  'a local_state_impl_ext equal;

fun def_hashmap_size_local_state_impl_ext A_ t =
  nat_of_integer (8 : IntInf.int);

fun variables (Local_state_impl_ext (variables, more)) = variables;

fun moreb (Local_state_impl_ext (variables, more)) = more;

fun hashcode_option A_ opt =
  (case opt of NONE => (Word32.fromInt 0)
    | SOME a => Word32.+ (hashcode A_ a, (Word32.fromInt 1)));

fun id x = (fn xa => xa) x;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun sum_list A_ xs =
  foldr (plus ((plus_semigroup_add o semigroup_add_monoid_add) A_)) xs
    (zero (zero_monoid_add A_));

datatype 'a set = Set of 'a list | Coset of 'a list;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun sum A_ B_ g (Set xs) =
  sum_list (monoid_add_comm_monoid_add B_) (map g (remdups A_ xs));

fun rbt_lookup A_ Empty k = NONE
  | rbt_lookup A_ (Branch (uu, l, x, y, r)) k =
    (if less A_ k x then rbt_lookup A_ l k
      else (if less A_ x k then rbt_lookup A_ r k else SOME y));

fun lookup A_ x =
  rbt_lookup ((ord_preorder o preorder_order o order_linorder) A_)
    (impl_of A_ x);

fun lookupa A_ (Mapping t) = lookup A_ t;

fun gen_keys kts (Branch (c, l, k, v, r)) = gen_keys ((k, r) :: kts) l
  | gen_keys ((k, t) :: kts) Empty = k :: gen_keys kts t
  | gen_keys [] Empty = [];

fun keysb x = gen_keys [] x;

fun keys A_ x = keysb (impl_of A_ x);

fun keysa A_ (Mapping t) = Set (keys A_ t);

fun image f (Set xs) = Set (map f xs);

fun mapping_val_hashcode A_ B_ m =
  sum equal_uint32 comm_monoid_add_uint32 (fn x => x)
    (image (hashcode_option B_ o lookupa A_ m) (keysa A_ m));

fun hashcode_local_state_impl_ext A_ ls =
  Word32.+ (mapping_val_hashcode linorder_literal hashable_uint32
              (variables ls), hashcode A_ (moreb ls));

fun hashable_local_state_impl_ext A_ =
  {hashcode = hashcode_local_state_impl_ext A_,
    def_hashmap_size = def_hashmap_size_local_state_impl_ext A_}
  : 'a local_state_impl_ext hashable;

datatype ('a, 'b, 'c, 'd) pid_global_config_ext =
  Pid_global_config_ext of ('a, 'b, unit) local_config_ext list * 'c * 'd;

fun equal_pid_global_config_exta A_ B_ C_ D_
  (Pid_global_config_ext (processesa, statea, morea))
  (Pid_global_config_ext (processes, state, more)) =
  equal_list (equal_local_config_ext A_ B_ equal_unit) processesa
    processes andalso
    (eq C_ statea state andalso eq D_ morea more);

fun equal_pid_global_config_ext A_ B_ C_ D_ =
  {equal = equal_pid_global_config_exta A_ B_ C_ D_} :
  ('a, 'b, 'c, 'd) pid_global_config_ext equal;

fun def_hashmap_size_pid_global_config_ext A_ B_ C_ D_ t =
  nat_of_integer (8 : IntInf.int);

fun processesa (Pid_global_config_ext (processes, state, more)) = processes;

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun hashcode_list A_ =
  foldl (fn h => fn x =>
          Word32.+ (Word32.* (h, Word32.fromLargeInt (IntInf.toLarge (33 : IntInf.int))), hashcode
            A_ x))
    (Word32.fromLargeInt (IntInf.toLarge (5381 : IntInf.int)));

fun statea (Pid_global_config_ext (processes, state, more)) = state;

fun morec (Pid_global_config_ext (processes, state, more)) = more;

fun hashcode_pid_global_config_ext A_ B_ C_ D_ gc =
  Word32.+ (Word32.+ (hashcode_list
                        (hashable_local_config_ext A_ B_ hashable_unit)
                        (processesa
                          gc), hashcode C_
                                 (statea gc)), hashcode D_ (morec gc));

fun hashable_pid_global_config_ext A_ B_ C_ D_ =
  {hashcode = hashcode_pid_global_config_ext A_ B_ C_ D_,
    def_hashmap_size = def_hashmap_size_pid_global_config_ext A_ B_ C_ D_}
  : ('a, 'b, 'c, 'd) pid_global_config_ext hashable;

datatype 'a global_state_impl_ext =
  Global_state_impl_ext of (string, Word32.word) mapping * 'a;

fun equal_global_state_impl_exta A_ (Global_state_impl_ext (variablesa, morea))
  (Global_state_impl_ext (variables, more)) =
  equal_mapping (equal_literal, linorder_literal) equal_uint32 variablesa
    variables andalso
    eq A_ morea more;

fun equal_global_state_impl_ext A_ = {equal = equal_global_state_impl_exta A_} :
  'a global_state_impl_ext equal;

fun def_hashmap_size_global_state_impl_ext A_ t =
  nat_of_integer (8 : IntInf.int);

fun variablesa (Global_state_impl_ext (variables, more)) = variables;

fun mored (Global_state_impl_ext (variables, more)) = more;

fun hashcode_global_state_impl_ext A_ gs =
  Word32.+ (mapping_val_hashcode linorder_literal hashable_uint32
              (variablesa gs), hashcode A_ (mored gs));

fun hashable_global_state_impl_ext A_ =
  {hashcode = hashcode_global_state_impl_ext A_,
    def_hashmap_size = def_hashmap_size_global_state_impl_ext A_}
  : 'a global_state_impl_ext hashable;

datatype 'a ltlc = True_ltlc | False_ltlc | Prop_ltlc of 'a |
  Not_ltlc of 'a ltlc | And_ltlc of 'a ltlc * 'a ltlc |
  Or_ltlc of 'a ltlc * 'a ltlc | Implies_ltlc of 'a ltlc * 'a ltlc |
  Next_ltlc of 'a ltlc | Final_ltlc of 'a ltlc | Global_ltlc of 'a ltlc |
  Until_ltlc of 'a ltlc * 'a ltlc | Release_ltlc of 'a ltlc * 'a ltlc;

datatype 'a word = Word of int;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

datatype 'a seq = Emptya | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);

datatype 'a dres = DSUCCEEDi | DFAILi | DRETURN of 'a;

datatype mode = Nop | Fast | Slow;

datatype compare = LT | GT | EQ;

datatype comp_res = LESS | EQUAL | GREATER;

datatype config_ce = CFG_CE_SCC_GABOW | CFG_CE_NDFS;

datatype ('a, 'b) lasso_ext = Lasso_ext of 'a list * 'a * 'a list * 'b;

datatype sm_result = TY_ERR | SAT | UNSAT |
  UNSAT_CE of
    ((nat, unit local_state_impl_ext, unit global_state_impl_ext, unit)
       pid_global_config_ext,
      unit)
      lasso_ext;

datatype ('a, 'b) hashmapa =
  HashMapa of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype ('b, 'a) hashmap = HashMap of ('b, 'a) hashmapa;

datatype config_l2b = CFG_L2B_GERTHS;

datatype 'a blue_witness = NO_CYC | REACH of 'a * 'a list |
  CIRC of 'a list * 'a list;

datatype ('a, 'b) hashmapb =
  HashMapb of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype 'a proc_decl_ext = Proc_decl_ext of string * cmd * string list * 'a;

datatype 'a program_ext =
  Program_ext of unit proc_decl_ext list * string list * 'a;

datatype ('a, 'b, 'c, 'd) gen_g_impl_ext = Gen_g_impl_ext of 'a * 'b * 'c * 'd;

datatype ('a, 'b) node_impl_ext =
  Node_impl_ext of
    nat * (nat, unit) rbta * 'a ltln list * 'a ltln list * 'a ltln list * 'b;

datatype ('a, 'b) gen_bg_impl_ext = Gen_bg_impl_ext of 'a * 'b;

datatype ('a, 'b) gen_sa_impl_ext = Gen_sa_impl_ext of 'a * 'b;

datatype ('a, 'b) gen_gba_impl_ext = Gen_gba_impl_ext of 'a * 'b;

datatype ('a, 'b) gen_gbg_impl_ext = Gen_gbg_impl_ext of 'a * 'b;

datatype ('a, 'b) gen_igba_impl_ext = Gen_igba_impl_ext of 'a * 'b;

datatype ('a, 'b) gen_igbg_impl_ext = Gen_igbg_impl_ext of nat * 'a * 'b;

datatype ('a, 'b) fas_state_impl_ext = Fas_state_impl_ext of 'a * 'b;

datatype ('a, 'b, 'c) simple_state_impl_ext =
  Simple_state_impl_ext of 'a * 'b * 'b * 'c;

datatype ('a, 'b, 'c) simple_state_nos_impl_ext =
  Simple_state_nos_impl_ext of 'a * 'b * 'c;

fun nat k = Nat (max ord_integer (0 : IntInf.int) (integer_of_int k));

fun suc n = plus_nata n one_nata;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun nth (x :: xs) n =
  (if equal_nata n zero_nata then x else nth xs (minus_nat n one_nata));

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun bind xs f = maps f xs;

fun null [] = true
  | null (x :: xs) = false;

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun nota e = E_bin (Bo_eq, e, E_const zero_int);

fun var v = E_var v;

fun empty A_ = RBT Empty;

fun test_bit_integer x n = Bits_Integer.test_bit x (integer_of_nat n);

fun test_bit_int (Int_of_integer x) n = test_bit_integer x n;

fun shiftl_integer x n = Bits_Integer.shiftl x (integer_of_nat n);

fun shiftl_int (Int_of_integer x) n = Int_of_integer (shiftl_integer x n);

fun bitAND_int (Int_of_integer i) (Int_of_integer j) =
  Int_of_integer (IntInf.andb (i, j));

fun minus_int k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

fun bit_integer i true = IntInf.+ (shiftl_integer i one_nata, (1 : IntInf.int))
  | bit_integer i false = shiftl_integer i one_nata;

fun bit (Int_of_integer i) b = Int_of_integer (bit_integer i b);

fun bin_mask n =
  (if equal_nata n zero_nata then zero_int
    else bit (bin_mask (minus_nat n one_nata)) true);

fun sbintrunc n bin =
  let
    val bina = bitAND_int bin (bin_mask (plus_nata n one_nata));
  in
    (if test_bit_int bina n
      then minus_int bina (shiftl_int (Int_of_integer (2 : IntInf.int)) n)
      else bina)
  end;

fun uint A_ (Word x) = x;

fun sint A_ w =
  sbintrunc (minus_nat (len_of (len0_len A_) Type) one_nata)
    (uint (len0_len A_) w);

fun sub asa n = Vector.sub (asa, integer_of_nat n);

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun merge (A1_, A2_) [] l2 = l2
  | merge (A1_, A2_) (v :: va) [] = v :: va
  | merge (A1_, A2_) (x1 :: l1) (x2 :: l2) =
    (if less ((ord_preorder o preorder_order o order_linorder) A2_) x1 x2
      then x1 :: merge (A1_, A2_) l1 (x2 :: l2)
      else (if eq A1_ x1 x2 then x1 :: merge (A1_, A2_) l1 l2
             else x2 :: merge (A1_, A2_) (x1 :: l1) l2));

fun join [] a = []
  | join (x :: xs) a = x :: a :: join xs a;

val mulog_property : exp ltlc =
  Global_ltlc (Prop_ltlc (E_bin (Bo_less_eq, E_var "x", E_const one_inta)));

val mulog_processes : string list = ["A", "B"];

fun mulog_process_name i =
  (if equal_nata i zero_nata then "unknown"
    else nth mulog_processes (minus_nat i one_nata));

fun mulog_handshake i = mulog_process_name i ^ "h";

fun handshake_receiver n = n ^ "r";

fun handshake_received n = n ^ "c";

fun handshake_message n = n ^ "m";

fun handshake_sender n = n ^ "s";

fun handshake_sent n = n ^ "n";

fun lock_lock n = n ^ "l";

fun lock_vars n = [lock_lock n];

fun handshake_vars n =
  maps lock_vars [handshake_sender n, handshake_receiver n] @
    [handshake_message n, handshake_sent n, handshake_received n];

fun mulog_vars_global i = handshake_vars (mulog_handshake i);

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length zero_nata x;

val mulog_process_ids : nat list =
  upt one_nata (suc (size_list mulog_processes));

fun mulog_requesting i = mulog_process_name i ^ "r";

fun mulog_parent i = mulog_process_name i ^ "p";

fun assignc c v e = Assign (c, v, e);

val efalse : exp = E_const zero_int;

val etrue : exp = E_const one_inta;

fun assign v e = Assign (etrue, v, e);

fun lock_block n c =
  Seqa (assignc (nota (var (lock_lock n))) (lock_lock n) etrue,
         Seqa (c, assign (lock_lock n) efalse));

fun wait c = Test c;

fun handshake_send n m =
  lock_block (handshake_sender n)
    (Seqa (assign (handshake_message n) m,
            Seqa (assign (handshake_sent n) etrue,
                   Seqa (wait (var (handshake_received n)),
                          assign (handshake_received n) efalse))));

fun ifelse c c1 c2 = Or (Seqa (Test c, c1), Seqa (Test (nota c), c2));

fun mulog_send_aux n proc msg =
  (if equal_nata n zero_nata then Skip
    else ifelse
           (E_bin
             (Bo_eq, proc, E_const (int_of_nat (suc (minus_nat n one_nata)))))
           (handshake_send (mulog_handshake (suc (minus_nat n one_nata))) msg)
           (mulog_send_aux (minus_nat n one_nata) proc msg));

fun mulog_send x = mulog_send_aux (size_list mulog_processes) x;

fun mulog_request_token i =
  Seqa (assign (mulog_requesting i) etrue,
         ifelse (E_bin (Bo_eq, var (mulog_parent i), E_const zero_int)) Skip
           (Seqa (mulog_send (var (mulog_parent i)) (E_const (int_of_nat i)),
                   assign (mulog_parent i) (E_const zero_int))));

fun mulog_token i = mulog_process_name i ^ "t";

fun mulog_next i = mulog_process_name i ^ "n";

fun mulog_release_token i =
  Seqa (assign (mulog_requesting i) efalse,
         ifelse (E_bin (Bo_eq, var (mulog_next i), E_const zero_int)) Skip
           (Seqa (assign (mulog_token i) efalse,
                   Seqa (mulog_send (var (mulog_next i)) (E_const zero_int),
                          assign (mulog_next i) (E_const zero_int)))));

fun handshake_waiting n = var (handshake_sent n);

fun handshake_receive n m =
  lock_block (handshake_receiver n)
    (Seqa (wait (var (handshake_sent n)),
            Seqa (assign (handshake_sent n) efalse,
                   Seqa (assign m (var (handshake_message n)),
                          assign (handshake_received n) etrue))));

fun lock_initialize n = assign (lock_lock n) efalse;

fun handshake_initialize n =
  Seqa (lock_initialize (handshake_sender n),
         Seqa (lock_initialize (handshake_receiver n),
                Seqa (assign (handshake_message n) (E_const zero_int),
                       Seqa (assign (handshake_sent n) efalse,
                              assign (handshake_received n) efalse))));

fun mulog_idle i = mulog_process_name i ^ "i";

fun mulog_msg i = mulog_process_name i ^ "m";

fun mulog_initialize i =
  Seqa (handshake_initialize (mulog_handshake i),
         Seqa (assign (mulog_msg i) (E_const zero_int),
                Seqa (assign (mulog_idle i) etrue,
                       Seqa (assign (mulog_parent i)
                               (if equal_nata i one_nata then E_const zero_int
                                 else E_const one_inta),
                              Seqa (assign (mulog_next i) (E_const zero_int),
                                     Seqa (assign (mulog_requesting i) efalse,
    assign (mulog_token i)
      (if equal_nata i one_nata then etrue else efalse)))))));

fun loop cmd = Iterate (cmd, cmd);

fun mulog_process_cmd i =
  Seqa (mulog_initialize i,
         loop (ifelse (handshake_waiting (mulog_handshake i))
                (Seqa (handshake_receive (mulog_handshake i) (mulog_msg i),
                        ifelse
                          (E_bin (Bo_eq, var (mulog_msg i), E_const zero_int))
                          (assign (mulog_token i) etrue)
                          (Seqa (ifelse
                                   (E_bin
                                     (Bo_eq, var (mulog_parent i),
                                       E_const zero_int))
                                   (ifelse (var (mulog_requesting i))
                                     (assign (mulog_next i) (var (mulog_msg i)))
                                     (Seqa (assign (mulog_token i) efalse,
     mulog_send (var (mulog_msg i)) (E_const zero_int))))
                                   (mulog_send (var (mulog_parent i))
                                     (var (mulog_msg i))),
                                  assign (mulog_parent i)
                                    (var (mulog_msg i))))))
                (ifelse (var (mulog_idle i))
                  (Seqa (assign (mulog_idle i) efalse, mulog_request_token i))
                  (ifelse (var (mulog_token i))
                    (Seqa (assign "x"
                             (E_bin (Bo_plus, var "x", E_const one_inta)),
                            Seqa (assign "x"
                                    (E_bin
                                      (Bo_minus, var "x", E_const one_inta)),
                                   Seqa (mulog_release_token i,
  assign (mulog_idle i) etrue))))
                    Skip))));

fun mulog_vars_local i =
  [mulog_msg i, mulog_idle i, mulog_token i, mulog_requesting i, mulog_parent i,
    mulog_next i];

fun mulog_process i =
  Proc_decl_ext
    (mulog_process_name i, mulog_process_cmd i, mulog_vars_local i, ());

val mulog_program : unit program_ext =
  Program_ext
    (map mulog_process mulog_process_ids,
      "x" :: maps mulog_vars_global mulog_process_ids, ());

val dflt_cfg : config_l2b * (unit * config_ce) =
  (CFG_L2B_GERTHS, ((), CFG_CE_SCC_GABOW));

fun ltlc_next_free True_ltlc = true
  | ltlc_next_free False_ltlc = true
  | ltlc_next_free (Prop_ltlc q) = true
  | ltlc_next_free (Not_ltlc phi) = ltlc_next_free phi
  | ltlc_next_free (And_ltlc (phi, psi)) =
    ltlc_next_free phi andalso ltlc_next_free psi
  | ltlc_next_free (Or_ltlc (phi, psi)) =
    ltlc_next_free phi andalso ltlc_next_free psi
  | ltlc_next_free (Implies_ltlc (phi, psi)) =
    ltlc_next_free phi andalso ltlc_next_free psi
  | ltlc_next_free (Next_ltlc phi) = false
  | ltlc_next_free (Final_ltlc phi) = ltlc_next_free phi
  | ltlc_next_free (Global_ltlc phi) = ltlc_next_free phi
  | ltlc_next_free (Until_ltlc (phi, psi)) =
    ltlc_next_free phi andalso ltlc_next_free psi
  | ltlc_next_free (Release_ltlc (phi, psi)) =
    ltlc_next_free phi andalso ltlc_next_free psi;

fun balance (Branch (R, a, w, x, b)) s t (Branch (R, c, y, z, d)) =
  Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z Empty =
    Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, a, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z Empty =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance
    (Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c))) y z
    Empty =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance
    (Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance Empty w x (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, d))
  | balance Empty w x (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance Empty w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
  | balance Empty s t Empty = Branch (B, Empty, s, t, Empty)
  | balance Empty s t (Branch (B, va, vb, vc, vd)) =
    Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
  | balance Empty s t (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
  | balance Empty s t (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch
      (B, Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | balance Empty s t (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch
      (B, Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance Empty s t
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, Empty, s, t,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance (Branch (B, va, vb, vc, vd)) s t Empty =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (B, ve, vf, vg, vh)) =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (v, Empty, vf, vg, Empty))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t,
          Branch
            (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (v, Empty, vb, vc, Empty)) s t Empty =
    Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
  | balance (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) s t Empty =
    Branch
      (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty)
  | balance (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) s t Empty =
    Branch
      (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty)
  | balance
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    s t Empty =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty)
  | balance (Branch (v, Empty, vf, vg, Empty)) s t (Branch (B, va, vb, vc, vd))
    = Branch
        (B, Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl))) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty)) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd))
  | balance
    (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)))
    s t (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch
            (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd));

fun rbt_insa A_ f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_insa A_ f k v (Branch (B, l, x, y, r)) =
    (if less A_ k x then balance (rbt_insa A_ f k v l) x y r
      else (if less A_ x k then balance l x y (rbt_insa A_ f k v r)
             else Branch (B, l, x, f k y v, r)))
  | rbt_insa A_ f k v (Branch (R, l, x, y, r)) =
    (if less A_ k x then Branch (R, rbt_insa A_ f k v l, x, y, r)
      else (if less A_ x k then Branch (R, l, x, y, rbt_insa A_ f k v r)
             else Branch (R, l, x, f k y v, r)));

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun rbt_insert_with_keya A_ f k v t = paint B (rbt_insa A_ f k v t);

fun rbt_inserta A_ = rbt_insert_with_keya A_ (fn _ => fn _ => fn nv => nv);

fun insert A_ xc xd xe =
  RBT (rbt_inserta ((ord_preorder o preorder_order o order_linorder) A_) xc xd
        (impl_of A_ xe));

fun updatea A_ k v (Mapping t) = Mapping (insert A_ k v t);

fun vi_update x = updatea linorder_literal x;

fun emptya A_ = Mapping (empty A_);

val vi_empty : (string, Word32.word) mapping = emptya linorder_literal;

fun init_valuation_impl vd =
  fold (fn x => vi_update x (Word32.fromInt 0)) vd vi_empty;

fun local_vars (Proc_decl_ext (name, body, local_vars, more)) = local_vars;

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun cr_index_of A_ [] x = NONE
  | cr_index_of A_ (a :: l) x =
    (if eq A_ x a then SOME zero_nata else map_option suc (cr_index_of A_ l x));

fun the (SOME x2) = x2;

fun comp_gamma_impl cinf c = the (cr_index_of equal_cmd (fst cinf) c);

fun body (Proc_decl_ext (name, body, local_vars, more)) = body;

fun init_pc_impl_impl mst pd =
  Local_config_ext
    (comp_gamma_impl mst (body pd),
      Local_state_impl_ext (init_valuation_impl (local_vars pd), ()), ());

fun global_vars (Program_ext (processes, global_vars, more)) = global_vars;

fun processes (Program_ext (processes, global_vars, more)) = processes;

fun pid_init_gc_impl_impl prog mst =
  Pid_global_config_ext
    (map (init_pc_impl_impl mst) (processes prog),
      Global_state_impl_ext (init_valuation_impl (global_vars prog), ()), ());

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun nat_of_hashcode x = nat_of_uint32 x;

fun bounded_hashcode_nat A_ n x =
  modulo_nata (nat_of_hashcode (hashcode A_ x)) n;

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun stutter_extend_en_list x =
  (fn xa => fn xaa => let
                        val y = xa xaa;
                      in
                        (if is_Nil y then [NONE] else map SOME y)
                      end)
    x;

fun collecti_index_list i a c [] = a
  | collecti_index_list i a c (x :: xs) =
    (case c i x of (true, s) => map (fn aa => (i, aa)) s
      | (false, s) =>
        collecti_index_list (suc i) (a @ map (fn aa => (i, aa)) s) c xs);

val bot_set : 'a set = Set [];

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun insertb A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun inserta A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | inserta A_ x (Set xs) = Set (insertb A_ x xs);

fun write_globals (AAssign (uu, x, uv)) = inserta equal_literal x bot_set
  | write_globals (AAssign_local (uw, ux, uy)) = bot_set
  | write_globals (AAssign_global (uz, x, va)) = inserta equal_literal x bot_set
  | write_globals (ATest e) = bot_set
  | write_globals ASkip = bot_set;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (inserta A_) xs a;

fun udvars_of_exp (E_var x) = inserta equal_literal x bot_set
  | udvars_of_exp (E_localvar x) = bot_set
  | udvars_of_exp (E_globalvar x) = bot_set
  | udvars_of_exp (E_const c) = bot_set
  | udvars_of_exp (E_bin (bop, e1, e2)) =
    sup_set equal_literal (udvars_of_exp e1) (udvars_of_exp e2)
  | udvars_of_exp (E_un (uop, e)) = udvars_of_exp e;

fun gvars_of_exp (E_var x) = bot_set
  | gvars_of_exp (E_localvar x) = bot_set
  | gvars_of_exp (E_globalvar x) = inserta equal_literal x bot_set
  | gvars_of_exp (E_const c) = bot_set
  | gvars_of_exp (E_bin (bop, e1, e2)) =
    sup_set equal_literal (gvars_of_exp e1) (gvars_of_exp e2)
  | gvars_of_exp (E_un (uop, e)) = gvars_of_exp e;

fun read_globals (AAssign (c, uu, e)) =
  sup_set equal_literal
    (sup_set equal_literal
      (sup_set equal_literal (gvars_of_exp c) (udvars_of_exp c))
      (gvars_of_exp e))
    (udvars_of_exp e)
  | read_globals (AAssign_local (c, uv, e)) =
    sup_set equal_literal
      (sup_set equal_literal
        (sup_set equal_literal (gvars_of_exp c) (udvars_of_exp c))
        (gvars_of_exp e))
      (udvars_of_exp e)
  | read_globals (AAssign_global (c, uw, e)) =
    sup_set equal_literal
      (sup_set equal_literal
        (sup_set equal_literal (gvars_of_exp c) (udvars_of_exp c))
        (gvars_of_exp e))
      (udvars_of_exp e)
  | read_globals (ATest e) =
    sup_set equal_literal (gvars_of_exp e) (udvars_of_exp e)
  | read_globals ASkip = bot_set;

fun bool_of_val_impl v = not ((v : Word32.word) = (Word32.fromInt 0));

fun val_of_bool_impl b = (if b then (Word32.fromInt 1) else (Word32.fromInt 0));

fun divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

fun abs_int i = (if less_int i zero_int then uminus_int i else i);

fun word_of_int A_ x = Word (bitAND_int x (bin_mask (len_of A_ Type)));

fun word_sdiv A_ x y =
  let
    val xa = sint A_ x;
    val ya = sint A_ y;
    val negative =
      not (equal_bool (less_int xa zero_int) (less_int ya zero_int));
    val result = divide_int (abs_int xa) (abs_int ya);
  in
    word_of_int (len0_len A_) (if negative then uminus_int result else result)
  end;

fun test_bit_uint32 x n =
  less_nat n (nat_of_integer (32 : IntInf.int)) andalso
    Uint32.test_bit x (integer_of_nat n);

fun bl_of_nth n f =
  (if equal_nata n zero_nata then []
    else f (minus_nat n one_nata) :: bl_of_nth (minus_nat n one_nata) f);

fun bl_to_bin_aux [] w = w
  | bl_to_bin_aux (b :: bs) w = bl_to_bin_aux bs (bit w b);

fun bl_to_bin bs = bl_to_bin_aux bs zero_int;

fun of_bl A_ bl = word_of_int A_ (bl_to_bin bl);

fun set_bits_word A_ f = of_bl A_ (bl_of_nth (len_of A_ Type) f);

fun rep_uint32 x =
  set_bits_word
    (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
    (test_bit_uint32 x);

fun abs_uint32 x =
  Word32.fromLargeInt (IntInf.toLarge (integer_of_int
(uint (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
  x)));

fun sdiv_impl x y =
  abs_uint32
    (word_sdiv (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
      (rep_uint32 x) (rep_uint32 y));

fun smod_impl a b = Word32.- (a, Word32.* (sdiv_impl a b, b));

fun eval_bin_op_impl_aux Bo_plus v1 v2 = Word32.+ (v1, v2)
  | eval_bin_op_impl_aux Bo_minus v1 v2 = Word32.- (v1, v2)
  | eval_bin_op_impl_aux Bo_mul v1 v2 = Word32.* (v1, v2)
  | eval_bin_op_impl_aux Bo_div v1 v2 = sdiv_impl v1 v2
  | eval_bin_op_impl_aux Bo_mod v1 v2 = smod_impl v1 v2
  | eval_bin_op_impl_aux Bo_less v1 v2 = val_of_bool_impl (Word32.< (v1, v2))
  | eval_bin_op_impl_aux Bo_less_eq v1 v2 =
    val_of_bool_impl (Word32.<= (v1, v2))
  | eval_bin_op_impl_aux Bo_eq v1 v2 =
    val_of_bool_impl ((v1 : Word32.word) = v2)
  | eval_bin_op_impl_aux Bo_and v1 v2 = Word32.andb (v1, v2)
  | eval_bin_op_impl_aux Bo_or v1 v2 = Word32.orb (v1, v2)
  | eval_bin_op_impl_aux Bo_xor v1 v2 = Word32.xorb (v1, v2);

fun eval_bin_op_impl bop v1 v2 = eval_bin_op_impl_aux bop v1 v2;

fun eval_un_op_impl_aux Uo_minus v = Word32.~ v
  | eval_un_op_impl_aux Uo_not v = Word32.notb v;

fun eval_un_op_impl uop v = eval_un_op_impl_aux uop v;

fun assert_option true = SOME ()
  | assert_option false = NONE;

fun vi_lookup x = lookupa linorder_literal x;

fun power A_ a n =
  (if equal_nata n zero_nata then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nat n one_nata)));

val min_signed : int =
  uminus_int
    (power power_int (Int_of_integer (2 : IntInf.int))
      (minus_nat
        (len_of_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
          Type)
        one_nata));

val max_signed : int =
  minus_int
    (power power_int (Int_of_integer (2 : IntInf.int))
      (minus_nat
        (len_of_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
          Type)
        one_nata))
    one_inta;

fun binda NONE f = NONE
  | binda (SOME x) f = f x;

fun eval_exp_impl (E_var x) (ls, gs) =
  let
    val lv = variables ls;
    val gv = variablesa gs;
  in
    (case vi_lookup lv x
      of NONE => (case vi_lookup gv x of NONE => NONE | SOME a => SOME a)
      | SOME a => SOME a)
  end
  | eval_exp_impl (E_localvar x) (ls, gs) = vi_lookup (variables ls) x
  | eval_exp_impl (E_globalvar x) (ls, gs) = vi_lookup (variablesa gs) x
  | eval_exp_impl (E_const n) fs =
    binda (assert_option
            (less_eq_int min_signed n andalso less_eq_int n max_signed))
      (fn _ => SOME (uint32_of_int n))
  | eval_exp_impl (E_bin (bop, e1, e2)) fs =
    binda (eval_exp_impl e1 fs)
      (fn v1 =>
        binda (eval_exp_impl e2 fs)
          (fn v2 => SOME (eval_bin_op_impl bop v1 v2)))
  | eval_exp_impl (E_un (uop, e)) fs =
    binda (eval_exp_impl e fs) (fn v => SOME (eval_un_op_impl uop v));

fun la_en_impl fs (AAssign (e, uu, uv)) =
  binda (eval_exp_impl e fs) (fn v => SOME (bool_of_val_impl v))
  | la_en_impl fs (AAssign_local (e, uw, ux)) =
    binda (eval_exp_impl e fs) (fn v => SOME (bool_of_val_impl v))
  | la_en_impl fs (AAssign_global (e, uy, uz)) =
    binda (eval_exp_impl e fs) (fn v => SOME (bool_of_val_impl v))
  | la_en_impl fs (ATest e) =
    binda (eval_exp_impl e fs) (fn v => SOME (bool_of_val_impl v))
  | la_en_impl va ASkip = SOME true;

fun la_en_impla fs a = (case la_en_impl fs a of NONE => false | SOME b => b);

fun length asa = nat_of_integer (Vector.length asa);

fun ccfg_succ_impl cinf c =
  let
    val mst = snd cinf;
  in
    (if less_nat c (length mst) then sub mst c else [])
  end;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

val top_set : 'a set = Coset [];

fun of_phantom (Phantom x) = x;

fun card (A1_, A2_) (Coset xs) =
  minus_nat (of_phantom (card_UNIV A1_)) (size_list (remdups A2_ xs))
  | card (A1_, A2_) (Set xs) = size_list (remdups A2_ xs);

fun eq_set (A1_, A2_) (Coset xs) (Coset ys) =
  list_all (membera A2_ ys) xs andalso list_all (membera A2_ xs) ys
  | eq_set (A1_, A2_) (Set xs) (Set ys) =
    list_all (membera A2_ ys) xs andalso list_all (membera A2_ xs) ys
  | eq_set (A1_, A2_) (Set ys) (Coset xs) =
    let
      val n = card (A1_, A2_) top_set;
    in
      (if equal_nata n zero_nata then false
        else let
               val xsa = remdups A2_ xs;
               val ysa = remdups A2_ ys;
             in
               equal_nata (plus_nata (size_list xsa) (size_list ysa)) n andalso
                 (list_all (fn x => not (membera A2_ ysa x)) xsa andalso
                   list_all (fn y => not (membera A2_ xsa y)) ysa)
             end)
    end
  | eq_set (A1_, A2_) (Coset xs) (Set ys) =
    let
      val n = card (A1_, A2_) top_set;
    in
      (if equal_nata n zero_nata then false
        else let
               val xsa = remdups A2_ xs;
               val ysa = remdups A2_ ys;
             in
               equal_nata (plus_nata (size_list xsa) (size_list ysa)) n andalso
                 (list_all (fn x => not (membera A2_ ysa x)) xsa andalso
                   list_all (fn y => not (membera A2_ xsa y)) ysa)
             end)
    end;

fun ga_gample_mil4_impl mst mem sticky_Ei gc =
  let
    val lcs = processesa gc;
    val gs = statea gc;
  in
    collecti_index_list zero_nata []
      (fn _ => fn lc =>
        let
          val c = command lc;
          val ls = state lc;
          val asa = ccfg_succ_impl mst c;
          val s = filter (la_en_impla (ls, gs) o fst) asa;
          val ample =
            not (null s) andalso
              (list_all
                 (fn (a, _) =>
                   eq_set (card_UNIV_literal, equal_literal) (read_globals a)
                     bot_set andalso
                     eq_set (card_UNIV_literal, equal_literal) (write_globals a)
                       bot_set)
                 asa andalso
                list_all (fn (_, ca) => not (mem (c, ca) sticky_Ei)) s);
        in
          (ample, map (fn a => (c, a)) s)
        end)
      lcs
  end;

fun set_iterator_image g it = (fn c => fn f => it c (fn x => f (g x)));

fun map_iterator_dom it = set_iterator_image fst it;

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

fun array_length x = (nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun array_set a = FArray.IsabelleMapping.array_set a o integer_of_nat;

fun array_get a = FArray.IsabelleMapping.array_get a o integer_of_nat;

fun is_none (SOME x) = false
  | is_none NONE = true;

fun ahm_update_auxa eq bhc (HashMapb (a, n)) k v =
  let
    val h = bhc (array_length a) k;
    val m = array_get a h;
    val insert = is_none (list_map_lookup eq k m);
  in
    HashMapb
      (array_set a h (list_map_update eq k v m),
        (if insert then plus_nata n one_nata else n))
  end;

fun idx_iteratei_aux get sz i l c f sigma =
  (if equal_nata i zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux get sz (minus_nat i one_nata) l c f
           (f (get l (minus_nat sz i)) sigma));

fun idx_iteratei get sz l c f sigma =
  idx_iteratei_aux get (sz l) (sz l) l c f sigma;

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun ahm_iteratei_auxa a c f sigma =
  idx_iteratei array_get array_length a c (fn x => foldli x c f) sigma;

fun ahm_rehash_auxc bhc n kv a = let
                                   val h = bhc n (fst kv);
                                 in
                                   array_set a h (kv :: array_get a h)
                                 end;

fun new_array v = FArray.IsabelleMapping.new_array v o integer_of_nat;

fun ahm_rehash_auxb bhc a sz =
  ahm_iteratei_auxa a (fn _ => true) (ahm_rehash_auxc bhc sz) (new_array [] sz);

fun ahm_rehasha bhc (HashMapb (a, n)) sz =
  HashMapb (ahm_rehash_auxb bhc a sz, n);

val load_factora : nat = nat_of_integer (75 : IntInf.int);

fun ahm_filleda (HashMapb (a, n)) =
  less_eq_nat (times_nata (array_length a) load_factora)
    (times_nata n (nat_of_integer (100 : IntInf.int)));

fun hm_growa (HashMapb (a, n)) =
  plus_nata (times_nata (nat_of_integer (2 : IntInf.int)) (array_length a))
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

fun array_grow a = FArray.IsabelleMapping.array_grow a o integer_of_nat;

fun ras_push x s =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if equal_nata n (array_length aa)
        then array_grow aa
               (max ord_nat (nat_of_integer (4 : IntInf.int))
                 (times_nata (nat_of_integer (2 : IntInf.int)) n))
               x
        else aa);
    val ac = array_set ab n x;
  in
    (ac, plus_nata n one_nata)
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
      (if less_eq_nat (times_nata (nat_of_integer (128 : IntInf.int)) n)
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

fun rev_append [] ac = ac
  | rev_append (x :: xs) ac = rev_append xs (x :: ac);

fun glist_delete_aux eq x [] asa = asa
  | glist_delete_aux eq x (y :: ys) asa =
    (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y :: asa));

fun glist_delete eq x l = glist_delete_aux eq x l [];

fun map2set_insert i k s = i k () s;

fun map2set_memb l k s = (case l k s of NONE => false | SOME _ => true);

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun gen_pick it s =
  the (it s (fn a => (case a of NONE => true | SOME _ => false))
         (fn x => fn _ => SOME x)
        NONE);

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
                         (fn xc =>
                           not false andalso
                             not (ras_is_empty (ssnos_stack_impl xc)))
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

fun ahm_iteratei (HashMapb (a, n)) = ahm_iteratei_auxa a;

fun gi_V (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_V;

fun prod_eq eqa eqb x1 x2 = let
                              val (a1, b1) = x1;
                              val (a2, b2) = x2;
                            in
                              eqa a1 a2 andalso eqb b1 b2
                            end;

fun ss_on_stack_impl_update ss_on_stack_impla
  (Simple_state_impl_ext
    (ss_stack_impl, ss_on_stack_impl, ss_visited_impl, more))
  = Simple_state_impl_ext
      (ss_stack_impl, ss_on_stack_impla ss_on_stack_impl, ss_visited_impl,
        more);

fun ss_visited_impl_update ss_visited_impla
  (Simple_state_impl_ext
    (ss_stack_impl, ss_on_stack_impl, ss_visited_impl, more))
  = Simple_state_impl_ext
      (ss_stack_impl, ss_on_stack_impl, ss_visited_impla ss_visited_impl, more);

fun ss_stack_impl_update ss_stack_impla
  (Simple_state_impl_ext
    (ss_stack_impl, ss_on_stack_impl, ss_visited_impl, more))
  = Simple_state_impl_ext
      (ss_stack_impla ss_stack_impl, ss_on_stack_impl, ss_visited_impl, more);

fun ss_on_stack_impl
  (Simple_state_impl_ext
    (ss_stack_impl, ss_on_stack_impl, ss_visited_impl, more))
  = ss_on_stack_impl;

fun ss_visited_impl
  (Simple_state_impl_ext
    (ss_stack_impl, ss_on_stack_impl, ss_visited_impl, more))
  = ss_visited_impl;

fun ss_stack_impl
  (Simple_state_impl_ext
    (ss_stack_impl, ss_on_stack_impl, ss_visited_impl, more))
  = ss_stack_impl;

fun more_update morea
  (Simple_state_impl_ext
    (ss_stack_impl, ss_on_stack_impl, ss_visited_impl, more))
  = Simple_state_impl_ext
      (ss_stack_impl, ss_on_stack_impl, ss_visited_impl, morea more);

fun fas_impl
  (Simple_state_impl_ext
    (ss_stack_impl, ss_on_stack_impl, ss_visited_impl,
      Fas_state_impl_ext (fas_impl, more)))
  = fas_impl;

fun morea
  (Simple_state_impl_ext
    (ss_stack_impl, ss_on_stack_impl, ss_visited_impl, more))
  = more;

fun list_map_delete_aux eq k [] accu = accu
  | list_map_delete_aux eq k (x :: xs) accu =
    (if eq (fst x) k then xs @ accu
      else list_map_delete_aux eq k xs (x :: accu));

fun list_map_delete eq k m = list_map_delete_aux eq k m [];

fun ahm_deleteb eq bhc k (HashMapb (a, n)) =
  let
    val h = bhc (array_length a) k;
    val m = array_get a h;
    val deleted = not (is_none (list_map_lookup eq k m));
  in
    HashMapb
      (array_set a h (list_map_delete eq k m),
        (if deleted then minus_nat n one_nata else n))
  end;

fun the_res (DRETURN x) = x;

fun dbind DFAILi f = DFAILi
  | dbind DSUCCEEDi f = DSUCCEEDi
  | dbind (DRETURN x) f = f x;

fun dWHILET b f s = (if b s then dbind (f s) (dWHILET b f) else DRETURN s);

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

fun prod_bhc (A1_, A2_) bhc1 bhc2 =
  (fn n => fn (a, b) =>
    modulo A2_
      (plus ((plus_semigroup_add o semigroup_add_numeral) A1_)
        (times ((times_dvd o dvd_modulo) A2_) (bhc1 n a)
          (numeral A1_ (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
        (bhc2 n b))
      n);

fun gen_diff del1 it2 s1 s2 = it2 s2 (fn _ => true) del1 s1;

fun find_fas_code eq bhc sz gi =
  the_res
    (dbind
      (foldli (gi_V0 gi)
        (fn a =>
          (case a of DSUCCEEDi => false | DFAILi => false
            | DRETURN _ => not false))
        (fn x => fn s =>
          dbind s
            (fn sigma =>
              let
                val _ = sigma;
              in
                (if map2set_memb (ahm_lookupb eq bhc) x (ss_visited_impl sigma)
                  then DRETURN sigma
                  else dbind let
                               val xc =
                                 ss_stack_impl_update
                                   (fn _ =>
                                     ras_singleton one_nat (x, gi_E gi x))
                                   sigma;
                               val xd =
                                 ss_on_stack_impl_update
                                   (fn _ =>
                                     map2set_insert (ahm_updateb eq bhc) x
                                       (ahm_emptyb sz))
                                   xc;
                             in
                               DRETURN
                                 (ss_visited_impl_update
                                   (fn _ =>
                                     map2set_insert (ahm_updateb eq bhc) x
                                       (ss_visited_impl xd))
                                   xd)
                             end
                         (fn xa =>
                           dWHILET
                             (fn xc =>
                               not false andalso
                                 not (ras_is_empty (ss_stack_impl xc)))
                             (fn xd =>
                               dbind let
                                       val a = ras_top (ss_stack_impl xd);
                                       val (aa, b) = a;
                                     in
                                       (if is_Nil b
 then DRETURN (aa, (NONE, xd))
 else let
        val xg = glist_delete eq (gen_pick foldli b) b;
        val xh =
          ss_stack_impl_update
            (fn _ => ras_push (aa, xg) (ras_pop (ss_stack_impl xd))) xd;
      in
        DRETURN (aa, (SOME (gen_pick foldli b), xh))
      end)
                                     end
                                 (fn a =>
                                   (case a
                                     of (aa, (NONE, ba)) =>
                                       dbind
 let
   val xf = ss_stack_impl_update (fn _ => ras_pop (ss_stack_impl ba)) ba;
 in
   DRETURN
     (ss_on_stack_impl_update
       (fn _ => ahm_deleteb eq bhc aa (ss_on_stack_impl xf)) xf)
 end
 (fn xf => DRETURN (more_update (fn _ => morea xf) xf))
                                     | (aa, (SOME xf, ba)) =>
                                       (if map2set_memb (ahm_lookupb eq bhc) xf
     (ss_visited_impl ba)
 then (if map2set_memb (ahm_lookupb eq bhc) xf
            (gen_diff (ahm_deleteb eq bhc) (map_iterator_dom o ahm_iteratei)
              (ss_visited_impl ba) (ss_on_stack_impl ba))
        then DRETURN (more_update (fn _ => morea ba) ba)
        else DRETURN
               (more_update
                 (fn _ =>
                   Fas_state_impl_ext
                     (map2set_insert
                        (ahm_updateb (prod_eq eq eq)
                          (prod_bhc (numeral_nat, modulo_nat) bhc bhc))
                        (aa, xf) (fas_impl ba),
                       ()))
                 ba))
 else dbind let
              val xg =
                ss_stack_impl_update
                  (fn _ => ras_push (xf, gi_E gi xf) (ss_stack_impl ba)) ba;
              val xh =
                ss_on_stack_impl_update
                  (fn _ =>
                    map2set_insert (ahm_updateb eq bhc) xf
                      (ss_on_stack_impl xg))
                  xg;
            in
              DRETURN
                (ss_visited_impl_update
                  (fn _ =>
                    map2set_insert (ahm_updateb eq bhc) xf (ss_visited_impl xh))
                  xh)
            end
        (fn xg => DRETURN (more_update (fn _ => morea xg) xg))))))
                             (more_update (fn _ => morea xa) xa)))
              end))
        (DRETURN
          (Simple_state_impl_ext
            (ras_empty zero_nat (), ahm_emptyb sz, ahm_emptyb sz,
              Fas_state_impl_ext (ahm_emptyb (plus_nata sz sz), ())))))
      (fn x => DRETURN (fas_impl x)));

fun glist_member eq x [] = false
  | glist_member eq x (y :: ys) = eq x y orelse glist_member eq x ys;

fun glist_insert eq x xs = (if glist_member eq x xs then xs else x :: xs);

fun gen_union it ins a b = it a (fn _ => true) ins b;

fun find_fas_init_code eq bhc sz gi fIi =
  let
    val x =
      gen_union (map_iterator_dom o ahm_iteratei) (glist_insert eq)
        (find_reachable_codeT eq bhc sz gi) [];
    val xa =
      find_fas_code eq bhc sz
        (Gen_g_impl_ext
          (gi_V gi,
            (fn xa => filter (fn xc => not (fIi (xa, xc))) (gi_E gi xa)), x,
            ()));
  in
    (fn xb =>
      fIi xb orelse
        map2set_memb
          (ahm_lookupb (prod_eq eq eq)
            (prod_bhc (numeral_nat, modulo_nat) bhc bhc))
          xb xa)
  end;

fun is_vis_edge_impl mst is_vis_var =
  (fn (c, ca) =>
    list_ex
      (fn (a, cc) => equal_nata ca cc andalso bex (write_globals a) is_vis_var)
      (ccfg_succ_impl mst c));

fun ccfg_E_succ_impl mst = remdups equal_nat o map snd o ccfg_succ_impl mst;

fun cfg_V0_list prog = remdups equal_cmd (map body (processes prog));

fun ccfg_V0_impl prog mst = map (comp_gamma_impl mst) (cfg_V0_list prog);

fun ccfg_G_impl_impl prog mst =
  Gen_g_impl_ext
    ((fn _ => true), ccfg_E_succ_impl mst, ccfg_V0_impl prog mst, ());

fun cr_ample_impl4_impl prog mst is_vis_var =
  let
    val sticky =
      find_fas_init_code equal_nata (bounded_hashcode_nat hashable_nat)
        (def_hashmap_size_nat Type) (ccfg_G_impl_impl prog mst)
        (is_vis_edge_impl mst is_vis_var);
  in
    stutter_extend_en_list
      (ga_gample_mil4_impl mst (fn x => fn f => f x) sticky)
  end;

fun gen_image it1 emp2 ins2 f s1 =
  it1 s1 (fn _ => true) (fn x => ins2 (f x)) emp2;

fun succ_of_enex_list C_ =
  (fn x => fn xa =>
    let
      val (xb, xc) = x;
    in
      gen_image (fn xd => foldli (id xd)) [] (glist_insert (eq C_))
        (fn xd => xc xd xa) (xb xa)
    end);

fun stutter_extend_ex ex = (fn a => (case a of NONE => id | SOME aa => ex aa));

fun variables_updatea variablesa (Global_state_impl_ext (variables, more)) =
  Global_state_impl_ext (variablesa variables, more);

fun variables_update variablesa (Local_state_impl_ext (variables, more)) =
  Local_state_impl_ext (variablesa variables, more);

fun la_ex_impl (ls, gs) (AAssign (ge, x, e)) =
  binda (eval_exp_impl ge (ls, gs))
    (fn v =>
      binda (assert_option (bool_of_val_impl v))
        (fn _ =>
          binda (eval_exp_impl e (ls, gs))
            (fn va =>
              (if not (is_none (vi_lookup (variables ls) x))
                then let
                       val lsa = variables_update (vi_update x va) ls;
                     in
                       SOME (lsa, gs)
                     end
                else binda (assert_option
                             (not (is_none (vi_lookup (variablesa gs) x))))
                       (fn _ =>
                         let
                           val gsa = variables_updatea (vi_update x va) gs;
                         in
                           SOME (ls, gsa)
                         end)))))
  | la_ex_impl (ls, gs) (AAssign_local (ge, x, e)) =
    binda (eval_exp_impl ge (ls, gs))
      (fn v =>
        binda (assert_option (bool_of_val_impl v))
          (fn _ =>
            binda (eval_exp_impl e (ls, gs))
              (fn va =>
                binda (assert_option
                        (not (is_none (vi_lookup (variables ls) x))))
                  (fn _ => let
                             val lsa = variables_update (vi_update x va) ls;
                           in
                             SOME (lsa, gs)
                           end))))
  | la_ex_impl (ls, gs) (AAssign_global (ge, x, e)) =
    binda (eval_exp_impl ge (ls, gs))
      (fn v =>
        binda (assert_option (bool_of_val_impl v))
          (fn _ =>
            binda (eval_exp_impl e (ls, gs))
              (fn va =>
                binda (assert_option
                        (not (is_none (vi_lookup (variablesa gs) x))))
                  (fn _ =>
                    let
                      val gsa = variables_updatea (vi_update x va) gs;
                    in
                      SOME (ls, gsa)
                    end))))
  | la_ex_impl fs (ATest e) =
    binda (eval_exp_impl e fs)
      (fn v => binda (assert_option (bool_of_val_impl v)) (fn _ => SOME fs))
  | la_ex_impl fs ASkip = SOME fs;

fun la_ex_impla fs a = (case la_ex_impl fs a of NONE => fs | SOME fsa => fsa);

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if equal_nata i zero_nata then y :: xs
      else x :: list_update xs (minus_nat i one_nata) y);

fun ga_gex_impl ga gc =
  let
    val a = ga;
    val (pid, aa) = a;
    val (_, ab) = aa;
    val (ac, c) = ab;
    val fs = (state (nth (processesa gc) pid), statea gc);
    val (ls, gs) = la_ex_impla fs ac;
    val gca =
      Pid_global_config_ext
        (list_update (processesa gc) pid (Local_config_ext (c, ls, ())), gs,
          ());
  in
    gca
  end;

fun ga_ex_impl x = stutter_extend_ex ga_gex_impl x;

fun impl4_succ_impl prog mst is_vis_var =
  succ_of_enex_list
    (equal_pid_global_config_ext equal_nat
      (equal_local_state_impl_ext equal_unit)
      (equal_global_state_impl_ext equal_unit) equal_unit)
    (cr_ample_impl4_impl prog mst is_vis_var, ga_ex_impl);

fun test_aprop_impl e s =
  (case eval_exp_impl e
          (Local_state_impl_ext (vi_empty, ()), Global_state_impl_ext (s, ()))
    of NONE => false | SOME a => bool_of_val_impl a);

fun pid_test_gc_impl gci ap = test_aprop_impl ap (variablesa (statea gci));

fun approx_reachable_list_aux (Assign (c, x, e)) = [Assign (c, x, e), Skip]
  | approx_reachable_list_aux (Assign_local (c, x, e)) =
    [Assign_local (c, x, e), Skip]
  | approx_reachable_list_aux (Assign_global (c, x, e)) =
    [Assign_global (c, x, e), Skip]
  | approx_reachable_list_aux (Test e) = [Test e, Skip]
  | approx_reachable_list_aux Skip = [Skip]
  | approx_reachable_list_aux (Seqa (c1, c2)) =
    approx_reachable_list_aux c2 @
      bind (approx_reachable_list_aux c1) (fn c1a => [Seqa (c1a, c2)])
  | approx_reachable_list_aux (Or (c1, c2)) =
    Or (c1, c2) :: approx_reachable_list_aux c1 @ approx_reachable_list_aux c2
  | approx_reachable_list_aux Break = [Break, Invalid]
  | approx_reachable_list_aux Continue = [Continue, Invalid]
  | approx_reachable_list_aux (Iterate (c1, c2)) =
    Skip ::
      bind (approx_reachable_list_aux c1) (fn c1a => [Iterate (c1a, c2)]) @
        bind (approx_reachable_list_aux c2) (fn c2a => [Iterate (c2a, c2)])
  | approx_reachable_list_aux Invalid = [Invalid];

fun approx_reachable_list prog =
  remdups equal_cmd (maps approx_reachable_list_aux (cfg_V0_list prog));

fun cfg_succ_list (Assign (ge, x, e)) = [(Inl (AAssign (ge, x, e)), Skip)]
  | cfg_succ_list (Assign_local (ge, x, e)) =
    [(Inl (AAssign_local (ge, x, e)), Skip)]
  | cfg_succ_list (Assign_global (ge, x, e)) =
    [(Inl (AAssign_global (ge, x, e)), Skip)]
  | cfg_succ_list (Test e) = [(Inl (ATest e), Skip)]
  | cfg_succ_list (Seqa (c1, c2)) =
    (if equal_cmda c1 Skip then [(Inl ASkip, c2)]
      else map (fn (e, c1a) =>
                 (e, (if equal_cmda c1a Skip then c2 else Seqa (c1a, c2))))
             (cfg_succ_list c1))
  | cfg_succ_list (Or (c1, c2)) =
    remdups (equal_prod (equal_sum equal_action equal_brk_ctd) equal_cmd)
      (cfg_succ_list c1 @ cfg_succ_list c2)
  | cfg_succ_list Break = [(Inr AIBreak, Invalid)]
  | cfg_succ_list Continue = [(Inr AIContinue, Invalid)]
  | cfg_succ_list (Iterate (c, cb)) =
    (if equal_cmda c Skip then [(Inl ASkip, Iterate (cb, cb))] else []) @
      remdups (equal_prod (equal_sum equal_action equal_brk_ctd) equal_cmd)
        (map (fn a =>
               (case a
                 of (Inl e, ca) =>
                   (Inl e,
                     (if equal_cmda ca Skip then Iterate (cb, cb)
                       else Iterate (ca, cb)))
                 | (Inr AIBreak, _) => (Inl ASkip, Skip)
                 | (Inr AIContinue, _) => (Inl ASkip, Iterate (cb, cb))))
          (cfg_succ_list c))
  | cfg_succ_list Skip = []
  | cfg_succ_list Invalid = [];

fun map_prod f g (a, b) = (f a, g b);

fun projl (Inl x1) = x1;

fun isl (Inl x1) = true
  | isl (Inr x2) = false;

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun cfg_succ_lista c =
  map_filter
    (fn x => (if (isl o fst) x then SOME (map_prod projl id x) else NONE))
    (cfg_succ_list c);

fun comp_info_of prog =
  let
    val rlist = approx_reachable_list prog;
    val succs_tab = map cfg_succ_lista rlist;
    val a =
      Vector.fromList
        (map (map (fn (a, c) => (a, the (cr_index_of equal_cmd rlist c))))
          succs_tab);
  in
    (rlist, a)
  end;

fun sm_to_sa_impl prog is_vis_var =
  let
    val cinf = comp_info_of prog;
  in
    Gen_g_impl_ext
      ((fn _ => true),
        remdups
          (equal_pid_global_config_ext equal_nat
            (equal_local_state_impl_ext equal_unit)
            (equal_global_state_impl_ext equal_unit) equal_unit) o
          impl4_succ_impl prog cinf is_vis_var,
        [pid_init_gc_impl_impl prog cinf],
        Gen_sa_impl_ext (pid_test_gc_impl, ()))
  end;

fun ty_expr (gamma_l, gamma_g) (E_var x) =
  (if not (is_none (gamma_l x)) orelse not (is_none (gamma_g x)) then SOME ()
    else NONE)
  | ty_expr (gamma_l, gamma_g) (E_localvar x) =
    (if not (is_none (gamma_l x)) then SOME () else NONE)
  | ty_expr (gamma_l, gamma_g) (E_globalvar x) =
    (if not (is_none (gamma_g x)) then SOME () else NONE)
  | ty_expr uu (E_const c) =
    (if less_eq_int min_signed c andalso less_eq_int c max_signed then SOME ()
      else NONE)
  | ty_expr (gamma_l, gamma_g) (E_bin (bop, e1, e2)) =
    binda (ty_expr (gamma_l, gamma_g) e1)
      (fn _ => binda (ty_expr (gamma_l, gamma_g) e2) (fn _ => SOME ()))
  | ty_expr (gamma_l, gamma_g) (E_un (uop, e)) =
    binda (ty_expr (gamma_l, gamma_g) e) (fn _ => SOME ());

fun ty_cmd ((gamma_l, gamma_g), loop) (Assign (c, x, e)) =
  not (is_none (ty_expr (gamma_l, gamma_g) c)) andalso
    ((not (is_none (gamma_l x)) orelse not (is_none (gamma_g x))) andalso
      not (is_none (ty_expr (gamma_l, gamma_g) e)))
  | ty_cmd ((gamma_l, gamma_g), loop) (Assign_local (c, x, e)) =
    not (is_none (ty_expr (gamma_l, gamma_g) c)) andalso
      (not (is_none (gamma_l x)) andalso
        not (is_none (ty_expr (gamma_l, gamma_g) e)))
  | ty_cmd ((gamma_l, gamma_g), loop) (Assign_global (c, x, e)) =
    not (is_none (ty_expr (gamma_l, gamma_g) c)) andalso
      (not (is_none (gamma_g x)) andalso
        not (is_none (ty_expr (gamma_l, gamma_g) e)))
  | ty_cmd ((gamma_l, gamma_g), loop) (Test e) =
    not (is_none (ty_expr (gamma_l, gamma_g) e))
  | ty_cmd ((gamma_l, gamma_g), loop) Skip = true
  | ty_cmd ((gamma_l, gamma_g), loop) (Seqa (c1, c2)) =
    ty_cmd ((gamma_l, gamma_g), loop) c1 andalso
      ty_cmd ((gamma_l, gamma_g), loop) c2
  | ty_cmd ((gamma_l, gamma_g), loop) (Or (c1, c2)) =
    ty_cmd ((gamma_l, gamma_g), loop) c1 andalso
      ty_cmd ((gamma_l, gamma_g), loop) c2
  | ty_cmd ((gamma_l, gamma_g), loop) Break = loop
  | ty_cmd ((gamma_l, gamma_g), loop) Continue = loop
  | ty_cmd ((gamma_l, gamma_g), loop) (Iterate (c1, c2)) =
    ty_cmd ((gamma_l, gamma_g), true) c1 andalso
      ty_cmd ((gamma_l, gamma_g), true) c2
  | ty_cmd ((gamma_l, gamma_g), loop) Invalid = false;

fun ty_proc_decl gamma_g pd =
  let
    val gamma_l =
      (fn x =>
        (if membera equal_literal (local_vars pd) x then SOME () else NONE));
  in
    ty_cmd ((gamma_l, gamma_g), false) (body pd)
  end;

fun ty_program prog =
  let
    val gamma_g =
      (fn x =>
        (if membera equal_literal (global_vars prog) x then SOME () else NONE));
  in
    list_all (ty_proc_decl gamma_g) (processes prog)
  end;

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun vars_of_aprop e = sup_set equal_literal (udvars_of_exp e) (gvars_of_exp e);

fun atoms_ltlc A_ True_ltlc = bot_set
  | atoms_ltlc A_ False_ltlc = bot_set
  | atoms_ltlc A_ (Prop_ltlc x3) = inserta A_ x3 bot_set
  | atoms_ltlc A_ (Not_ltlc x4) = atoms_ltlc A_ x4
  | atoms_ltlc A_ (And_ltlc (x51, x52)) =
    sup_set A_ (atoms_ltlc A_ x51) (atoms_ltlc A_ x52)
  | atoms_ltlc A_ (Or_ltlc (x61, x62)) =
    sup_set A_ (atoms_ltlc A_ x61) (atoms_ltlc A_ x62)
  | atoms_ltlc A_ (Implies_ltlc (x71, x72)) =
    sup_set A_ (atoms_ltlc A_ x71) (atoms_ltlc A_ x72)
  | atoms_ltlc A_ (Next_ltlc x8) = atoms_ltlc A_ x8
  | atoms_ltlc A_ (Final_ltlc x9) = atoms_ltlc A_ x9
  | atoms_ltlc A_ (Global_ltlc x10) = atoms_ltlc A_ x10
  | atoms_ltlc A_ (Until_ltlc (x111, x112)) =
    sup_set A_ (atoms_ltlc A_ x111) (atoms_ltlc A_ x112)
  | atoms_ltlc A_ (Release_ltlc (x121, x122)) =
    sup_set A_ (atoms_ltlc A_ x121) (atoms_ltlc A_ x122);

fun vars_of_ltlc phi =
  sup_seta equal_literal (image vars_of_aprop (atoms_ltlc equal_exp phi));

fun cfg_l2b (c1, (c2, c3)) = c1;

fun cfg_ce (c1, (c2, c3)) = c3;

fun igbgi_num_acc
  (Gen_g_impl_ext
    (gi_V, gi_E, gi_V0, Gen_igbg_impl_ext (igbgi_num_acc, igbgi_acc, more)))
  = igbgi_num_acc;

fun incoming_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = incoming_impl;

fun name_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = name_impl;

fun array_get_oo x a = FArray.IsabelleMapping.array_get_oo x a o integer_of_nat;

fun iam_alpha a i = array_get_oo NONE a i;

fun iam_increment l idx =
  max ord_nat (minus_nat (plus_nata idx one_nata) l)
    (plus_nata (times_nata (nat_of_integer (2 : IntInf.int)) l)
      (nat_of_integer (3 : IntInf.int)));

fun array_set_oo f a = FArray.IsabelleMapping.array_set_oo f a o integer_of_nat;

fun iam_update k v a =
  array_set_oo
    (fn _ => let
               val l = array_length a;
             in
               array_set (array_grow a (iam_increment l k) NONE) k (SOME v)
             end)
    a k (SOME v);

fun iam_empty x = (fn _ => FArray.IsabelleMapping.array_of_list []) x;

fun rm_iterateoi Empty c f sigma = sigma
  | rm_iterateoi (Branch (col, l, k, v, r)) c f sigma =
    (if c sigma
      then let
             val sigmaa = rm_iterateoi l c f sigma;
           in
             (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa) else sigmaa)
           end
      else sigma);

fun the_default uu (SOME x) = x
  | the_default x NONE = x;

fun build_succ_code A_ x =
  foldli x (fn _ => true)
    (fn xa =>
      (map_iterator_dom o rm_iterateoi) (incoming_impl xa) (fn _ => true)
        (fn xaa => fn sigma =>
          (if equal_nata xaa zero_nata then sigma
            else iam_update xaa
                   (glist_insert equal_nata (name_impl xa)
                     (the_default [] (iam_alpha sigma xaa)))
                   sigma)))
    (iam_empty ());

fun old_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = old_impl;

fun rbt_ins less f k v (Branch (R, l, x, y, r)) =
  (if less k x then Branch (R, rbt_ins less f k v l, x, y, r)
    else (if less x k then Branch (R, l, x, y, rbt_ins less f k v r)
           else Branch (R, l, x, f k y v, r)))
  | rbt_ins less f k v (Branch (B, l, x, y, r)) =
    (if less k x then balance (rbt_ins less f k v l) x y r
      else (if less x k then balance l x y (rbt_ins less f k v r)
             else Branch (B, l, x, f k y v, r)))
  | rbt_ins less f k v Empty = Branch (R, Empty, k, v, Empty);

fun rbt_insert_with_key less f k v t = paint B (rbt_ins less f k v t);

fun rbt_insert less = rbt_insert_with_key less (fn _ => fn _ => fn nv => nv);

fun sunion_with less f asa [] = asa
  | sunion_with less f [] bs = bs
  | sunion_with less f ((ka, va) :: asa) ((k, v) :: bs) =
    (if less k ka then (k, v) :: sunion_with less f ((ka, va) :: asa) bs
      else (if less ka k then (ka, va) :: sunion_with less f asa ((k, v) :: bs)
             else (ka, f ka va v) :: sunion_with less f asa bs));

fun skip_red (Branch (R, l, k, v, r)) = l
  | skip_red Empty = Empty
  | skip_red (Branch (B, va, vb, vc, vd)) = Branch (B, va, vb, vc, vd);

fun skip_black t =
  let
    val ta = skip_red t;
  in
    (case ta of Empty => ta | Branch (R, _, _, _, _) => ta
      | Branch (B, l, _, _, _) => l)
  end;

fun compare_height sx s t tx =
  (case (skip_red sx, (skip_red s, (skip_red t, skip_red tx)))
    of (Empty, (Empty, (_, Empty))) => EQ
    | (Empty, (Empty, (_, Branch (_, _, _, _, _)))) => LT
    | (Empty, (Branch (_, _, _, _, _), (Empty, _))) => EQ
    | (Empty, (Branch (_, _, _, _, _), (Branch (_, _, _, _, _), Empty))) => EQ
    | (Empty,
        (Branch (_, sa, _, _, _),
          (Branch (_, ta, _, _, _), Branch (_, txa, _, _, _))))
      => compare_height Empty sa ta (skip_black txa)
    | (Branch (_, _, _, _, _), (Empty, (Empty, Empty))) => GT
    | (Branch (_, _, _, _, _), (Empty, (Empty, Branch (_, _, _, _, _)))) => LT
    | (Branch (_, _, _, _, _), (Empty, (Branch (_, _, _, _, _), Empty))) => EQ
    | (Branch (_, _, _, _, _),
        (Empty, (Branch (_, _, _, _, _), Branch (_, _, _, _, _))))
      => LT
    | (Branch (_, _, _, _, _), (Branch (_, _, _, _, _), (Empty, _))) => GT
    | (Branch (_, sxa, _, _, _),
        (Branch (_, sa, _, _, _), (Branch (_, ta, _, _, _), Empty)))
      => compare_height (skip_black sxa) sa ta Empty
    | (Branch (_, sxa, _, _, _),
        (Branch (_, sa, _, _, _),
          (Branch (_, ta, _, _, _), Branch (_, txa, _, _, _))))
      => compare_height (skip_black sxa) sa ta (skip_black txa));

fun apfst f (x, y) = (f x, y);

fun divmod_nat m n = (divide_nata m n, modulo_nata m n);

fun rbtreeify_g n kvs =
  (if equal_nata n zero_nata orelse equal_nata n one_nata then (Empty, kvs)
    else let
           val (na, r) = divmod_nat n (nat_of_integer (2 : IntInf.int));
         in
           (if equal_nata r zero_nata
             then let
                    val (t1, (k, v) :: kvsa) = rbtreeify_g na kvs;
                  in
                    apfst (fn a => Branch (B, t1, k, v, a))
                      (rbtreeify_g na kvsa)
                  end
             else let
                    val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                  in
                    apfst (fn a => Branch (B, t1, k, v, a))
                      (rbtreeify_g na kvsa)
                  end)
         end)
and rbtreeify_f n kvs =
  (if equal_nata n zero_nata then (Empty, kvs)
    else (if equal_nata n one_nata then let
  val (k, v) :: kvsa = kvs;
in
  (Branch (R, Empty, k, v, Empty), kvsa)
end
           else let
                  val (na, r) = divmod_nat n (nat_of_integer (2 : IntInf.int));
                in
                  (if equal_nata r zero_nata
                    then let
                           val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                         in
                           apfst (fn a => Branch (B, t1, k, v, a))
                             (rbtreeify_g na kvsa)
                         end
                    else let
                           val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                         in
                           apfst (fn a => Branch (B, t1, k, v, a))
                             (rbtreeify_f na kvsa)
                         end)
                end));

fun rbtreeify kvs = fst (rbtreeify_g (suc (size_list kvs)) kvs);

fun folda f (Branch (c, lt, k, v, rt)) x = folda f rt (f k v (folda f lt x))
  | folda f Empty x = x;

fun rbt_union_with_key less f t1 t2 =
  (case compare_height t1 t1 t2 t2
    of LT =>
      folda (rbt_insert_with_key less (fn k => fn v => fn w => f k w v)) t1 t2
    | GT => folda (rbt_insert_with_key less f) t2 t1
    | EQ => rbtreeify (sunion_with less f (entriesa t1) (entriesa t2)));

fun rbt_union less = rbt_union_with_key less (fn _ => fn _ => fn rv => rv);

fun dflt_cmp le lt a b =
  (if lt a b then LESS else (if le a b then EQUAL else GREATER));

fun cmp_prod cmp1 cmp2 (a1, a2) (b1, b2) =
  (case cmp1 a1 b1 of LESS => LESS | EQUAL => cmp2 a2 b2 | GREATER => GREATER);

fun rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 True_ltln = f1
  | rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 False_ltln = f2
  | rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 (Prop_ltln x3) = f3 x3
  | rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 (Nprop_ltln x4) = f4 x4
  | rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 (And_ltln (x51, x52)) =
    f5 x51 x52 (rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 x51)
      (rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 x52)
  | rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 (Or_ltln (x61, x62)) =
    f6 x61 x62 (rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 x61)
      (rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 x62)
  | rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 (Next_ltln x7) =
    f7 x7 (rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 x7)
  | rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 (Until_ltln (x81, x82)) =
    f8 x81 x82 (rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 x81)
      (rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 x82)
  | rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 (Release_ltln (x91, x92)) =
    f9 x91 x92 (rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 x91)
      (rec_ltln f1 f2 f3 f4 f5 f6 f7 f8 f9 x92);

fun comp2lt cmp a b =
  (case cmp a b of LESS => true | EQUAL => false | GREATER => false);

fun until_frmlsn_impl (A1_, A2_) =
  rec_ltln Empty Empty (fn _ => Empty) (fn _ => Empty)
    (fn _ => fn _ =>
      rbt_union
        (comp2lt
          (cmp_prod (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_)))
            (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_))))))
    (fn _ => fn _ =>
      rbt_union
        (comp2lt
          (cmp_prod (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_)))
            (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_))))))
    (fn _ => fn xa => xa)
    (fn x => fn xa => fn xb => fn xc =>
      map2set_insert
        (rbt_insert
          (comp2lt
            (cmp_prod
              (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_)))
              (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_))))))
        (x, xa)
        (rbt_union
          (comp2lt
            (cmp_prod
              (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_)))
              (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_)))))
          xb xc))
    (fn _ => fn _ =>
      rbt_union
        (comp2lt
          (cmp_prod (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_)))
            (dflt_cmp (less_eq_ltln (A1_, A2_)) (less_ltln (A1_, A2_))))));

fun memb_sorted (A1_, A2_) [] x = false
  | memb_sorted (A1_, A2_) (y :: xs) x =
    (if less A2_ y x then memb_sorted (A1_, A2_) xs x else eq A1_ x y);

fun lss_memb (A1_, A2_) x l =
  memb_sorted (A1_, (ord_preorder o preorder_order o order_linorder) A2_) l x;

fun it_to_list it s = it s (fn _ => true) (fn x => fn l => l @ [x]) [];

fun gen_subseteq ball1 mem2 s1 s2 = ball1 s1 (fn x => mem2 x s2);

fun gen_equal ss1 ss2 s1 s2 = ss1 s1 s2 andalso ss2 s2 s1;

fun gen_ball it s p = it s (fn x => x) (fn x => fn _ => p x) true;

fun build_F_impl (A1_, A2_) =
  (fn x => fn xa =>
    gen_image
      (fn xb =>
        foldli
          (it_to_list (map_iterator_dom o (foldli o it_to_list rm_iterateoi))
            xb))
      [] (glist_insert
           (gen_equal
             (gen_subseteq (gen_ball (fn xb => foldli (id xb)))
               (glist_member equal_nata))
             (gen_subseteq (gen_ball (fn xb => foldli (id xb)))
               (glist_member equal_nata))))
      (fn (xb, xc) =>
        gen_image (fn xd => foldli (id xd)) [] (glist_insert equal_nata)
          name_impl
          (filter
            (fn xd =>
              (if lss_memb (equal_ltln A1_, linorder_ltln (A1_, A2_))
                    (Until_ltln (xb, xc)) (old_impl xd)
                then lss_memb (equal_ltln A1_, linorder_ltln (A1_, A2_)) xc
                       (old_impl xd)
                else true))
            x))
      (until_frmlsn_impl (A1_, A2_) xa));

fun lss_iteratei l = foldli l;

fun iteratei_set_op_list_it_lss_ops A_ s = lss_iteratei s;

fun pn_map_code (A1_, A2_) x =
  foldli x (fn _ => true)
    (fn xa => fn sigma =>
      let
        val xaa =
          iteratei_set_op_list_it_lss_ops (linorder_ltln (A1_, A2_))
            (old_impl xa) (fn _ => true)
            (fn xaa => fn (a, b) =>
              (case xaa of True_ltln => (a, b) | False_ltln => (a, b)
                | Prop_ltln aa => (glist_insert (eq A1_) aa a, b)
                | Nprop_ltln aa => (a, glist_insert (eq A1_) aa b)
                | And_ltln (_, _) => (a, b) | Or_ltln (_, _) => (a, b)
                | Next_ltln _ => (a, b) | Until_ltln (_, _) => (a, b)
                | Release_ltln (_, _) => (a, b)))
            ([], []);
      in
        iam_update (name_impl xa) xaa sigma
      end)
    (iam_empty ());

fun cr_rename_gba_code (A1_, A2_) x y =
  let
    val xa = gen_image foldli [] (glist_insert equal_nata) name_impl x;
    val xaa =
      gen_image foldli [] (glist_insert equal_nata) name_impl
        (filter
          (fn xb =>
            map2set_memb (fn k => fn t => rbt_lookup ord_nat t k) zero_nata
              (incoming_impl xb))
          x);
    val xb = build_succ_code A2_ x;
    val xc = (fn xc => the_default [] (iam_alpha xb xc));
    val xd = build_F_impl (A1_, A2_) x y;
    val xe = pn_map_code (A1_, A2_) x;
    val xf =
      (fn xda => fn xea =>
        (case iam_alpha xe xda of NONE => false
          | SOME (xf, xg) =>
            gen_ball foldli xf xea andalso
              gen_ball foldli xg (fn xh => not (xea xh))));
  in
    Gen_g_impl_ext
      (xa, xc, xaa, Gen_gbg_impl_ext (xd, Gen_gba_impl_ext (xf, ())))
  end;

fun insertion_sort (A1_, A2_) x [] = [x]
  | insertion_sort (A1_, A2_) x (y :: xs) =
    (if less A2_ y x then y :: insertion_sort (A1_, A2_) x xs
      else (if eq A1_ x y then y :: xs else x :: y :: xs));

fun lss_ins (A1_, A2_) x l =
  insertion_sort (A1_, (ord_preorder o preorder_order o order_linorder) A2_) x
    l;

fun lss_ins_dj (A1_, A2_) = lss_ins (A1_, A2_);

fun lss_empty x = (fn _ => []) x;

fun next_impl_update next_impla
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = Node_impl_ext
      (name_impl, incoming_impl, new_impl, old_impl, next_impla next_impl,
        more);

fun name_impl_update name_impla
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = Node_impl_ext
      (name_impla name_impl, incoming_impl, new_impl, old_impl, next_impl,
        more);

fun old_impl_update old_impla
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = Node_impl_ext
      (name_impl, incoming_impl, new_impl, old_impla old_impl, next_impl, more);

fun new_impl_update new_impla
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = Node_impl_ext
      (name_impl, incoming_impl, new_impla new_impl, old_impl, next_impl, more);

fun iteratei_bset_op_list_it_lss_basic_ops A_ s = lss_iteratei s;

fun g_ball_lss_basic_ops A_ s p =
  iteratei_bset_op_list_it_lss_basic_ops A_ s (fn c => c) (fn x => fn _ => p x)
    true;

fun g_subset_lss_basic_ops (A1_, A2_) s1 s2 =
  g_ball_lss_basic_ops A2_ s1 (fn x => lss_memb (A1_, A2_) x s2);

fun g_equal_lss_basic_ops (A1_, A2_) s1 s2 =
  g_subset_lss_basic_ops (A1_, A2_) s1 s2 andalso
    g_subset_lss_basic_ops (A1_, A2_) s2 s1;

fun g_sel_lss_basic_ops A_ s p =
  iteratei_bset_op_list_it_lss_basic_ops A_ s is_none
    (fn x => fn _ => (if p x then SOME x else NONE)) NONE;

fun next_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = next_impl;

fun new_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = new_impl;

fun incoming_impl_update incoming_impla
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = Node_impl_ext
      (name_impl, incoming_impla incoming_impl, new_impl, old_impl, next_impl,
        more);

fun upd_incoming_impl (A1_, A2_) =
  (fn x =>
    map (fn xa =>
          (if g_equal_lss_basic_ops (equal_ltln A1_, linorder_ltln (A1_, A2_))
                (old_impl xa) (old_impl x) andalso
                g_equal_lss_basic_ops (equal_ltln A1_, linorder_ltln (A1_, A2_))
                  (next_impl xa) (next_impl x)
            then incoming_impl_update
                   (fn _ =>
                     rbt_union less_nat (incoming_impl x) (incoming_impl xa))
                   xa
            else xa)));

fun lss_union (A1_, A2_) s1 s2 = merge (A1_, A2_) s1 s2;

fun lss_union_dj (A1_, A2_) = lss_union (A1_, A2_);

fun lss_isEmpty s = null s;

fun delete_sorted (A1_, A2_) x [] = []
  | delete_sorted (A1_, A2_) x (y :: xs) =
    (if less A2_ y x then y :: delete_sorted (A1_, A2_) x xs
      else (if eq A1_ x y then xs else y :: xs));

fun lss_delete (A1_, A2_) x l =
  delete_sorted (A1_, (ord_preorder o preorder_order o order_linorder) A2_) x l;

fun gen_bex it s p = it s not (fn x => fn _ => p x) false;

fun expand_code_0 (A1_, A2_) x =
  let
    val (a, b) = x;
  in
    (if lss_isEmpty (new_impl a)
      then (if gen_bex (fn xa => foldli (id xa)) b
                 (fn xc =>
                   g_equal_lss_basic_ops
                     (equal_ltln A1_, linorder_ltln (A1_, A2_)) (old_impl xc)
                     (old_impl a) andalso
                     g_equal_lss_basic_ops
                       (equal_ltln A1_, linorder_ltln (A1_, A2_)) (next_impl xc)
                       (next_impl a))
             then DRETURN (name_impl a, upd_incoming_impl (A1_, A2_) a b)
             else expand_code_0 (A1_, A2_)
                    (Node_impl_ext
                       (suc (name_impl a),
                         map2set_insert (rbt_inserta ord_nat) (name_impl a)
                           Empty,
                         next_impl a, lss_empty (), lss_empty (), ()),
                      a :: b))
      else dbind (DRETURN
                   (the (g_sel_lss_basic_ops (linorder_ltln (A1_, A2_))
                          (new_impl a) (fn _ => true))))
             (fn xa =>
               let
                 val xb =
                   new_impl_update
                     (fn _ =>
                       lss_delete (equal_ltln A1_, linorder_ltln (A1_, A2_)) xa
                         (new_impl a))
                     a;
               in
                 (case xa
                   of True_ltln =>
                     expand_code_0 (A1_, A2_)
                       (old_impl_update
                          (fn _ =>
                            lss_union (equal_ltln A1_, linorder_ltln (A1_, A2_))
                              (lss_ins_dj
                                (equal_ltln A1_, linorder_ltln (A1_, A2_)) xa
                                (lss_empty ()))
                              (old_impl xb))
                          xb,
                         b)
                   | False_ltln => DRETURN (name_impl xb, b)
                   | Prop_ltln aa =>
                     (if lss_memb (equal_ltln A1_, linorder_ltln (A1_, A2_))
                           (Nprop_ltln aa) (old_impl xb)
                       then DRETURN (name_impl xb, b)
                       else expand_code_0 (A1_, A2_)
                              (old_impl_update
                                 (fn _ =>
                                   lss_union
                                     (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                     (lss_ins_dj
                                       (equal_ltln A1_,
 linorder_ltln (A1_, A2_))
                                       xa (lss_empty ()))
                                     (old_impl xb))
                                 xb,
                                b))
                   | Nprop_ltln aa =>
                     (if lss_memb (equal_ltln A1_, linorder_ltln (A1_, A2_))
                           (Prop_ltln aa) (old_impl xb)
                       then DRETURN (name_impl xb, b)
                       else expand_code_0 (A1_, A2_)
                              (old_impl_update
                                 (fn _ =>
                                   lss_union
                                     (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                     (lss_ins_dj
                                       (equal_ltln A1_,
 linorder_ltln (A1_, A2_))
                                       xa (lss_empty ()))
                                     (old_impl xb))
                                 xb,
                                b))
                   | And_ltln (ltln1, ltln2) =>
                     expand_code_0 (A1_, A2_)
                       (next_impl_update (fn _ => next_impl xb)
                          (old_impl_update
                            (fn _ =>
                              lss_union
                                (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                (lss_ins_dj
                                  (equal_ltln A1_, linorder_ltln (A1_, A2_)) xa
                                  (lss_empty ()))
                                (old_impl xb))
                            (new_impl_update
                              (fn _ =>
                                lss_ins
                                  (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  ltln1
                                  (lss_ins
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    ltln2 (new_impl xb)))
                              xb)),
                         b)
                   | Or_ltln (ltln1, ltln2) =>
                     dbind (expand_code_0 (A1_, A2_)
                             (next_impl_update
                                (fn _ =>
                                  lss_union_dj
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    (lss_empty ()) (next_impl xb))
                                (old_impl_update
                                  (fn _ =>
                                    lss_ins
                                      (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                      xa (old_impl xb))
                                  (new_impl_update
                                    (fn _ =>
                                      lss_ins
(equal_ltln A1_, linorder_ltln (A1_, A2_)) ltln1 (new_impl xb))
                                    xb)),
                               b))
                       (fn (aa, ba) =>
                         expand_code_0 (A1_, A2_)
                           (old_impl_update
                              (fn _ =>
                                lss_union
                                  (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  (lss_ins_dj
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    xa (lss_empty ()))
                                  (old_impl xb))
                              (new_impl_update
                                (fn _ =>
                                  lss_union
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    (lss_ins_dj
                                      (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                      ltln2 (lss_empty ()))
                                    (new_impl xb))
                                (name_impl_update (fn _ => aa) xb)),
                             ba))
                   | Next_ltln ltln =>
                     expand_code_0 (A1_, A2_)
                       (next_impl_update
                          (fn _ =>
                            lss_ins (equal_ltln A1_, linorder_ltln (A1_, A2_))
                              ltln (next_impl xb))
                          (old_impl_update
                            (fn _ =>
                              lss_union
                                (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                (lss_ins_dj
                                  (equal_ltln A1_, linorder_ltln (A1_, A2_)) xa
                                  (lss_empty ()))
                                (old_impl xb))
                            (new_impl_update (fn _ => new_impl xb) xb)),
                         b)
                   | Until_ltln (ltln1, ltln2) =>
                     dbind (expand_code_0 (A1_, A2_)
                             (next_impl_update
                                (fn _ =>
                                  lss_union
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    (lss_ins_dj
                                      (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                      xa (lss_empty ()))
                                    (next_impl xb))
                                (old_impl_update
                                  (fn _ =>
                                    lss_ins
                                      (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                      xa (old_impl xb))
                                  (new_impl_update
                                    (fn _ =>
                                      lss_ins
(equal_ltln A1_, linorder_ltln (A1_, A2_)) ltln1 (new_impl xb))
                                    xb)),
                               b))
                       (fn (aa, ba) =>
                         expand_code_0 (A1_, A2_)
                           (old_impl_update
                              (fn _ =>
                                lss_union
                                  (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  (lss_ins_dj
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    xa (lss_empty ()))
                                  (old_impl xb))
                              (new_impl_update
                                (fn _ =>
                                  lss_union
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    (lss_ins_dj
                                      (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                      ltln2 (lss_empty ()))
                                    (new_impl xb))
                                (name_impl_update (fn _ => aa) xb)),
                             ba))
                   | Release_ltln (ltln1, ltln2) =>
                     dbind (expand_code_0 (A1_, A2_)
                             (next_impl_update
                                (fn _ =>
                                  lss_union
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    (lss_ins_dj
                                      (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                      xa (lss_empty ()))
                                    (next_impl xb))
                                (old_impl_update
                                  (fn _ =>
                                    lss_ins
                                      (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                      xa (old_impl xb))
                                  (new_impl_update
                                    (fn _ =>
                                      lss_ins
(equal_ltln A1_, linorder_ltln (A1_, A2_)) ltln2 (new_impl xb))
                                    xb)),
                               b))
                       (fn (aa, ba) =>
                         expand_code_0 (A1_, A2_)
                           (old_impl_update
                              (fn _ =>
                                lss_union
                                  (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  (lss_ins_dj
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    xa (lss_empty ()))
                                  (old_impl xb))
                              (new_impl_update
                                (fn _ =>
                                  lss_union
                                    (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                    (lss_ins
                                      (equal_ltln A1_, linorder_ltln (A1_, A2_))
                                      ltln1
                                      (lss_ins_dj
(equal_ltln A1_, linorder_ltln (A1_, A2_)) ltln2 (lss_empty ())))
                                    (new_impl xb))
                                (name_impl_update (fn _ => aa) xb)),
                             ba)))
               end))
  end;

fun expand_code (A1_, A2_) n_ns = the_res (expand_code_0 (A1_, A2_) n_ns);

fun create_graph_code (A1_, A2_) phi =
  let
    val (_, b) =
      expand_code (A1_, A2_)
        (Node_impl_ext
           (suc zero_nata, map2set_insert (rbt_inserta ord_nat) zero_nata Empty,
             lss_ins_dj (equal_ltln A1_, linorder_ltln (A1_, A2_)) phi
               (lss_empty ()),
             lss_empty (), lss_empty (), ()),
          []);
  in
    b
  end;

fun create_name_gba_code (A1_, A2_) phi =
  let
    val x = create_graph_code (A1_, A2_) phi;
  in
    cr_rename_gba_code (A1_, A2_) x phi
  end;

fun gbai_L
  (Gen_g_impl_ext
    (gi_V, gi_E, gi_V0,
      Gen_gbg_impl_ext (gbgi_F, Gen_gba_impl_ext (gbai_L, more))))
  = gbai_L;

fun gbgi_F (Gen_g_impl_ext (gi_V, gi_E, gi_V0, Gen_gbg_impl_ext (gbgi_F, more)))
  = gbgi_F;

fun set_bit_integer x i b = Bits_Integer.set_bit x (integer_of_nat i) b;

fun bs_insert i s = set_bit_integer s i true;

fun bs_empty x = (fn _ => (0 : IntInf.int)) x;

fun gbg_to_idx_ext_code def_size eq bhc ecnv g =
  let
    val a =
      let
        val x = id (gbgi_F g);
        val xa = size_list x;
        val a =
          let
            val xb = ahm_emptyb def_size;
            val (_, b) =
              foldli x (fn _ => true)
                (fn xc => fn (a, b) =>
                  let
                    val ba =
                      foldli (id xc) (fn _ => true)
                        (fn xd => fn sigma =>
                          ahm_updateb eq bhc xd
                            (bs_insert a
                              (the_default (bs_empty ())
                                (ahm_lookupb eq bhc xd sigma)))
                            sigma)
                        b;
                  in
                    (suc a, ba)
                  end)
                (zero_nata, xb);
          in
            (fn xe => the_default (bs_empty ()) (ahm_lookupb eq bhc xe b))
          end;
      in
        (xa, a)
      end;
    val (aa, b) = a;
  in
    Gen_g_impl_ext (gi_V g, gi_E g, gi_V0 g, Gen_igbg_impl_ext (aa, b, ecnv g))
  end;

fun gba_to_idx_ext_code eq bhc def_size ecnv g =
  gbg_to_idx_ext_code eq bhc def_size
    (fn xa => Gen_igba_impl_ext (gbai_L xa, ecnv xa)) g;

fun stat_set_data ns ni na =
  Gerth_Statistics.set_data (integer_of_nat ns) (integer_of_nat ni)
    (integer_of_nat na);

fun gen_card D_ it s = it s (fn _ => true) (fn _ => suc) (zero D_);

fun create_name_igba_code (A1_, A2_) phi =
  let
    val x = create_name_gba_code (A1_, A2_) phi;
    val xa =
      gba_to_idx_ext_code (def_hashmap_size_nat Type) equal_nata
        (bounded_hashcode_nat hashable_nat) (fn _ => ()) x;
    val _ =
      stat_set_data (gen_card zero_nat foldli (gi_V x))
        (gen_card zero_nat foldli (gi_V0 xa)) (igbgi_num_acc xa);
  in
    xa
  end;

fun size_ltln True_ltln = suc zero_nata
  | size_ltln False_ltln = suc zero_nata
  | size_ltln (Prop_ltln x3) = suc zero_nata
  | size_ltln (Nprop_ltln x4) = suc zero_nata
  | size_ltln (And_ltln (x51, x52)) =
    plus_nata (plus_nata (size_ltln x51) (size_ltln x52)) (suc zero_nata)
  | size_ltln (Or_ltln (x61, x62)) =
    plus_nata (plus_nata (size_ltln x61) (size_ltln x62)) (suc zero_nata)
  | size_ltln (Next_ltln x7) = plus_nata (size_ltln x7) (suc zero_nata)
  | size_ltln (Until_ltln (x81, x82)) =
    plus_nata (plus_nata (size_ltln x81) (size_ltln x82)) (suc zero_nata)
  | size_ltln (Release_ltln (x91, x92)) =
    plus_nata (plus_nata (size_ltln x91) (size_ltln x92)) (suc zero_nata);

fun sup_pred (Seq f) (Seq g) =
  Seq (fn _ =>
        (case f () of Emptya => g ()
          | Insert (x, p) => Insert (x, sup_pred p (Seq g))
          | Join (p, xq) => adjunct (Seq g) (Join (p, xq))))
and adjunct p Emptya = Join (p, Emptya)
  | adjunct p (Insert (x, q)) = Insert (x, sup_pred q p)
  | adjunct p (Join (q, xq)) = Join (q, adjunct p xq);

val bot_pred : 'a pred = Seq (fn _ => Emptya);

fun single x = Seq (fn _ => Insert (x, bot_pred));

fun bindb (Seq g) f = Seq (fn _ => apply f (g ()))
and apply f Emptya = Emptya
  | apply f (Insert (x, p)) = Join (f x, Join (bindb p f, Emptya))
  | apply f (Join (p, xq)) = Join (bindb p f, apply f xq);

fun eq_i_i A_ xa xb =
  bindb (single (xa, xb))
    (fn (x, xaa) => (if eq A_ x xaa then single () else bot_pred));

fun syntactical_implies_i_i A_ x xa =
  sup_pred
    (bindb (single (x, xa))
      (fn a =>
        (case a of (_, True_ltln) => single () | (_, False_ltln) => bot_pred
          | (_, Prop_ltln _) => bot_pred | (_, Nprop_ltln _) => bot_pred
          | (_, And_ltln (_, _)) => bot_pred | (_, Or_ltln (_, _)) => bot_pred
          | (_, Next_ltln _) => bot_pred | (_, Until_ltln (_, _)) => bot_pred
          | (_, Release_ltln (_, _)) => bot_pred)))
    (sup_pred
      (bindb (single (x, xa))
        (fn a =>
          (case a of (True_ltln, _) => bot_pred | (False_ltln, _) => single ()
            | (Prop_ltln _, _) => bot_pred | (Nprop_ltln _, _) => bot_pred
            | (And_ltln (_, _), _) => bot_pred | (Or_ltln (_, _), _) => bot_pred
            | (Next_ltln _, _) => bot_pred | (Until_ltln (_, _), _) => bot_pred
            | (Release_ltln (_, _), _) => bot_pred)))
      (sup_pred
        (bindb (single (x, xa))
          (fn (phi, phia) =>
            (if equal_ltlna A_ phi phia
              then bindb (eq_i_i (equal_ltln A_) phi phi) (fn () => single ())
              else bot_pred)))
        (sup_pred
          (bindb (single (x, xa))
            (fn a =>
              (case a of (True_ltln, _) => bot_pred
                | (False_ltln, _) => bot_pred | (Prop_ltln _, _) => bot_pred
                | (Nprop_ltln _, _) => bot_pred
                | (And_ltln (phi, _), chi) =>
                  bindb (syntactical_implies_i_i A_ phi chi)
                    (fn () => single ())
                | (Or_ltln (_, _), _) => bot_pred | (Next_ltln _, _) => bot_pred
                | (Until_ltln (_, _), _) => bot_pred
                | (Release_ltln (_, _), _) => bot_pred)))
          (sup_pred
            (bindb (single (x, xa))
              (fn a =>
                (case a of (True_ltln, _) => bot_pred
                  | (False_ltln, _) => bot_pred | (Prop_ltln _, _) => bot_pred
                  | (Nprop_ltln _, _) => bot_pred
                  | (And_ltln (_, psi), chi) =>
                    bindb (syntactical_implies_i_i A_ psi chi)
                      (fn () => single ())
                  | (Or_ltln (_, _), _) => bot_pred
                  | (Next_ltln _, _) => bot_pred
                  | (Until_ltln (_, _), _) => bot_pred
                  | (Release_ltln (_, _), _) => bot_pred)))
            (sup_pred
              (bindb (single (x, xa))
                (fn a =>
                  (case a of (_, True_ltln) => bot_pred
                    | (_, False_ltln) => bot_pred | (_, Prop_ltln _) => bot_pred
                    | (_, Nprop_ltln _) => bot_pred
                    | (phi, And_ltln (psi, chi)) =>
                      bindb (syntactical_implies_i_i A_ phi psi)
                        (fn () =>
                          bindb (syntactical_implies_i_i A_ phi chi)
                            (fn () => single ()))
                    | (_, Or_ltln (_, _)) => bot_pred
                    | (_, Next_ltln _) => bot_pred
                    | (_, Until_ltln (_, _)) => bot_pred
                    | (_, Release_ltln (_, _)) => bot_pred)))
              (sup_pred
                (bindb (single (x, xa))
                  (fn a =>
                    (case a of (_, True_ltln) => bot_pred
                      | (_, False_ltln) => bot_pred
                      | (_, Prop_ltln _) => bot_pred
                      | (_, Nprop_ltln _) => bot_pred
                      | (_, And_ltln (_, _)) => bot_pred
                      | (phi, Or_ltln (psi, _)) =>
                        bindb (syntactical_implies_i_i A_ phi psi)
                          (fn () => single ())
                      | (_, Next_ltln _) => bot_pred
                      | (_, Until_ltln (_, _)) => bot_pred
                      | (_, Release_ltln (_, _)) => bot_pred)))
                (sup_pred
                  (bindb (single (x, xa))
                    (fn a =>
                      (case a of (_, True_ltln) => bot_pred
                        | (_, False_ltln) => bot_pred
                        | (_, Prop_ltln _) => bot_pred
                        | (_, Nprop_ltln _) => bot_pred
                        | (_, And_ltln (_, _)) => bot_pred
                        | (phi, Or_ltln (_, chi)) =>
                          bindb (syntactical_implies_i_i A_ phi chi)
                            (fn () => single ())
                        | (_, Next_ltln _) => bot_pred
                        | (_, Until_ltln (_, _)) => bot_pred
                        | (_, Release_ltln (_, _)) => bot_pred)))
                  (sup_pred
                    (bindb (single (x, xa))
                      (fn a =>
                        (case a of (True_ltln, _) => bot_pred
                          | (False_ltln, _) => bot_pred
                          | (Prop_ltln _, _) => bot_pred
                          | (Nprop_ltln _, _) => bot_pred
                          | (And_ltln (_, _), _) => bot_pred
                          | (Or_ltln (phi, psi), chi) =>
                            bindb (syntactical_implies_i_i A_ phi chi)
                              (fn () =>
                                bindb (syntactical_implies_i_i A_ psi chi)
                                  (fn () => single ()))
                          | (Next_ltln _, _) => bot_pred
                          | (Until_ltln (_, _), _) => bot_pred
                          | (Release_ltln (_, _), _) => bot_pred)))
                    (sup_pred
                      (bindb (single (x, xa))
                        (fn a =>
                          (case a of (_, True_ltln) => bot_pred
                            | (_, False_ltln) => bot_pred
                            | (_, Prop_ltln _) => bot_pred
                            | (_, Nprop_ltln _) => bot_pred
                            | (_, And_ltln (_, _)) => bot_pred
                            | (_, Or_ltln (_, _)) => bot_pred
                            | (_, Next_ltln _) => bot_pred
                            | (phi, Until_ltln (_, chi)) =>
                              bindb (syntactical_implies_i_i A_ phi chi)
                                (fn () => single ())
                            | (_, Release_ltln (_, _)) => bot_pred)))
                      (sup_pred
                        (bindb (single (x, xa))
                          (fn a =>
                            (case a of (True_ltln, _) => bot_pred
                              | (False_ltln, _) => bot_pred
                              | (Prop_ltln _, _) => bot_pred
                              | (Nprop_ltln _, _) => bot_pred
                              | (And_ltln (_, _), _) => bot_pred
                              | (Or_ltln (_, _), _) => bot_pred
                              | (Next_ltln _, _) => bot_pred
                              | (Until_ltln (phi, psi), chi) =>
                                bindb (syntactical_implies_i_i A_ phi chi)
                                  (fn () =>
                                    bindb (syntactical_implies_i_i A_ psi chi)
                                      (fn () => single ()))
                              | (Release_ltln (_, _), _) => bot_pred)))
                        (sup_pred
                          (bindb (single (x, xa))
                            (fn a =>
                              (case a of (True_ltln, _) => bot_pred
                                | (False_ltln, _) => bot_pred
                                | (Prop_ltln _, _) => bot_pred
                                | (Nprop_ltln _, _) => bot_pred
                                | (And_ltln (_, _), _) => bot_pred
                                | (Or_ltln (_, _), _) => bot_pred
                                | (Next_ltln _, _) => bot_pred
                                | (Until_ltln (_, _), True_ltln) => bot_pred
                                | (Until_ltln (_, _), False_ltln) => bot_pred
                                | (Until_ltln (_, _), Prop_ltln _) => bot_pred
                                | (Until_ltln (_, _), Nprop_ltln _) => bot_pred
                                | (Until_ltln (_, _), And_ltln (_, _)) =>
                                  bot_pred
                                | (Until_ltln (_, _), Or_ltln (_, _)) =>
                                  bot_pred
                                | (Until_ltln (_, _), Next_ltln _) => bot_pred
                                | (Until_ltln (phi, psi), Until_ltln (chi, nu))
                                  => bindb (syntactical_implies_i_i A_ phi chi)
                                       (fn () =>
 bindb (syntactical_implies_i_i A_ psi nu) (fn () => single ()))
                                | (Until_ltln (_, _), Release_ltln (_, _)) =>
                                  bot_pred
                                | (Release_ltln (_, _), _) => bot_pred)))
                          (sup_pred
                            (bindb (single (x, xa))
                              (fn a =>
                                (case a of (True_ltln, _) => bot_pred
                                  | (False_ltln, _) => bot_pred
                                  | (Prop_ltln _, _) => bot_pred
                                  | (Nprop_ltln _, _) => bot_pred
                                  | (And_ltln (_, _), _) => bot_pred
                                  | (Or_ltln (_, _), _) => bot_pred
                                  | (Next_ltln _, _) => bot_pred
                                  | (Until_ltln (_, _), _) => bot_pred
                                  | (Release_ltln (_, chi), phi) =>
                                    bindb (syntactical_implies_i_i A_ chi phi)
                                      (fn () => single ()))))
                            (sup_pred
                              (bindb (single (x, xa))
                                (fn a =>
                                  (case a of (_, True_ltln) => bot_pred
                                    | (_, False_ltln) => bot_pred
                                    | (_, Prop_ltln _) => bot_pred
                                    | (_, Nprop_ltln _) => bot_pred
                                    | (_, And_ltln (_, _)) => bot_pred
                                    | (_, Or_ltln (_, _)) => bot_pred
                                    | (_, Next_ltln _) => bot_pred
                                    | (_, Until_ltln (_, _)) => bot_pred
                                    | (chi, Release_ltln (phi, psi)) =>
                                      bindb (syntactical_implies_i_i A_ chi phi)
(fn () => bindb (syntactical_implies_i_i A_ chi psi) (fn () => single ())))))
                              (sup_pred
                                (bindb (single (x, xa))
                                  (fn a =>
                                    (case a of (True_ltln, _) => bot_pred
                                      | (False_ltln, _) => bot_pred
                                      | (Prop_ltln _, _) => bot_pred
                                      | (Nprop_ltln _, _) => bot_pred
                                      | (And_ltln (_, _), _) => bot_pred
                                      | (Or_ltln (_, _), _) => bot_pred
                                      | (Next_ltln _, _) => bot_pred
                                      | (Until_ltln (_, _), _) => bot_pred
                                      | (Release_ltln (_, _), True_ltln) =>
bot_pred
                                      | (Release_ltln (_, _), False_ltln) =>
bot_pred
                                      | (Release_ltln (_, _), Prop_ltln _) =>
bot_pred
                                      | (Release_ltln (_, _), Nprop_ltln _) =>
bot_pred
                                      | (Release_ltln (_, _), And_ltln (_, _))
=> bot_pred
                                      | (Release_ltln (_, _), Or_ltln (_, _)) =>
bot_pred
                                      | (Release_ltln (_, _), Next_ltln _) =>
bot_pred
                                      | (Release_ltln (_, _), Until_ltln (_, _))
=> bot_pred
                                      |
(Release_ltln (phi, psi), Release_ltln (chi, nu)) =>
bindb (syntactical_implies_i_i A_ phi chi)
  (fn () => bindb (syntactical_implies_i_i A_ psi nu) (fn () => single ())))))
                                (sup_pred
                                  (bindb (single (x, xa))
                                    (fn a =>
                                      (case a of (True_ltln, _) => bot_pred
| (False_ltln, _) => bot_pred | (Prop_ltln _, _) => bot_pred
| (Nprop_ltln _, _) => bot_pred | (And_ltln (_, _), _) => bot_pred
| (Or_ltln (_, _), _) => bot_pred | (Next_ltln _, _) => bot_pred
| (Until_ltln (_, _), _) => bot_pred
| (Release_ltln (True_ltln, _), _) => bot_pred
| (Release_ltln (False_ltln, _), True_ltln) => bot_pred
| (Release_ltln (False_ltln, _), False_ltln) => bot_pred
| (Release_ltln (False_ltln, _), Prop_ltln _) => bot_pred
| (Release_ltln (False_ltln, _), Nprop_ltln _) => bot_pred
| (Release_ltln (False_ltln, _), And_ltln (_, _)) => bot_pred
| (Release_ltln (False_ltln, _), Or_ltln (_, _)) => bot_pred
| (Release_ltln (False_ltln, phi), Next_ltln psi) =>
  bindb (syntactical_implies_i_i A_ (Release_ltln (False_ltln, phi)) psi)
    (fn () => single ())
| (Release_ltln (False_ltln, _), Until_ltln (_, _)) => bot_pred
| (Release_ltln (False_ltln, _), Release_ltln (_, _)) => bot_pred
| (Release_ltln (Prop_ltln _, _), _) => bot_pred
| (Release_ltln (Nprop_ltln _, _), _) => bot_pred
| (Release_ltln (And_ltln (_, _), _), _) => bot_pred
| (Release_ltln (Or_ltln (_, _), _), _) => bot_pred
| (Release_ltln (Next_ltln _, _), _) => bot_pred
| (Release_ltln (Until_ltln (_, _), _), _) => bot_pred
| (Release_ltln (Release_ltln (_, _), _), _) => bot_pred)))
                                  (sup_pred
                                    (bindb (single (x, xa))
                                      (fn a =>
(case a of (True_ltln, _) => bot_pred | (False_ltln, _) => bot_pred
  | (Prop_ltln _, _) => bot_pred | (Nprop_ltln _, _) => bot_pred
  | (And_ltln (_, _), _) => bot_pred | (Or_ltln (_, _), _) => bot_pred
  | (Next_ltln _, True_ltln) => bot_pred | (Next_ltln _, False_ltln) => bot_pred
  | (Next_ltln _, Prop_ltln _) => bot_pred
  | (Next_ltln _, Nprop_ltln _) => bot_pred
  | (Next_ltln _, And_ltln (_, _)) => bot_pred
  | (Next_ltln _, Or_ltln (_, _)) => bot_pred
  | (Next_ltln _, Next_ltln _) => bot_pred
  | (Next_ltln phi, Until_ltln (True_ltln, psi)) =>
    bindb (syntactical_implies_i_i A_ phi (Until_ltln (True_ltln, psi)))
      (fn () => single ())
  | (Next_ltln _, Until_ltln (False_ltln, _)) => bot_pred
  | (Next_ltln _, Until_ltln (Prop_ltln _, _)) => bot_pred
  | (Next_ltln _, Until_ltln (Nprop_ltln _, _)) => bot_pred
  | (Next_ltln _, Until_ltln (And_ltln (_, _), _)) => bot_pred
  | (Next_ltln _, Until_ltln (Or_ltln (_, _), _)) => bot_pred
  | (Next_ltln _, Until_ltln (Next_ltln _, _)) => bot_pred
  | (Next_ltln _, Until_ltln (Until_ltln (_, _), _)) => bot_pred
  | (Next_ltln _, Until_ltln (Release_ltln (_, _), _)) => bot_pred
  | (Next_ltln _, Release_ltln (_, _)) => bot_pred
  | (Until_ltln (_, _), _) => bot_pred | (Release_ltln (_, _), _) => bot_pred)))
                                    (bindb (single (x, xa))
                                      (fn a =>
(case a of (True_ltln, _) => bot_pred | (False_ltln, _) => bot_pred
  | (Prop_ltln _, _) => bot_pred | (Nprop_ltln _, _) => bot_pred
  | (And_ltln (_, _), _) => bot_pred | (Or_ltln (_, _), _) => bot_pred
  | (Next_ltln _, True_ltln) => bot_pred | (Next_ltln _, False_ltln) => bot_pred
  | (Next_ltln _, Prop_ltln _) => bot_pred
  | (Next_ltln _, Nprop_ltln _) => bot_pred
  | (Next_ltln _, And_ltln (_, _)) => bot_pred
  | (Next_ltln _, Or_ltln (_, _)) => bot_pred
  | (Next_ltln phi, Next_ltln psi) =>
    bindb (syntactical_implies_i_i A_ phi psi) (fn () => single ())
  | (Next_ltln _, Until_ltln (_, _)) => bot_pred
  | (Next_ltln _, Release_ltln (_, _)) => bot_pred
  | (Until_ltln (_, _), _) => bot_pred
  | (Release_ltln (_, _), _) => bot_pred)))))))))))))))))));

fun eval A_ (Seq f) = memberb A_ (f ())
and memberb A_ Emptya x = false
  | memberb A_ (Insert (y, p)) x = eq A_ x y orelse eval A_ p x
  | memberb A_ (Join (p, xq)) x = eval A_ p x orelse memberb A_ xq x;

fun holds p = eval equal_unit p ();

fun syntactical_implies A_ x1 x2 = holds (syntactical_implies_i_i A_ x1 x2);

fun remove_release (Release_ltln (x, y)) = remove_release y
  | remove_release (And_ltln (x, y)) =
    And_ltln (remove_release x, remove_release y)
  | remove_release True_ltln = True_ltln
  | remove_release False_ltln = False_ltln
  | remove_release (Prop_ltln v) = Prop_ltln v
  | remove_release (Nprop_ltln v) = Nprop_ltln v
  | remove_release (Or_ltln (v, va)) = Or_ltln (v, va)
  | remove_release (Next_ltln v) = Next_ltln v
  | remove_release (Until_ltln (v, va)) = Until_ltln (v, va);

fun mk_release x y =
  (case x of True_ltln => y
    | False_ltln =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Release_ltln (False_ltln, remove_release y)
        | Nprop_ltln _ => Release_ltln (False_ltln, remove_release y)
        | And_ltln (_, _) => Release_ltln (False_ltln, remove_release y)
        | Or_ltln (_, _) => Release_ltln (False_ltln, remove_release y)
        | Next_ltln _ => Release_ltln (False_ltln, remove_release y)
        | Until_ltln (_, _) => Release_ltln (False_ltln, remove_release y)
        | Release_ltln (_, _) => Release_ltln (False_ltln, remove_release y))
    | Prop_ltln _ =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Release_ltln (x, y)
        | Nprop_ltln _ => Release_ltln (x, y)
        | And_ltln (_, _) => Release_ltln (x, y)
        | Or_ltln (_, _) => Release_ltln (x, y)
        | Next_ltln _ => Release_ltln (x, y)
        | Until_ltln (_, _) => Release_ltln (x, y)
        | Release_ltln (_, _) => Release_ltln (x, y))
    | Nprop_ltln _ =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Release_ltln (x, y)
        | Nprop_ltln _ => Release_ltln (x, y)
        | And_ltln (_, _) => Release_ltln (x, y)
        | Or_ltln (_, _) => Release_ltln (x, y)
        | Next_ltln _ => Release_ltln (x, y)
        | Until_ltln (_, _) => Release_ltln (x, y)
        | Release_ltln (_, _) => Release_ltln (x, y))
    | And_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Release_ltln (x, y)
        | Nprop_ltln _ => Release_ltln (x, y)
        | And_ltln (_, _) => Release_ltln (x, y)
        | Or_ltln (_, _) => Release_ltln (x, y)
        | Next_ltln _ => Release_ltln (x, y)
        | Until_ltln (_, _) => Release_ltln (x, y)
        | Release_ltln (_, _) => Release_ltln (x, y))
    | Or_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Release_ltln (x, y)
        | Nprop_ltln _ => Release_ltln (x, y)
        | And_ltln (_, _) => Release_ltln (x, y)
        | Or_ltln (_, _) => Release_ltln (x, y)
        | Next_ltln _ => Release_ltln (x, y)
        | Until_ltln (_, _) => Release_ltln (x, y)
        | Release_ltln (_, _) => Release_ltln (x, y))
    | Next_ltln _ =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Release_ltln (x, y)
        | Nprop_ltln _ => Release_ltln (x, y)
        | And_ltln (_, _) => Release_ltln (x, y)
        | Or_ltln (_, _) => Release_ltln (x, y)
        | Next_ltln _ => Release_ltln (x, y)
        | Until_ltln (_, _) => Release_ltln (x, y)
        | Release_ltln (_, _) => Release_ltln (x, y))
    | Until_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Release_ltln (x, y)
        | Nprop_ltln _ => Release_ltln (x, y)
        | And_ltln (_, _) => Release_ltln (x, y)
        | Or_ltln (_, _) => Release_ltln (x, y)
        | Next_ltln _ => Release_ltln (x, y)
        | Until_ltln (_, _) => Release_ltln (x, y)
        | Release_ltln (_, _) => Release_ltln (x, y))
    | Release_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Release_ltln (x, y)
        | Nprop_ltln _ => Release_ltln (x, y)
        | And_ltln (_, _) => Release_ltln (x, y)
        | Or_ltln (_, _) => Release_ltln (x, y)
        | Next_ltln _ => Release_ltln (x, y)
        | Until_ltln (_, _) => Release_ltln (x, y)
        | Release_ltln (_, _) => Release_ltln (x, y)));

fun remove_until (Until_ltln (x, y)) = remove_until y
  | remove_until (Or_ltln (x, y)) = Or_ltln (remove_until x, remove_until y)
  | remove_until True_ltln = True_ltln
  | remove_until False_ltln = False_ltln
  | remove_until (Prop_ltln v) = Prop_ltln v
  | remove_until (Nprop_ltln v) = Nprop_ltln v
  | remove_until (And_ltln (v, va)) = And_ltln (v, va)
  | remove_until (Next_ltln v) = Next_ltln v
  | remove_until (Release_ltln (v, va)) = Release_ltln (v, va);

fun mk_until x y =
  (case x
    of True_ltln =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Until_ltln (True_ltln, remove_until y)
        | Nprop_ltln _ => Until_ltln (True_ltln, remove_until y)
        | And_ltln (_, _) => Until_ltln (True_ltln, remove_until y)
        | Or_ltln (_, _) => Until_ltln (True_ltln, remove_until y)
        | Next_ltln _ => Until_ltln (True_ltln, remove_until y)
        | Until_ltln (_, _) => Until_ltln (True_ltln, remove_until y)
        | Release_ltln (_, _) => Until_ltln (True_ltln, remove_until y))
    | False_ltln => y
    | Prop_ltln _ =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Until_ltln (x, y) | Nprop_ltln _ => Until_ltln (x, y)
        | And_ltln (_, _) => Until_ltln (x, y)
        | Or_ltln (_, _) => Until_ltln (x, y) | Next_ltln _ => Until_ltln (x, y)
        | Until_ltln (_, _) => Until_ltln (x, y)
        | Release_ltln (_, _) => Until_ltln (x, y))
    | Nprop_ltln _ =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Until_ltln (x, y) | Nprop_ltln _ => Until_ltln (x, y)
        | And_ltln (_, _) => Until_ltln (x, y)
        | Or_ltln (_, _) => Until_ltln (x, y) | Next_ltln _ => Until_ltln (x, y)
        | Until_ltln (_, _) => Until_ltln (x, y)
        | Release_ltln (_, _) => Until_ltln (x, y))
    | And_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Until_ltln (x, y) | Nprop_ltln _ => Until_ltln (x, y)
        | And_ltln (_, _) => Until_ltln (x, y)
        | Or_ltln (_, _) => Until_ltln (x, y) | Next_ltln _ => Until_ltln (x, y)
        | Until_ltln (_, _) => Until_ltln (x, y)
        | Release_ltln (_, _) => Until_ltln (x, y))
    | Or_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Until_ltln (x, y) | Nprop_ltln _ => Until_ltln (x, y)
        | And_ltln (_, _) => Until_ltln (x, y)
        | Or_ltln (_, _) => Until_ltln (x, y) | Next_ltln _ => Until_ltln (x, y)
        | Until_ltln (_, _) => Until_ltln (x, y)
        | Release_ltln (_, _) => Until_ltln (x, y))
    | Next_ltln _ =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Until_ltln (x, y) | Nprop_ltln _ => Until_ltln (x, y)
        | And_ltln (_, _) => Until_ltln (x, y)
        | Or_ltln (_, _) => Until_ltln (x, y) | Next_ltln _ => Until_ltln (x, y)
        | Until_ltln (_, _) => Until_ltln (x, y)
        | Release_ltln (_, _) => Until_ltln (x, y))
    | Until_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Until_ltln (x, y) | Nprop_ltln _ => Until_ltln (x, y)
        | And_ltln (_, _) => Until_ltln (x, y)
        | Or_ltln (_, _) => Until_ltln (x, y) | Next_ltln _ => Until_ltln (x, y)
        | Until_ltln (_, _) => Until_ltln (x, y)
        | Release_ltln (_, _) => Until_ltln (x, y))
    | Release_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => False_ltln
        | Prop_ltln _ => Until_ltln (x, y) | Nprop_ltln _ => Until_ltln (x, y)
        | And_ltln (_, _) => Until_ltln (x, y)
        | Or_ltln (_, _) => Until_ltln (x, y) | Next_ltln _ => Until_ltln (x, y)
        | Until_ltln (_, _) => Until_ltln (x, y)
        | Release_ltln (_, _) => Until_ltln (x, y)));

fun mk_next x =
  (case x of True_ltln => True_ltln | False_ltln => False_ltln
    | Prop_ltln _ => Next_ltln x | Nprop_ltln _ => Next_ltln x
    | And_ltln (_, _) => Next_ltln x | Or_ltln (_, _) => Next_ltln x
    | Next_ltln _ => Next_ltln x | Until_ltln (_, _) => Next_ltln x
    | Release_ltln (_, _) => Next_ltln x);

fun mk_and x y =
  (case x of True_ltln => y | False_ltln => False_ltln
    | Prop_ltln _ =>
      (case y of True_ltln => x | False_ltln => False_ltln
        | Prop_ltln _ => And_ltln (x, y) | Nprop_ltln _ => And_ltln (x, y)
        | And_ltln (_, _) => And_ltln (x, y) | Or_ltln (_, _) => And_ltln (x, y)
        | Next_ltln _ => And_ltln (x, y) | Until_ltln (_, _) => And_ltln (x, y)
        | Release_ltln (_, _) => And_ltln (x, y))
    | Nprop_ltln _ =>
      (case y of True_ltln => x | False_ltln => False_ltln
        | Prop_ltln _ => And_ltln (x, y) | Nprop_ltln _ => And_ltln (x, y)
        | And_ltln (_, _) => And_ltln (x, y) | Or_ltln (_, _) => And_ltln (x, y)
        | Next_ltln _ => And_ltln (x, y) | Until_ltln (_, _) => And_ltln (x, y)
        | Release_ltln (_, _) => And_ltln (x, y))
    | And_ltln (_, _) =>
      (case y of True_ltln => x | False_ltln => False_ltln
        | Prop_ltln _ => And_ltln (x, y) | Nprop_ltln _ => And_ltln (x, y)
        | And_ltln (_, _) => And_ltln (x, y) | Or_ltln (_, _) => And_ltln (x, y)
        | Next_ltln _ => And_ltln (x, y) | Until_ltln (_, _) => And_ltln (x, y)
        | Release_ltln (_, _) => And_ltln (x, y))
    | Or_ltln (_, _) =>
      (case y of True_ltln => x | False_ltln => False_ltln
        | Prop_ltln _ => And_ltln (x, y) | Nprop_ltln _ => And_ltln (x, y)
        | And_ltln (_, _) => And_ltln (x, y) | Or_ltln (_, _) => And_ltln (x, y)
        | Next_ltln _ => And_ltln (x, y) | Until_ltln (_, _) => And_ltln (x, y)
        | Release_ltln (_, _) => And_ltln (x, y))
    | Next_ltln _ =>
      (case y of True_ltln => x | False_ltln => False_ltln
        | Prop_ltln _ => And_ltln (x, y) | Nprop_ltln _ => And_ltln (x, y)
        | And_ltln (_, _) => And_ltln (x, y) | Or_ltln (_, _) => And_ltln (x, y)
        | Next_ltln _ => And_ltln (x, y) | Until_ltln (_, _) => And_ltln (x, y)
        | Release_ltln (_, _) => And_ltln (x, y))
    | Until_ltln (_, _) =>
      (case y of True_ltln => x | False_ltln => False_ltln
        | Prop_ltln _ => And_ltln (x, y) | Nprop_ltln _ => And_ltln (x, y)
        | And_ltln (_, _) => And_ltln (x, y) | Or_ltln (_, _) => And_ltln (x, y)
        | Next_ltln _ => And_ltln (x, y) | Until_ltln (_, _) => And_ltln (x, y)
        | Release_ltln (_, _) => And_ltln (x, y))
    | Release_ltln (_, _) =>
      (case y of True_ltln => x | False_ltln => False_ltln
        | Prop_ltln _ => And_ltln (x, y) | Nprop_ltln _ => And_ltln (x, y)
        | And_ltln (_, _) => And_ltln (x, y) | Or_ltln (_, _) => And_ltln (x, y)
        | Next_ltln _ => And_ltln (x, y) | Until_ltln (_, _) => And_ltln (x, y)
        | Release_ltln (_, _) => And_ltln (x, y)));

fun mk_or x y =
  (case x of True_ltln => True_ltln | False_ltln => y
    | Prop_ltln _ =>
      (case y of True_ltln => True_ltln | False_ltln => x
        | Prop_ltln _ => Or_ltln (x, y) | Nprop_ltln _ => Or_ltln (x, y)
        | And_ltln (_, _) => Or_ltln (x, y) | Or_ltln (_, _) => Or_ltln (x, y)
        | Next_ltln _ => Or_ltln (x, y) | Until_ltln (_, _) => Or_ltln (x, y)
        | Release_ltln (_, _) => Or_ltln (x, y))
    | Nprop_ltln _ =>
      (case y of True_ltln => True_ltln | False_ltln => x
        | Prop_ltln _ => Or_ltln (x, y) | Nprop_ltln _ => Or_ltln (x, y)
        | And_ltln (_, _) => Or_ltln (x, y) | Or_ltln (_, _) => Or_ltln (x, y)
        | Next_ltln _ => Or_ltln (x, y) | Until_ltln (_, _) => Or_ltln (x, y)
        | Release_ltln (_, _) => Or_ltln (x, y))
    | And_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => x
        | Prop_ltln _ => Or_ltln (x, y) | Nprop_ltln _ => Or_ltln (x, y)
        | And_ltln (_, _) => Or_ltln (x, y) | Or_ltln (_, _) => Or_ltln (x, y)
        | Next_ltln _ => Or_ltln (x, y) | Until_ltln (_, _) => Or_ltln (x, y)
        | Release_ltln (_, _) => Or_ltln (x, y))
    | Or_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => x
        | Prop_ltln _ => Or_ltln (x, y) | Nprop_ltln _ => Or_ltln (x, y)
        | And_ltln (_, _) => Or_ltln (x, y) | Or_ltln (_, _) => Or_ltln (x, y)
        | Next_ltln _ => Or_ltln (x, y) | Until_ltln (_, _) => Or_ltln (x, y)
        | Release_ltln (_, _) => Or_ltln (x, y))
    | Next_ltln _ =>
      (case y of True_ltln => True_ltln | False_ltln => x
        | Prop_ltln _ => Or_ltln (x, y) | Nprop_ltln _ => Or_ltln (x, y)
        | And_ltln (_, _) => Or_ltln (x, y) | Or_ltln (_, _) => Or_ltln (x, y)
        | Next_ltln _ => Or_ltln (x, y) | Until_ltln (_, _) => Or_ltln (x, y)
        | Release_ltln (_, _) => Or_ltln (x, y))
    | Until_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => x
        | Prop_ltln _ => Or_ltln (x, y) | Nprop_ltln _ => Or_ltln (x, y)
        | And_ltln (_, _) => Or_ltln (x, y) | Or_ltln (_, _) => Or_ltln (x, y)
        | Next_ltln _ => Or_ltln (x, y) | Until_ltln (_, _) => Or_ltln (x, y)
        | Release_ltln (_, _) => Or_ltln (x, y))
    | Release_ltln (_, _) =>
      (case y of True_ltln => True_ltln | False_ltln => x
        | Prop_ltln _ => Or_ltln (x, y) | Nprop_ltln _ => Or_ltln (x, y)
        | And_ltln (_, _) => Or_ltln (x, y) | Or_ltln (_, _) => Or_ltln (x, y)
        | Next_ltln _ => Or_ltln (x, y) | Until_ltln (_, _) => Or_ltln (x, y)
        | Release_ltln (_, _) => Or_ltln (x, y)));

fun not_n True_ltln = False_ltln
  | not_n False_ltln = True_ltln
  | not_n (Prop_ltln a) = Nprop_ltln a
  | not_n (Nprop_ltln a) = Prop_ltln a
  | not_n (And_ltln (phi, psi)) = Or_ltln (not_n phi, not_n psi)
  | not_n (Or_ltln (phi, psi)) = And_ltln (not_n phi, not_n psi)
  | not_n (Until_ltln (phi, psi)) = Release_ltln (not_n phi, not_n psi)
  | not_n (Release_ltln (phi, psi)) = Until_ltln (not_n phi, not_n psi)
  | not_n (Next_ltln phi) = Next_ltln (not_n phi);

fun rewrite_syn_imp A_ (And_ltln (phi, psi)) =
  (if syntactical_implies A_ phi psi then rewrite_syn_imp A_ phi
    else (if syntactical_implies A_ psi phi then rewrite_syn_imp A_ psi
           else (if syntactical_implies A_ phi (not_n psi) orelse
                      syntactical_implies A_ psi (not_n phi)
                  then False_ltln
                  else mk_and (rewrite_syn_imp A_ phi)
                         (rewrite_syn_imp A_ psi))))
  | rewrite_syn_imp A_ (Or_ltln (phi, psi)) =
    (if syntactical_implies A_ phi psi then rewrite_syn_imp A_ psi
      else (if syntactical_implies A_ psi phi then rewrite_syn_imp A_ phi
             else (if syntactical_implies A_ (not_n phi) psi orelse
                        syntactical_implies A_ (not_n psi) phi
                    then True_ltln
                    else mk_or (rewrite_syn_imp A_ phi)
                           (rewrite_syn_imp A_ psi))))
  | rewrite_syn_imp A_ (Until_ltln (phi, psi)) =
    (if syntactical_implies A_ phi psi then rewrite_syn_imp A_ psi
      else (if syntactical_implies A_ (not_n phi) psi
             then mk_until True_ltln (rewrite_syn_imp A_ psi)
             else mk_until (rewrite_syn_imp A_ phi) (rewrite_syn_imp A_ psi)))
  | rewrite_syn_imp A_ (Release_ltln (phi, psi)) =
    (if syntactical_implies A_ psi phi then rewrite_syn_imp A_ psi
      else (if syntactical_implies A_ psi (not_n phi)
             then mk_release False_ltln (rewrite_syn_imp A_ psi)
             else mk_release (rewrite_syn_imp A_ phi) (rewrite_syn_imp A_ psi)))
  | rewrite_syn_imp A_ (Next_ltln phi) = mk_next (rewrite_syn_imp A_ phi)
  | rewrite_syn_imp A_ True_ltln = True_ltln
  | rewrite_syn_imp A_ False_ltln = False_ltln
  | rewrite_syn_imp A_ (Prop_ltln v) = Prop_ltln v
  | rewrite_syn_imp A_ (Nprop_ltln v) = Nprop_ltln v;

fun pure_universal A_ True_ltln = true
  | pure_universal A_ False_ltln = true
  | pure_universal A_ (And_ltln (nua, nu)) =
    pure_universal A_ nua andalso pure_universal A_ nu
  | pure_universal A_ (Or_ltln (nua, nu)) =
    pure_universal A_ nua andalso pure_universal A_ nu
  | pure_universal A_ (Until_ltln (nua, nu)) =
    pure_universal A_ nua andalso pure_universal A_ nu
  | pure_universal A_ (Release_ltln (nua, nu)) =
    equal_ltlna A_ nua False_ltln orelse pure_universal A_ nu
  | pure_universal A_ (Next_ltln nu) = pure_universal A_ nu
  | pure_universal A_ (Prop_ltln v) = false
  | pure_universal A_ (Nprop_ltln v) = false;

fun pure_eventual A_ True_ltln = true
  | pure_eventual A_ False_ltln = true
  | pure_eventual A_ (And_ltln (mua, mu)) =
    pure_eventual A_ mua andalso pure_eventual A_ mu
  | pure_eventual A_ (Or_ltln (mua, mu)) =
    pure_eventual A_ mua andalso pure_eventual A_ mu
  | pure_eventual A_ (Until_ltln (mua, mu)) =
    equal_ltlna A_ mua True_ltln orelse pure_eventual A_ mu
  | pure_eventual A_ (Release_ltln (mua, mu)) =
    pure_eventual A_ mua andalso pure_eventual A_ mu
  | pure_eventual A_ (Next_ltln mu) = pure_eventual A_ mu
  | pure_eventual A_ (Prop_ltln v) = false
  | pure_eventual A_ (Nprop_ltln v) = false;

fun suspendable A_ True_ltln = true
  | suspendable A_ False_ltln = true
  | suspendable A_ (And_ltln (xia, xi)) =
    suspendable A_ xia andalso suspendable A_ xi
  | suspendable A_ (Or_ltln (xia, xi)) =
    suspendable A_ xia andalso suspendable A_ xi
  | suspendable A_ (Until_ltln (phi, xi)) =
    equal_ltlna A_ phi True_ltln andalso pure_universal A_ xi orelse
      suspendable A_ xi
  | suspendable A_ (Release_ltln (phi, xi)) =
    equal_ltlna A_ phi False_ltln andalso pure_eventual A_ xi orelse
      suspendable A_ xi
  | suspendable A_ (Next_ltln xi) = suspendable A_ xi
  | suspendable A_ (Prop_ltln v) = false
  | suspendable A_ (Nprop_ltln v) = false;

fun rewrite_modal A_ True_ltln = True_ltln
  | rewrite_modal A_ False_ltln = False_ltln
  | rewrite_modal A_ (And_ltln (phi, psi)) =
    And_ltln (rewrite_modal A_ phi, rewrite_modal A_ psi)
  | rewrite_modal A_ (Or_ltln (phi, psi)) =
    Or_ltln (rewrite_modal A_ phi, rewrite_modal A_ psi)
  | rewrite_modal A_ (Until_ltln (phi, psi)) =
    (if pure_eventual A_ psi orelse suspendable A_ psi then rewrite_modal A_ psi
      else Until_ltln (rewrite_modal A_ phi, rewrite_modal A_ psi))
  | rewrite_modal A_ (Release_ltln (phi, psi)) =
    (if pure_universal A_ psi orelse suspendable A_ psi
      then rewrite_modal A_ psi
      else Release_ltln (rewrite_modal A_ phi, rewrite_modal A_ psi))
  | rewrite_modal A_ (Next_ltln phi) =
    (if suspendable A_ phi then rewrite_modal A_ phi
      else Next_ltln (rewrite_modal A_ phi))
  | rewrite_modal A_ (Prop_ltln v) = Prop_ltln v
  | rewrite_modal A_ (Nprop_ltln v) = Nprop_ltln v;

val zero_enat : enat = Enat zero_nata;

fun minus_enat (Enat a) Infinity_enat = zero_enat
  | minus_enat Infinity_enat n = Infinity_enat
  | minus_enat (Enat a) (Enat b) = Enat (minus_nat a b);

fun min A_ a b = (if less_eq A_ a b then a else b);

fun funpow n f =
  (if equal_nata n zero_nata then id else f o funpow (minus_nat n one_nata) f);

fun mk_next_pow n x =
  (case x of True_ltln => True_ltln | False_ltln => False_ltln
    | Prop_ltln _ => funpow n Next_ltln x | Nprop_ltln _ => funpow n Next_ltln x
    | And_ltln (_, _) => funpow n Next_ltln x
    | Or_ltln (_, _) => funpow n Next_ltln x
    | Next_ltln _ => funpow n Next_ltln x
    | Until_ltln (_, _) => funpow n Next_ltln x
    | Release_ltln (_, _) => funpow n Next_ltln x);

fun is_constant True_ltln = true
  | is_constant False_ltln = true
  | is_constant (Prop_ltln v) = false
  | is_constant (Nprop_ltln v) = false
  | is_constant (And_ltln (v, va)) = false
  | is_constant (Or_ltln (v, va)) = false
  | is_constant (Next_ltln v) = false
  | is_constant (Until_ltln (v, va)) = false
  | is_constant (Release_ltln (v, va)) = false;

fun the_enat_0 (Enat i) = i
  | the_enat_0 Infinity_enat = zero_nata;

fun combine binop (phi, i) (psi, j) =
  let
    val chi =
      binop (mk_next_pow (the_enat_0 (minus_enat i j)) phi)
        (mk_next_pow (the_enat_0 (minus_enat j i)) psi);
  in
    (chi, (if is_constant chi then Infinity_enat else min ord_enat i j))
  end;

fun eSuc i =
  (case i of Enat n => Enat (suc n) | Infinity_enat => Infinity_enat);

fun rewrite_X_enat True_ltln = (True_ltln, Infinity_enat)
  | rewrite_X_enat False_ltln = (False_ltln, Infinity_enat)
  | rewrite_X_enat (Prop_ltln a) = (Prop_ltln a, zero_enat)
  | rewrite_X_enat (Nprop_ltln a) = (Nprop_ltln a, zero_enat)
  | rewrite_X_enat (And_ltln (phi, psi)) =
    combine mk_and (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (Or_ltln (phi, psi)) =
    combine mk_or (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (Until_ltln (phi, psi)) =
    combine mk_until (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (Release_ltln (phi, psi)) =
    combine mk_release (rewrite_X_enat phi) (rewrite_X_enat psi)
  | rewrite_X_enat (Next_ltln phi) = let
                                       val (phia, n) = rewrite_X_enat phi;
                                     in
                                       (phia, eSuc n)
                                     end;

fun rewrite_X phi = let
                      val t = rewrite_X_enat phi;
                    in
                      mk_next_pow (the_enat_0 (snd t)) (fst t)
                    end;

fun iterate A_ f x n =
  (if equal_nata n zero_nata then x
    else let
           val xa = f x;
         in
           (if eq A_ x xa then x else iterate A_ f xa (minus_nat n one_nata))
         end);

fun rewrite_iter_slow A_ phi =
  iterate (equal_ltln A_) (rewrite_syn_imp A_ o rewrite_modal A_ o rewrite_X)
    phi (size_ltln phi);

fun rewrite_iter_fast A_ phi =
  iterate (equal_ltln A_) (rewrite_modal A_ o rewrite_X) phi (size_ltln phi);

fun simplify A_ Nop = id
  | simplify A_ Fast = rewrite_iter_fast A_
  | simplify A_ Slow = rewrite_iter_slow A_;

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

fun gerth_ltl_to_gba_code (A1_, A2_) phi =
  create_name_igba_code (A1_, A2_) (simplify A1_ Slow (ltlc_to_ltln phi));

fun ltl_to_gba_code (A1_, A2_) cfg = let
                                       val CFG_L2B_GERTHS = cfg;
                                     in
                                       gerth_ltl_to_gba_code (A1_, A2_)
                                     end;

fun igbgi_acc
  (Gen_g_impl_ext
    (gi_V, gi_E, gi_V0, Gen_igbg_impl_ext (igbgi_num_acc, igbgi_acc, more)))
  = igbgi_acc;

fun igbai_L
  (Gen_g_impl_ext
    (gi_V, gi_E, gi_V0,
      Gen_igbg_impl_ext
        (igbgi_num_acc, igbgi_acc, Gen_igba_impl_ext (igbai_L, more))))
  = igbai_L;

fun sai_L (Gen_g_impl_ext (gi_V, gi_E, gi_V0, Gen_sa_impl_ext (sai_L, more))) =
  sai_L;

fun gbav_sys_prod_impl_cava_reorder eqq gi si =
  Gen_g_impl_ext
    ((fn (x, xa) => glist_member eqq x (gi_V gi) andalso gi_V si xa),
      (fn (x, xa) =>
        (if igbai_L gi x (sai_L si xa)
          then maps (fn xaa => map (fn xb => (xb, xaa)) (gi_E gi x))
                 (rev (gi_E si xa))
          else [])),
      maps (fn x => map (fn a => (x, a)) (gi_V0 si)) (gi_V0 gi),
      Gen_igbg_impl_ext
        (igbgi_num_acc gi,
          (fn (x, xa) => (if gi_V si xa then igbgi_acc gi x else bs_empty ())),
          ()));

fun dflt_inter_impl eqq si gi =
  (gbav_sys_prod_impl_cava_reorder eqq gi si, snd);

fun graph_restrict_right_impl memr =
  (fn x => fn xa => fn xb => filter (fn xc => memr xc x) (xa xb));

fun graph_restrict_left_impl meml =
  (fn x => fn xa => fn xb => (if meml xb x then xa xb else []));

fun list_map_pick_remove [] = (raise Fail "undefined")
  | list_map_pick_remove (kv :: l) = (kv, l);

fun list_map_isEmpty x = null x;

fun is_None a = (case a of NONE => true | SOME _ => false);

fun wset_find_path_code (A1_, A2_) e u0 p =
  let
    val x =
      let
        val a =
          foldli u0 (fn _ => true)
            (fn x => fn (a, b) =>
              (map2set_insert (ahm_updateb (eq A1_) (bounded_hashcode_nat A2_))
                 x a,
                list_map_update (eq A1_) x [] b))
            (ahm_emptyb (def_hashmap_size A2_ Type), []);
        val (aa, b) = a;
      in
        (NONE, (aa, b))
      end;
    val a =
      whilea (fn (xb, (_, xd)) => is_None xb andalso not (list_map_isEmpty xd))
        (fn (_, (aa, ba)) =>
          let
            val ((ac, bc), bb) = list_map_pick_remove ba;
          in
            (if p ac then (SOME (rev bc, ac), (aa, bb))
              else let
                     val (ad, bd) =
                       foldli (rev (e ac)) (fn _ => true)
                         (fn xc => fn (ad, bd) =>
                           (if map2set_memb
                                 (ahm_lookupb (eq A1_)
                                   (bounded_hashcode_nat A2_))
                                 xc ad
                             then (ad, bd)
                             else (map2set_insert
                                     (ahm_updateb (eq A1_)
                                       (bounded_hashcode_nat A2_))
                                     xc ad,
                                    (xc, ac :: bc) :: bd)))
                         (aa, bb);
                   in
                     (NONE, (ad, bd))
                   end)
          end)
        x;
    val (aa, (_, _)) = a;
  in
    aa
  end;

fun find_path1_code (A1_, A2_) e u p =
  let
    val a = wset_find_path_code (A1_, A2_) e (e u) p;
  in
    (case a of NONE => NONE | SOME aa => let
   val (ab, b) = aa;
 in
   SOME (u :: ab, b)
 end)
  end;

fun atLeastLessThan_tr emp ins a b =
  let
    val (_, ba) =
      whilea (fn (xc, _) => less_nat xc b)
        (fn (aa, ba) => (plus_nata aa one_nata, ins aa ba)) (a, emp);
  in
    ba
  end;

fun bs_subset_eq s1 s2 =
  (((IntInf.andb (s1, IntInf.notb s2)) : IntInf.int) = (0 : IntInf.int));

fun bs_union s1 s2 = IntInf.orb (s1, s2);

fun bs_eq s1 s2 = ((s1 : IntInf.int) = s2);

fun reconstruct_lasso_tr (A1_, A2_) vr vl g_impl =
  let
    val a =
      let
        val a =
          wset_find_path_code (A1_, A2_)
            (graph_restrict_left_impl (fn x => fn f => f x) vr (gi_E g_impl))
            (gi_V0 g_impl) vl;
      in
        the a
      end;
    val (aa, b) = a;
    val xa =
      atLeastLessThan_tr (bs_empty ()) bs_insert zero_nata
        (igbgi_num_acc g_impl);
    val xb = graph_restrict_right_impl (fn x => fn f => f x) vl (gi_E g_impl);
    val (aaa, (ab, _)) =
      whilea (fn (_, (_, xg)) => not (bs_eq xg xa))
        (fn (aaa, (ab, bb)) =>
          let
            val xd =
              wset_find_path_code (A1_, A2_) xb [aaa]
                (fn ac => not (bs_subset_eq (igbgi_acc g_impl ac) bb));
            val (ac, bc) = the xd;
          in
            (bc, (ab @ ac, bs_union bb (igbgi_acc g_impl bc)))
          end)
        (b, ([], igbgi_acc g_impl b));
    val xd =
      (if is_Nil ab then find_path1_code (A1_, A2_) xb aaa (eq A1_ b)
        else wset_find_path_code (A1_, A2_) xb [aaa] (eq A1_ b));
    val (ac, _) = the xd;
  in
    (aa, ab @ ac)
  end;

fun as_is_empty s = equal_nata (snd s) zero_nata;

fun as_length x = snd x;

fun as_top s = let
                 val a = s;
                 val (aa, n) = a;
               in
                 array_get aa (minus_nat n one_nata)
               end;

fun as_set s i x = let
                     val a = s;
                     val (aa, b) = a;
                   in
                     (array_set aa i x, b)
                   end;

fun as_shrink s =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if less_eq_nat (times_nata (nat_of_integer (128 : IntInf.int)) n)
            (array_length aa) andalso
            less_nat (nat_of_integer (4 : IntInf.int)) n
        then array_shrink aa n else aa);
  in
    (ab, n)
  end;

fun as_pop s = let
                 val a = s;
                 val (aa, n) = a;
               in
                 as_shrink (aa, minus_nat n one_nata)
               end;

fun as_get s i = let
                   val a = s;
                   val (aa, _) = a;
                 in
                   array_get aa i
                 end;

fun select_edge_tr (A1_, A2_) s =
  let
    val (a, (aa, (ab, bb))) = s;
  in
    (if as_is_empty bb then (NONE, (a, (aa, (ab, bb))))
      else let
             val (ac, bc) = as_top bb;
           in
             (if less_eq_nat (as_get aa (minus_nat (as_length aa) one_nata)) ac
               then let
                      val xa = gen_pick (fn x => foldli (id x)) bc;
                      val xb = glist_delete (eq A1_) xa bc;
                      val xc =
                        (if is_Nil xb then as_pop bb
                          else as_set bb (minus_nat (as_length bb) one_nata)
                                 (ac, xb));
                    in
                      (SOME xa, (a, (aa, (ab, xc))))
                    end
               else (NONE, (a, (aa, (ab, bb)))))
           end)
  end;

fun go_is_no_brk_code A_ = (fn x => is_None (fst x));

fun go_is_done_code (A1_, A2_) =
  (fn x => fn xa =>
    (case ahm_lookupb (eq A1_) (bounded_hashcode_nat A2_) x (snd xa)
      of NONE => false
      | SOME i => (if less_eq_int zero_int i then false else true)));

fun as_singleton B_ x = (FArray.IsabelleMapping.array_of_list [x], one B_);

fun as_push s x =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if equal_nata n (array_length aa)
        then array_grow aa
               (max ord_nat (nat_of_integer (4 : IntInf.int))
                 (times_nata (nat_of_integer (2 : IntInf.int)) n))
               x
        else aa);
    val ac = array_set ab n x;
  in
    (ac, plus_nata n one_nata)
  end;

fun push_code (A1_, A2_) g_impl =
  (fn x => fn (xa, (xb, (xc, xd))) =>
    let
      val _ = Gabow_Skeleton_Statistics.newnode ();
      val y_a = as_length xa;
      val y_b = as_push xa x;
      val y_c = as_push xb y_a;
      val y_d =
        ahm_updateb (eq A1_) (bounded_hashcode_nat A2_) x (int_of_nat y_a) xc;
      val y_e =
        (if is_Nil (gi_E g_impl x) then xd
          else as_push xd (y_a, gi_E g_impl x));
    in
      (y_b, (y_c, (y_d, y_e)))
    end);

fun find_max_nat n uu =
  (if equal_nata n zero_nata then zero_nata
    else (if uu (minus_nat n one_nata) then minus_nat n one_nata
           else find_max_nat (minus_nat n one_nata) uu));

fun idx_of_tr (A1_, A2_) s v =
  let
    val (_, (aa, (ab, _))) = v;
    val x =
      let
        val SOME i = ahm_lookupb (eq A1_) (bounded_hashcode_nat A2_) s ab;
        val true = less_eq_int zero_int i;
      in
        nat i
      end;
    val xa = find_max_nat (as_length aa) (fn j => less_eq_nat (as_get aa j) x);
  in
    xa
  end;

fun gto_outer_code A_ = (fn x => fn (_, (_, (_, (xe, _)))) => (x, xe));

fun goinitial_code A_ = (NONE, ahm_emptyb (def_hashmap_size A_ Type));

fun as_take m s = let
                    val a = s;
                    val (aa, n) = a;
                  in
                    (if less_nat m n then as_shrink (aa, m) else (aa, n))
                  end;

fun pop_tr (A1_, A2_) s =
  let
    val (a, (aa, (ab, bb))) = s;
    val x = minus_nat (as_length aa) one_nata;
    val xa =
      let
        val (_, bc) =
          whilea
            (fn (xe, _) =>
              less_nat xe
                (if equal_nata (plus_nata x one_nata) (as_length aa)
                  then as_length a else as_get aa (plus_nata x one_nata)))
            (fn (ac, bc) =>
              (suc ac,
                ahm_updateb (eq A1_) (bounded_hashcode_nat A2_) (as_get a ac)
                  (uminus_int one_inta) bc))
            (as_get aa x, ab);
      in
        bc
      end;
    val xb = as_take (as_top aa) a;
    val xc = as_pop aa;
  in
    (xb, (xc, (xa, bb)))
  end;

fun as_empty B_ uu = (FArray.IsabelleMapping.array_of_list [], zero B_);

fun goBrk_code A_ = fst;

fun un_set_drop_tr es_impl un_impl i a =
  let
    val (_, b) =
      whilea (fn (xc, _) => less_nat xc (as_length a))
        (fn (aa, b) => let
                         val xa = un_impl (as_get a aa) b;
                         val xb = plus_nata aa one_nata;
                       in
                         (xb, xa)
                       end)
        (i, es_impl);
  in
    b
  end;

fun all_interval_nat p i j =
  less_eq_nat j i orelse p i andalso all_interval_nat p (suc i) j;

fun bs_mem i s = test_bit_integer s i;

fun find_ce_tr (A1_, A2_) g_impl =
  let
    val _ = Gabow_Skeleton_Statistics.start ();
    val xa = goinitial_code A2_;
    val xb =
      foldli (id (gi_V0 g_impl)) (go_is_no_brk_code A2_)
        (fn xb => fn sigma =>
          (if not (go_is_done_code (A1_, A2_) xb sigma)
            then let
                   val xc =
                     (NONE,
                       (as_singleton one_nat (igbgi_acc g_impl xb),
                         (as_singleton one_nat xb,
                           (as_singleton one_nat zero_nata,
                             (ahm_updateb (eq A1_) (bounded_hashcode_nat A2_) xb
                                (int_of_nat zero_nata) (snd sigma),
                               (if is_Nil (gi_E g_impl xb)
                                 then as_empty zero_nat ()
                                 else as_singleton one_nat
(zero_nata, gi_E g_impl xb)))))));
                   val a =
                     whilea
                       (fn (xd, xe) =>
                         is_None xd andalso
                           not (as_is_empty let
      val (xaa, (_, (_, _))) = snd xe;
    in
      xaa
    end))
                       (fn (_, b) =>
                         (case let
                                 val (aa, ba) = b;
                                 val (ab, bb) = select_edge_tr (A1_, A2_) ba;
                               in
                                 (ab, (aa, bb))
                               end
                           of (NONE, ba) =>
                             let
                               val a = let
 val (ab, bb) = ba;
 val xg = pop_tr (A1_, A2_) bb;
 val xh = as_pop ab;
                                       in
 (xh, xg)
                                       end;
                             in
                               (NONE, a)
                             end
                           | (SOME xf, ba) =>
                             (if (case ahm_lookupb (eq A1_)
 (bounded_hashcode_nat A2_) xf let
                                 val (_, (_, (xd, _))) = snd ba;
                               in
                                 xd
                               end
                                   of NONE => false
                                   | SOME i =>
                                     (if less_eq_int zero_int i then true
                                       else false))
                               then let
                                      val xg =
let
  val (ab, (ac, (ad, (ae, be)))) = ba;
  val xh = idx_of_tr (A1_, A2_) xf (ac, (ad, (ae, be)));
  val xi = as_take (plus_nata xh one_nata) ad;
  val xj = un_set_drop_tr (bs_empty ()) bs_union xh ab;
  val xk = as_push (as_take xh ab) xj;
in
  (xk, (ac, (xi, (ae, be))))
end;
                                    in
                                      (case
let
  val (ab, _) = xg;
in
  all_interval_nat (fn xca => bs_mem xca (as_top ab)) zero_nata
    (igbgi_num_acc g_impl)
end
of true =>
  let
    val (ab, (ac, (ad, (ae, be)))) = xg;
    val xj =
      (fn xfa =>
        (case ahm_lookupb (eq A1_) (bounded_hashcode_nat A2_) xfa ae
          of NONE => false
          | SOME i =>
            (if less_eq_int zero_int i then less_nat (nat i) (as_top ad)
              else false)));
    val xk =
      (fn xfa =>
        (case ahm_lookupb (eq A1_) (bounded_hashcode_nat A2_) xfa ae
          of NONE => false
          | SOME i =>
            (if less_eq_int zero_int i then less_eq_nat (as_top ad) (nat i)
              else false)));
  in
    (SOME (xj, xk), (ab, (ac, (ad, (ae, be)))))
  end
| false => (NONE, xg))
                                    end
                               else (if not
  (case ahm_lookupb (eq A1_) (bounded_hashcode_nat A2_) xf
          let
            val (_, (_, (xd, _))) = snd ba;
          in
            xd
          end
    of NONE => false
    | SOME i => (if less_eq_int zero_int i then false else true))
                                      then (NONE,
     let
       val (xba, xca) = ba;
     in
       (as_push xba (igbgi_acc g_impl xf), push_code (A1_, A2_) g_impl xf xca)
     end)
                                      else (NONE, ba)))))
                       xc;
                   val (aa, b) = a;
                 in
                   gto_outer_code A2_ aa b
                 end
            else sigma))
        xa;
    val _ = Gabow_Skeleton_Statistics.stop ();
  in
    goBrk_code A2_ xb
  end;

fun find_lasso_tr (A1_, A2_) g_impl =
  let
    val a = find_ce_tr (A1_, A2_) g_impl;
  in
    (case a of NONE => NONE
      | SOME aa => let
                     val (ab, b) = aa;
                     val ac = reconstruct_lasso_tr (A1_, A2_) ab b g_impl;
                   in
                     SOME ac
                   end)
  end;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun hd (x21 :: x22) = x21;

fun lasso_of_prpl prpl = let
                           val (pr, pl) = prpl;
                         in
                           Lasso_ext (pr, hd pl, tl pl, ())
                         end;

fun gabow_find_ce_code (A1_, A2_) =
  map_option (SOME o lasso_of_prpl) o find_lasso_tr (A1_, A2_);

fun degeneralize_ext_impl gi x =
  (if equal_nata (igbgi_num_acc gi) zero_nata
    then Gen_g_impl_ext
           ((fn (xa, xb) => equal_nata xb zero_nata andalso gi_V gi xa),
             (fn (xa, xb) =>
               (if equal_nata xb zero_nata
                 then map (fn xc => (xc, zero_nata)) (gi_E gi xa) else [])),
             map (fn xa => (xa, zero_nata)) (gi_V0 gi),
             Gen_bg_impl_ext
               ((fn (xa, xb) => equal_nata xb zero_nata andalso gi_V gi xa),
                 x gi))
    else Gen_g_impl_ext
           ((fn (xa, xb) => less_nat xb (igbgi_num_acc gi) andalso gi_V gi xa),
             (fn (xa, xb) =>
               (if less_nat xb (igbgi_num_acc gi)
                 then let
                        val y =
                          (if bs_mem xb (igbgi_acc gi xa)
                            then modulo_nata (plus_nata xb one_nata)
                                   (igbgi_num_acc gi)
                            else xb);
                      in
                        map (fn xc => (xc, y)) (gi_E gi xa)
                      end
                 else [])),
             map (fn xa => (xa, zero_nata)) (gi_V0 gi),
             Gen_bg_impl_ext
               ((fn (xa, xb) =>
                  equal_nata xb zero_nata andalso
                    bs_mem zero_nata (igbgi_acc gi xa)),
                 x gi)));

fun equal_blue_witness A_ (REACH (x21, x22)) (CIRC (x31, x32)) = false
  | equal_blue_witness A_ (CIRC (x31, x32)) (REACH (x21, x22)) = false
  | equal_blue_witness A_ NO_CYC (CIRC (x31, x32)) = false
  | equal_blue_witness A_ (CIRC (x31, x32)) NO_CYC = false
  | equal_blue_witness A_ NO_CYC (REACH (x21, x22)) = false
  | equal_blue_witness A_ (REACH (x21, x22)) NO_CYC = false
  | equal_blue_witness A_ (CIRC (x31, x32)) (CIRC (y31, y32)) =
    equal_list A_ x31 y31 andalso equal_list A_ x32 y32
  | equal_blue_witness A_ (REACH (x21, x22)) (REACH (y21, y22)) =
    eq A_ x21 y21 andalso equal_list A_ x22 y22
  | equal_blue_witness A_ NO_CYC NO_CYC = true;

fun new_hashmap_with A_ size = HashMapa (new_array [] size, zero_nata);

fun ahm_emptya A_ = (fn _ => new_hashmap_with A_ (def_hashmap_size A_ Type));

fun ahm_empty_const A_ = HashMap (ahm_emptya A_ ());

fun ahm_empty A_ = (fn _ => ahm_empty_const A_);

fun empty_ahm_basic_ops A_ = ahm_empty A_;

fun ahm_alpha_aux (A1_, A2_) a k =
  map_of A1_ (array_get a (bounded_hashcode_nat A2_ (array_length a) k)) k;

fun ahm_alpha (A1_, A2_) (HashMapa (a, uu)) = ahm_alpha_aux (A1_, A2_) a;

fun ahm_lookupa (A1_, A2_) k hm = ahm_alpha (A1_, A2_) hm k;

fun impl_ofa B_ (HashMap x) = x;

fun ahm_lookup (A1_, A2_) k hm = ahm_lookupa (A1_, A2_) k (impl_ofa A2_ hm);

fun memb_ahm_basic_ops (A1_, A2_) x s =
  not (is_none (ahm_lookup (A1_, A2_) x s));

fun delete A_ k = filter (fn (ka, _) => not (eq A_ k ka));

fun ahm_deletea (A1_, A2_) k (HashMapa (a, n)) =
  let
    val h = bounded_hashcode_nat A2_ (array_length a) k;
    val m = array_get a h;
    val deleted = not (is_none (map_of A1_ m k));
  in
    HashMapa
      (array_set a h (delete A1_ k m),
        (if deleted then minus_nat n one_nata else n))
  end;

fun ahm_delete (A1_, A2_) k hm =
  HashMap (ahm_deletea (A1_, A2_) k (impl_ofa A2_ hm));

fun delete_ahm_basic_ops (A1_, A2_) x s = ahm_delete (A1_, A2_) x s;

fun bgi_F (Gen_g_impl_ext (gi_V, gi_E, gi_V0, Gen_bg_impl_ext (bgi_F, more))) =
  bgi_F;

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if eq A_ (fst p) k then (k, v) :: ps else p :: update A_ k v ps);

fun ahm_update_aux (A1_, A2_) (HashMapa (a, n)) k v =
  let
    val h = bounded_hashcode_nat A2_ (array_length a) k;
    val m = array_get a h;
    val insert = is_none (map_of A1_ m k);
  in
    HashMapa
      (array_set a h (update A1_ k v m),
        (if insert then plus_nata n one_nata else n))
  end;

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

fun ahm_filled A_ (HashMapa (a, n)) =
  less_eq_nat (times_nata (array_length a) load_factor)
    (times_nata n (nat_of_integer (100 : IntInf.int)));

fun hm_grow A_ (HashMapa (a, n)) =
  plus_nata (times_nata (nat_of_integer (2 : IntInf.int)) (array_length a))
    (nat_of_integer (3 : IntInf.int));

fun ahm_updatea (A1_, A2_) k v hm =
  let
    val hma = ahm_update_aux (A1_, A2_) hm k v;
  in
    (if ahm_filled A2_ hma then ahm_rehash A2_ hma (hm_grow A2_ hma) else hma)
  end;

fun ahm_update (A1_, A2_) k v hm =
  HashMap (ahm_updatea (A1_, A2_) k v (impl_ofa A2_ hm));

fun ins_ahm_basic_ops (A1_, A2_) x s = ahm_update (A1_, A2_) x () s;

fun init_wit_blue_early A_ s t =
  (if eq A_ s t then CIRC ([], [s]) else REACH (t, [s]));

fun red_init_witness u v = SOME ([u], v);

fun prep_wit_red v NONE = NONE
  | prep_wit_red v (SOME (p, u)) = SOME (v :: p, u);

fun code_red_dfs_ahs_0 (A1_, A2_) e onstack x =
  let
    val (a, b) = x;
    val xa = ins_ahm_basic_ops (A1_, A2_) b a;
  in
    dbind (DRETURN (NDFS_SI_Statistics.vis_red ()))
      (fn _ =>
        dbind (dbind (DRETURN (id (e b)))
                (fn xs =>
                  foldli xs
                    (fn aa =>
                      (case aa of DSUCCEEDi => false | DFAILi => false
                        | DRETURN ab => is_None ab))
                    (fn xb => fn s =>
                      dbind s
                        (fn _ =>
                          (if memb_ahm_basic_ops (A1_, A2_) xb onstack
                            then DRETURN (red_init_witness b xb)
                            else DRETURN NONE)))
                    (DRETURN NONE)))
          (fn xc =>
            (case xc
              of NONE =>
                dbind (DRETURN (id (e b)))
                  (fn xs =>
                    foldli xs
                      (fn aa =>
                        (case aa of DSUCCEEDi => false | DFAILi => false
                          | DRETURN ab => let
    val (_, ac) = ab;
  in
    is_None ac
  end))
                      (fn xb => fn s =>
                        dbind s
                          (fn (aa, _) =>
                            (if not (memb_ahm_basic_ops (A1_, A2_) xb aa)
                              then dbind (code_red_dfs_ahs_0 (A1_, A2_) e
   onstack (aa, xb))
                                     (fn (ab, bb) =>
                                       DRETURN (ab, prep_wit_red b bb))
                              else DRETURN (aa, NONE))))
                      (DRETURN (xa, NONE)))
              | SOME _ => DRETURN (xa, xc))))
  end;

fun code_red_dfs_ahs (A1_, A2_) e onstack v u =
  the_res (code_red_dfs_ahs_0 (A1_, A2_) e onstack (v, u));

fun prep_wit_blue A_ u0 NO_CYC = NO_CYC
  | prep_wit_blue A_ u0 (REACH (u, p)) =
    (if eq A_ u0 u then CIRC ([], u0 :: p) else REACH (u, u0 :: p))
  | prep_wit_blue A_ u0 (CIRC (pr, pl)) = CIRC (u0 :: pr, pl);

fun init_wit_blue A_ u0 NONE = NO_CYC
  | init_wit_blue A_ u0 (SOME (p, u)) =
    (if eq A_ u u0 then CIRC ([], p) else REACH (u, p));

fun code_blue_dfs_ahs_0 (A1_, A2_) g x =
  let
    val (ab, (ac, (ad, bd))) = x;
    val xc = ins_ahm_basic_ops (A1_, A2_) bd ab;
    val xd = ins_ahm_basic_ops (A1_, A2_) bd ad;
    val xe = bgi_F g bd;
  in
    dbind (DRETURN (NDFS_SI_Statistics.vis_blue ()))
      (fn _ =>
        dbind (dbind (DRETURN (id (gi_E g bd)))
                (fn xs =>
                  foldli xs
                    (fn a =>
                      (case a of DSUCCEEDi => false | DFAILi => false
                        | DRETURN (_, (_, (_, xo))) =>
                          equal_blue_witness A1_ xo NO_CYC))
                    (fn xa => fn s =>
                      dbind s
                        (fn (ae, (af, (ag, bg))) =>
                          (if memb_ahm_basic_ops (A1_, A2_) xa ag andalso
                                (xe orelse bgi_F g xa)
                            then DRETURN
                                   (ae, (af,
  (ag, init_wit_blue_early A1_ bd xa)))
                            else (if not (memb_ahm_basic_ops (A1_, A2_) xa ae)
                                   then dbind
  (code_blue_dfs_ahs_0 (A1_, A2_) g (ae, (af, (ag, xa))))
  (fn (ah, (ai, (aj, bj))) => DRETURN (ah, (ai, (aj, prep_wit_blue A1_ bd bj))))
                                   else dbind
  (DRETURN (NDFS_SI_Statistics.match_blue ()))
  (fn _ => DRETURN (ae, (af, (ag, bg))))))))
                    (DRETURN (xc, (ac, (xd, NO_CYC))))))
          (fn (ae, (af, (ag, bg))) =>
            dbind (if equal_blue_witness A1_ bg NO_CYC andalso xe
                    then dbind (DRETURN
                                 (code_red_dfs_ahs (A1_, A2_) (gi_E g) ag af
                                   bd))
                           (fn (ah, bh) =>
                             DRETURN (ah, init_wit_blue A1_ bd bh))
                    else DRETURN (af, bg))
              (fn (ah, bh) =>
                let
                  val xi = delete_ahm_basic_ops (A1_, A2_) bd ag;
                in
                  DRETURN (ae, (ah, (xi, bh)))
                end)))
  end;

fun extract_res cyc =
  (case cyc of NO_CYC => NONE | REACH (_, _) => NONE
    | CIRC (pr, pl) => SOME (pr, pl));

fun code_blue_dfs_ahs (A1_, A2_) g =
  the_res
    (dbind (DRETURN (NDFS_SI_Statistics.start ()))
      (fn _ =>
        dbind (dbind (DRETURN (id (gi_V0 g)))
                (fn xs =>
                  foldli xs
                    (fn a =>
                      (case a of DSUCCEEDi => false | DFAILi => false
                        | DRETURN (_, (_, xd)) =>
                          equal_blue_witness A1_ xd NO_CYC))
                    (fn x => fn s =>
                      dbind s
                        (fn (a, (aa, _)) =>
                          (if not (memb_ahm_basic_ops (A1_, A2_) x a)
                            then dbind (code_blue_dfs_ahs_0 (A1_, A2_) g
 (a, (aa, (empty_ahm_basic_ops A2_ (), x))))
                                   (fn (ab, (ac, (_, bd))) =>
                                     DRETURN (ab, (ac, bd)))
                            else DRETURN (a, (aa, NO_CYC)))))
                    (DRETURN
                      (empty_ahm_basic_ops A2_ (),
                        (empty_ahm_basic_ops A2_ (), NO_CYC)))))
          (fn (_, (_, ba)) =>
            dbind (DRETURN (NDFS_SI_Statistics.stop ()))
              (fn _ => DRETURN (extract_res ba)))));

fun lasso_reach (Lasso_ext (lasso_reach, lasso_va, lasso_cysfx, more)) =
  lasso_reach;

fun lasso_cysfx (Lasso_ext (lasso_reach, lasso_va, lasso_cysfx, more)) =
  lasso_cysfx;

fun lasso_va (Lasso_ext (lasso_reach, lasso_va, lasso_cysfx, more)) = lasso_va;

fun map_lasso f l =
  Lasso_ext (map f (lasso_reach l), f (lasso_va l), map f (lasso_cysfx l), ());

fun ndfs_find_ce_code (A1_, A2_) g =
  let
    val x = degeneralize_ext_impl g (fn _ => ());
  in
    (case code_blue_dfs_ahs
            (equal_prod A1_ equal_nat, hashable_prod A2_ hashable_nat) x
      of NONE => NONE
      | SOME xb => SOME (SOME (map_lasso fst (lasso_of_prpl xb))))
  end;

fun find_ce_code (A1_, A2_) cfg =
  (case cfg of CFG_CE_SCC_GABOW => gabow_find_ce_code (A1_, A2_)
    | CFG_CE_NDFS => ndfs_find_ce_code (A1_, A2_));

fun impl_model_check_ltl_to_gba_code_uu_find_ce_code_map_lasso (A1_, A2_)
  (B1_, B2_) cfg sys phi =
  let
    val ba = ltl_to_gba_code (B1_, B2_) (cfg_l2b cfg) (Not_ltlc phi);
    val (g, map_q) = dflt_inter_impl equal_nata sys ba;
  in
    (case find_ce_code
            (equal_prod equal_nat A1_, hashable_prod hashable_nat A2_)
            (cfg_ce cfg) g
      of NONE => NONE | SOME NONE => SOME NONE
      | SOME (SOME ce) => SOME (SOME (map_lasso map_q ce)))
  end;

fun cava_sys_agn (A1_, A2_) (B1_, B2_) =
  impl_model_check_ltl_to_gba_code_uu_find_ce_code_map_lasso (A1_, A2_)
    (B1_, B2_);

fun processes_update processesa (Program_ext (processes, global_vars, more)) =
  Program_ext (processesa processes, global_vars, more);

fun body_update bodya (Proc_decl_ext (name, body, local_vars, more)) =
  Proc_decl_ext (name, bodya body, local_vars, more);

fun dloc_exp l (E_var x) =
  (if member equal_literal x l then E_localvar x else E_globalvar x)
  | dloc_exp uu (E_localvar x) = E_localvar x
  | dloc_exp uv (E_globalvar x) = E_globalvar x
  | dloc_exp uw (E_const c) = E_const c
  | dloc_exp l (E_bin (bop, e1, e2)) = E_bin (bop, dloc_exp l e1, dloc_exp l e2)
  | dloc_exp l (E_un (uop, e)) = E_un (uop, dloc_exp l e);

fun dloc_cmd l (Assign (c, x, e)) =
  (if member equal_literal x l
    then (fn a => fn b => fn ca => Assign_local (a, b, ca))
    else (fn a => fn b => fn ca => Assign_global (a, b, ca)))
    (dloc_exp l c)
    x
    (dloc_exp l e)
  | dloc_cmd l (Assign_local (c, x, e)) =
    Assign_local (dloc_exp l c, x, dloc_exp l e)
  | dloc_cmd l (Assign_global (c, x, e)) =
    Assign_global (dloc_exp l c, x, dloc_exp l e)
  | dloc_cmd l (Test e) = Test (dloc_exp l e)
  | dloc_cmd l Skip = Skip
  | dloc_cmd l (Seqa (c1, c2)) = Seqa (dloc_cmd l c1, dloc_cmd l c2)
  | dloc_cmd l (Or (c1, c2)) = Or (dloc_cmd l c1, dloc_cmd l c2)
  | dloc_cmd l Break = Break
  | dloc_cmd l Continue = Continue
  | dloc_cmd l (Iterate (c1, c2)) = Iterate (dloc_cmd l c1, dloc_cmd l c2)
  | dloc_cmd l Invalid = Invalid;

fun dloc_proc pd = body_update (dloc_cmd (Set (local_vars pd))) pd;

fun dloc x = processes_update (map dloc_proc) x;

fun cava_sm cfg prog phi =
  let
    val proga = dloc prog;
  in
    (if ty_program proga andalso ltlc_next_free phi
      then (case cava_sys_agn
                   (equal_pid_global_config_ext equal_nat
                      (equal_local_state_impl_ext equal_unit)
                      (equal_global_state_impl_ext equal_unit) equal_unit,
                     hashable_pid_global_config_ext hashable_nat
                       (hashable_local_state_impl_ext hashable_unit)
                       (hashable_global_state_impl_ext hashable_unit)
                       hashable_unit)
                   (equal_exp, linorder_exp) cfg
                   (sm_to_sa_impl proga
                     (fn x => member equal_literal x (vars_of_ltlc phi)))
                   phi
             of NONE => SAT
             | SOME a => (case a of NONE => UNSAT | SOME aa => UNSAT_CE aa))
      else TY_ERR)
  end;

fun test n = cava_sm dflt_cfg mulog_program mulog_property;

fun joina (x :: y :: xs) a = x :: a :: joina (y :: xs) a
  | joina [] a = []
  | joina [v] a = [v];

fun literal_concat xs = foldr (fn a => fn b => a ^ b) xs "";

fun ordered_keys A_ (Mapping t) = keys A_ t;

fun nat_to_string n =
  (if equal_nata n zero_nata then "0"
    else (if equal_nata (minus_nat n one_nata) zero_nata then "1"
           else (if equal_nata (minus_nat (minus_nat n one_nata) one_nata)
                      zero_nata
                  then "2"
                  else (if equal_nata
                             (minus_nat
                               (minus_nat (minus_nat n one_nata) one_nata)
                               one_nata)
                             zero_nata
                         then "3" else "many"))));

fun get_assignments v =
  map (fn k =>
        k ^ " = " ^
          nat_to_string (nat_of_uint32 (the (lookupa linorder_literal v k))))
    (ordered_keys linorder_literal v);

fun show_state s =
  let
    val gvals = variablesa (statea s);
    val lvals = map (variables o state) (processesa s);
  in
    literal_concat (joina (maps get_assignments (gvals :: lvals)) ", ")
  end;

fun remdups_adj A_ [] = []
  | remdups_adj A_ [x] = [x]
  | remdups_adj A_ (x :: y :: xs) =
    (if eq A_ x y then remdups_adj A_ (x :: xs)
      else x :: remdups_adj A_ (y :: xs));

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs =
  (String.implode
    o List.map (fn k => if 0 <= k andalso k < 128 then (Char.chr o IntInf.toInt) k else raise Fail "Non-ASCII character in literal"))
    (map integer_of_char cs);

fun show_ce ce =
  "reach" ^
    implode [Chara (false, true, false, true, false, false, false, false)] ^
    literal_concat
      (joina (remdups_adj equal_literal (map show_state (lasso_reach ce)))
        (implode
          [Chara (false, true, false, true, false, false, false, false)])) ^
    implode [Chara (false, true, false, true, false, false, false, false)] ^
    "va" ^
    implode [Chara (false, true, false, true, false, false, false, false)] ^
    show_state (lasso_va ce) ^
    implode [Chara (false, true, false, true, false, false, false, false)] ^
    "cysfx" ^
    implode [Chara (false, true, false, true, false, false, false, false)] ^
    literal_concat
      (joina (remdups_adj equal_literal (map show_state (lasso_cysfx ce)))
        (implode
          [Chara (false, true, false, true, false, false, false, false)]));

fun int_to_string i =
  (if less_int i zero_int then "-" ^ nat_to_string (nat (uminus_int i))
    else nat_to_string (nat i));

fun bin_op_to_promela Bo_plus = "+"
  | bin_op_to_promela Bo_minus = "-"
  | bin_op_to_promela Bo_mul = "*"
  | bin_op_to_promela Bo_div = "/"
  | bin_op_to_promela Bo_mod = "%"
  | bin_op_to_promela Bo_less = "<"
  | bin_op_to_promela Bo_less_eq = "<="
  | bin_op_to_promela Bo_eq = "=="
  | bin_op_to_promela Bo_and = "&"
  | bin_op_to_promela Bo_or = "|"
  | bin_op_to_promela Bo_xor = "^";

fun un_op_to_promela Uo_minus = "-"
  | un_op_to_promela Uo_not = "~";

fun exp_to_promela (E_var v) = v
  | exp_to_promela (E_localvar v) = v
  | exp_to_promela (E_globalvar v) = v
  | exp_to_promela (E_const i) = int_to_string i
  | exp_to_promela (E_bin (bo, e1, e2)) =
    "(" ^ exp_to_promela e1 ^ " " ^ bin_op_to_promela bo ^ " " ^
      exp_to_promela e2 ^
      ")"
  | exp_to_promela (E_un (uo, e)) =
    "(" ^ un_op_to_promela uo ^ " " ^ exp_to_promela e ^ ")";

fun cmd_to_promela (Assign (c, v, e)) =
  "atomic { " ^ exp_to_promela c ^ " -> " ^ v ^ " = " ^ exp_to_promela e ^ " }"
  | cmd_to_promela (Assign_local (c, v, e)) =
    "atomic { " ^ exp_to_promela c ^ " -> " ^ v ^ " = " ^ exp_to_promela e ^
      " }"
  | cmd_to_promela (Assign_global (c, v, e)) =
    "atomic { " ^ exp_to_promela c ^ " -> " ^ v ^ " = " ^ exp_to_promela e ^
      " }"
  | cmd_to_promela (Test c) = exp_to_promela c
  | cmd_to_promela Skip = "skip"
  | cmd_to_promela (Seqa (c1, c2)) =
    cmd_to_promela c1 ^ "; " ^ cmd_to_promela c2
  | cmd_to_promela (Or (c1, c2)) =
    "if" ^ " :: " ^ cmd_to_promela c1 ^ " :: " ^ cmd_to_promela c2 ^ " fi"
  | cmd_to_promela (Iterate (c1, c2)) =
    (if equal_cmda c1 c2 then "do" ^ " :: " ^ cmd_to_promela c1 ^ " od"
      else (raise Fail "General iterate not supported by promela translator")
             (fn _ => (raise Fail "undefined")));

fun name (Proc_decl_ext (name, body, local_vars, more)) = name;

fun run_process_to_promela proc_decl = "run" ^ " " ^ name proc_decl ^ "()";

fun var_decl_to_promela var_decl = "int" ^ " " ^ var_decl;

fun proc_decl_to_promela proc_decl =
  "proctype" ^ " " ^ name proc_decl ^ "()" ^ " " ^ "{ " ^
    literal_concat
      (join (map var_decl_to_promela (local_vars proc_decl)) "; ") ^
    cmd_to_promela (body proc_decl) ^
    " }";

fun program_to_promela program =
  literal_concat (join (map var_decl_to_promela (global_vars program)) "; ") ^
    literal_concat (map proc_decl_to_promela (processes program)) ^
    "init { " ^
    literal_concat
      (joina (map run_process_to_promela (processes program)) "; ") ^
    " }";

end; (*struct Mulog*)
