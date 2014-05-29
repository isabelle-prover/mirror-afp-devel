
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
      fun newnode () = num_vis := !num_vis + 1

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


structure Fun : sig
  val id : 'a -> 'a
end = struct

fun id x = (fn xa => xa) x;

end; (*struct Fun*)

structure HOL : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
  datatype 'a itself = Type
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

datatype 'a itself = Type;

end; (*struct HOL*)

structure LTL : sig
  datatype 'a ltl = LTLTrue | LTLFalse | LTLProp of 'a | LTLNeg of 'a ltl |
    LTLAnd of 'a ltl * 'a ltl | LTLOr of 'a ltl * 'a ltl | LTLNext of 'a ltl |
    LTLUntil of 'a ltl * 'a ltl | LTLRelease of 'a ltl * 'a ltl
  datatype 'a ltlc = LTLcTrue | LTLcFalse | LTLcProp of 'a | LTLcNeg of 'a ltlc
    | LTLcAnd of 'a ltlc * 'a ltlc | LTLcOr of 'a ltlc * 'a ltlc |
    LTLcImplies of 'a ltlc * 'a ltlc | LTLcIff of 'a ltlc * 'a ltlc |
    LTLcNext of 'a ltlc | LTLcFinal of 'a ltlc | LTLcGlobal of 'a ltlc |
    LTLcUntil of 'a ltlc * 'a ltlc | LTLcRelease of 'a ltlc * 'a ltlc
  datatype 'a ltln = LTLnTrue | LTLnFalse | LTLnProp of 'a | LTLnNProp of 'a |
    LTLnAnd of 'a ltln * 'a ltln | LTLnOr of 'a ltln * 'a ltln |
    LTLnNext of 'a ltln | LTLnUntil of 'a ltln * 'a ltln |
    LTLnRelease of 'a ltln * 'a ltln
  val ltln_rec :
    'a -> 'a -> ('b -> 'a) ->
                  ('b -> 'a) ->
                    ('b ltln -> 'b ltln -> 'a -> 'a -> 'a) ->
                      ('b ltln -> 'b ltln -> 'a -> 'a -> 'a) ->
                        ('b ltln -> 'a -> 'a) ->
                          ('b ltln -> 'b ltln -> 'a -> 'a -> 'a) ->
                            ('b ltln -> 'b ltln -> 'a -> 'a -> 'a) ->
                              'b ltln -> 'a
  val equal_ltlna : 'a HOL.equal -> 'a ltln -> 'a ltln -> bool
  val equal_ltln : 'a HOL.equal -> 'a ltln HOL.equal
  val ltl_pushneg : 'a ltl -> 'a ltl
  val ltl_to_ltln : 'a ltl -> 'a ltln
  val ltlc_to_ltl : 'a ltlc -> 'a ltl
end = struct

datatype 'a ltl = LTLTrue | LTLFalse | LTLProp of 'a | LTLNeg of 'a ltl |
  LTLAnd of 'a ltl * 'a ltl | LTLOr of 'a ltl * 'a ltl | LTLNext of 'a ltl |
  LTLUntil of 'a ltl * 'a ltl | LTLRelease of 'a ltl * 'a ltl;

datatype 'a ltlc = LTLcTrue | LTLcFalse | LTLcProp of 'a | LTLcNeg of 'a ltlc |
  LTLcAnd of 'a ltlc * 'a ltlc | LTLcOr of 'a ltlc * 'a ltlc |
  LTLcImplies of 'a ltlc * 'a ltlc | LTLcIff of 'a ltlc * 'a ltlc |
  LTLcNext of 'a ltlc | LTLcFinal of 'a ltlc | LTLcGlobal of 'a ltlc |
  LTLcUntil of 'a ltlc * 'a ltlc | LTLcRelease of 'a ltlc * 'a ltlc;

datatype 'a ltln = LTLnTrue | LTLnFalse | LTLnProp of 'a | LTLnNProp of 'a |
  LTLnAnd of 'a ltln * 'a ltln | LTLnOr of 'a ltln * 'a ltln |
  LTLnNext of 'a ltln | LTLnUntil of 'a ltln * 'a ltln |
  LTLnRelease of 'a ltln * 'a ltln;

fun ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 LTLnTrue = f1
  | ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 LTLnFalse = f2
  | ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 (LTLnProp a) = f3 a
  | ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 (LTLnNProp a) = f4 a
  | ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 (LTLnAnd (ltln1, ltln2)) =
    f5 ltln1 ltln2 (ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 ltln1)
      (ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 ltln2)
  | ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 (LTLnOr (ltln1, ltln2)) =
    f6 ltln1 ltln2 (ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 ltln1)
      (ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 ltln2)
  | ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 (LTLnNext ltln) =
    f7 ltln (ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 ltln)
  | ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 (LTLnUntil (ltln1, ltln2)) =
    f8 ltln1 ltln2 (ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 ltln1)
      (ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 ltln2)
  | ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 (LTLnRelease (ltln1, ltln2)) =
    f9 ltln1 ltln2 (ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 ltln1)
      (ltln_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 ltln2);

fun equal_ltlna A_ (LTLnRelease (ltln1a, ltln2a)) (LTLnUntil (ltln1, ltln2)) =
  false
  | equal_ltlna A_ (LTLnUntil (ltln1a, ltln2a)) (LTLnRelease (ltln1, ltln2)) =
    false
  | equal_ltlna A_ (LTLnRelease (ltln1, ltln2)) (LTLnNext ltln) = false
  | equal_ltlna A_ (LTLnNext ltln) (LTLnRelease (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnUntil (ltln1, ltln2)) (LTLnNext ltln) = false
  | equal_ltlna A_ (LTLnNext ltln) (LTLnUntil (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnRelease (ltln1a, ltln2a)) (LTLnOr (ltln1, ltln2)) =
    false
  | equal_ltlna A_ (LTLnOr (ltln1a, ltln2a)) (LTLnRelease (ltln1, ltln2)) =
    false
  | equal_ltlna A_ (LTLnUntil (ltln1a, ltln2a)) (LTLnOr (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnOr (ltln1a, ltln2a)) (LTLnUntil (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnNext ltln) (LTLnOr (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnOr (ltln1, ltln2)) (LTLnNext ltln) = false
  | equal_ltlna A_ (LTLnRelease (ltln1a, ltln2a)) (LTLnAnd (ltln1, ltln2)) =
    false
  | equal_ltlna A_ (LTLnAnd (ltln1a, ltln2a)) (LTLnRelease (ltln1, ltln2)) =
    false
  | equal_ltlna A_ (LTLnUntil (ltln1a, ltln2a)) (LTLnAnd (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnAnd (ltln1a, ltln2a)) (LTLnUntil (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnNext ltln) (LTLnAnd (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnAnd (ltln1, ltln2)) (LTLnNext ltln) = false
  | equal_ltlna A_ (LTLnOr (ltln1a, ltln2a)) (LTLnAnd (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnAnd (ltln1a, ltln2a)) (LTLnOr (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnRelease (ltln1, ltln2)) (LTLnNProp a) = false
  | equal_ltlna A_ (LTLnNProp a) (LTLnRelease (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnUntil (ltln1, ltln2)) (LTLnNProp a) = false
  | equal_ltlna A_ (LTLnNProp a) (LTLnUntil (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnNext ltln) (LTLnNProp a) = false
  | equal_ltlna A_ (LTLnNProp a) (LTLnNext ltln) = false
  | equal_ltlna A_ (LTLnOr (ltln1, ltln2)) (LTLnNProp a) = false
  | equal_ltlna A_ (LTLnNProp a) (LTLnOr (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnAnd (ltln1, ltln2)) (LTLnNProp a) = false
  | equal_ltlna A_ (LTLnNProp a) (LTLnAnd (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnRelease (ltln1, ltln2)) (LTLnProp a) = false
  | equal_ltlna A_ (LTLnProp a) (LTLnRelease (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnUntil (ltln1, ltln2)) (LTLnProp a) = false
  | equal_ltlna A_ (LTLnProp a) (LTLnUntil (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnNext ltln) (LTLnProp a) = false
  | equal_ltlna A_ (LTLnProp a) (LTLnNext ltln) = false
  | equal_ltlna A_ (LTLnOr (ltln1, ltln2)) (LTLnProp a) = false
  | equal_ltlna A_ (LTLnProp a) (LTLnOr (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnAnd (ltln1, ltln2)) (LTLnProp a) = false
  | equal_ltlna A_ (LTLnProp a) (LTLnAnd (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnNProp aa) (LTLnProp a) = false
  | equal_ltlna A_ (LTLnProp aa) (LTLnNProp a) = false
  | equal_ltlna A_ (LTLnRelease (ltln1, ltln2)) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnRelease (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnUntil (ltln1, ltln2)) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnUntil (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnNext ltln) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnNext ltln) = false
  | equal_ltlna A_ (LTLnOr (ltln1, ltln2)) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnOr (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnAnd (ltln1, ltln2)) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnAnd (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnNProp a) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnNProp a) = false
  | equal_ltlna A_ (LTLnProp a) LTLnFalse = false
  | equal_ltlna A_ LTLnFalse (LTLnProp a) = false
  | equal_ltlna A_ (LTLnRelease (ltln1, ltln2)) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnRelease (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnUntil (ltln1, ltln2)) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnUntil (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnNext ltln) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnNext ltln) = false
  | equal_ltlna A_ (LTLnOr (ltln1, ltln2)) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnOr (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnAnd (ltln1, ltln2)) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnAnd (ltln1, ltln2)) = false
  | equal_ltlna A_ (LTLnNProp a) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnNProp a) = false
  | equal_ltlna A_ (LTLnProp a) LTLnTrue = false
  | equal_ltlna A_ LTLnTrue (LTLnProp a) = false
  | equal_ltlna A_ LTLnFalse LTLnTrue = false
  | equal_ltlna A_ LTLnTrue LTLnFalse = false
  | equal_ltlna A_ (LTLnRelease (ltln1a, ltln2a)) (LTLnRelease (ltln1, ltln2)) =
    equal_ltlna A_ ltln1a ltln1 andalso equal_ltlna A_ ltln2a ltln2
  | equal_ltlna A_ (LTLnUntil (ltln1a, ltln2a)) (LTLnUntil (ltln1, ltln2)) =
    equal_ltlna A_ ltln1a ltln1 andalso equal_ltlna A_ ltln2a ltln2
  | equal_ltlna A_ (LTLnNext ltlna) (LTLnNext ltln) = equal_ltlna A_ ltlna ltln
  | equal_ltlna A_ (LTLnOr (ltln1a, ltln2a)) (LTLnOr (ltln1, ltln2)) =
    equal_ltlna A_ ltln1a ltln1 andalso equal_ltlna A_ ltln2a ltln2
  | equal_ltlna A_ (LTLnAnd (ltln1a, ltln2a)) (LTLnAnd (ltln1, ltln2)) =
    equal_ltlna A_ ltln1a ltln1 andalso equal_ltlna A_ ltln2a ltln2
  | equal_ltlna A_ (LTLnNProp aa) (LTLnNProp a) = HOL.eq A_ aa a
  | equal_ltlna A_ (LTLnProp aa) (LTLnProp a) = HOL.eq A_ aa a
  | equal_ltlna A_ LTLnFalse LTLnFalse = true
  | equal_ltlna A_ LTLnTrue LTLnTrue = true;

fun equal_ltln A_ = {equal = equal_ltlna A_} : 'a ltln HOL.equal;

fun ltl_pushneg LTLTrue = LTLTrue
  | ltl_pushneg LTLFalse = LTLFalse
  | ltl_pushneg (LTLProp q) = LTLProp q
  | ltl_pushneg (LTLNeg LTLTrue) = LTLFalse
  | ltl_pushneg (LTLNeg LTLFalse) = LTLTrue
  | ltl_pushneg (LTLNeg (LTLProp q)) = LTLNeg (LTLProp q)
  | ltl_pushneg (LTLNeg (LTLNeg psi)) = ltl_pushneg psi
  | ltl_pushneg (LTLNeg (LTLAnd (nu, mu))) =
    LTLOr (ltl_pushneg (LTLNeg nu), ltl_pushneg (LTLNeg mu))
  | ltl_pushneg (LTLNeg (LTLOr (nu, mu))) =
    LTLAnd (ltl_pushneg (LTLNeg nu), ltl_pushneg (LTLNeg mu))
  | ltl_pushneg (LTLNeg (LTLNext psi)) = LTLNext (ltl_pushneg (LTLNeg psi))
  | ltl_pushneg (LTLNeg (LTLUntil (nu, mu))) =
    LTLRelease (ltl_pushneg (LTLNeg nu), ltl_pushneg (LTLNeg mu))
  | ltl_pushneg (LTLNeg (LTLRelease (nu, mu))) =
    LTLUntil (ltl_pushneg (LTLNeg nu), ltl_pushneg (LTLNeg mu))
  | ltl_pushneg (LTLAnd (phi, psi)) = LTLAnd (ltl_pushneg phi, ltl_pushneg psi)
  | ltl_pushneg (LTLOr (phi, psi)) = LTLOr (ltl_pushneg phi, ltl_pushneg psi)
  | ltl_pushneg (LTLNext phi) = LTLNext (ltl_pushneg phi)
  | ltl_pushneg (LTLUntil (phi, psi)) =
    LTLUntil (ltl_pushneg phi, ltl_pushneg psi)
  | ltl_pushneg (LTLRelease (phi, psi)) =
    LTLRelease (ltl_pushneg phi, ltl_pushneg psi);

fun ltl_to_ltln LTLTrue = LTLnTrue
  | ltl_to_ltln LTLFalse = LTLnFalse
  | ltl_to_ltln (LTLProp q) = LTLnProp q
  | ltl_to_ltln (LTLNeg (LTLProp q)) = LTLnNProp q
  | ltl_to_ltln (LTLAnd (phi, psi)) = LTLnAnd (ltl_to_ltln phi, ltl_to_ltln psi)
  | ltl_to_ltln (LTLOr (phi, psi)) = LTLnOr (ltl_to_ltln phi, ltl_to_ltln psi)
  | ltl_to_ltln (LTLNext phi) = LTLnNext (ltl_to_ltln phi)
  | ltl_to_ltln (LTLUntil (phi, psi)) =
    LTLnUntil (ltl_to_ltln phi, ltl_to_ltln psi)
  | ltl_to_ltln (LTLRelease (phi, psi)) =
    LTLnRelease (ltl_to_ltln phi, ltl_to_ltln psi);

fun ltlc_to_ltl LTLcTrue = LTLTrue
  | ltlc_to_ltl LTLcFalse = LTLFalse
  | ltlc_to_ltl (LTLcProp q) = LTLProp q
  | ltlc_to_ltl (LTLcNeg phi) = LTLNeg (ltlc_to_ltl phi)
  | ltlc_to_ltl (LTLcAnd (phi, psi)) = LTLAnd (ltlc_to_ltl phi, ltlc_to_ltl psi)
  | ltlc_to_ltl (LTLcOr (phi, psi)) = LTLOr (ltlc_to_ltl phi, ltlc_to_ltl psi)
  | ltlc_to_ltl (LTLcImplies (phi, psi)) =
    LTLOr (LTLNeg (ltlc_to_ltl phi), ltlc_to_ltl psi)
  | ltlc_to_ltl (LTLcIff (phi, psi)) =
    let
      val phia = ltlc_to_ltl phi;
      val psia = ltlc_to_ltl psi;
    in
      LTLAnd (LTLOr (LTLNeg phia, psia), LTLOr (LTLNeg psia, phia))
    end
  | ltlc_to_ltl (LTLcNext phi) = LTLNext (ltlc_to_ltl phi)
  | ltlc_to_ltl (LTLcFinal phi) = LTLUntil (LTLTrue, ltlc_to_ltl phi)
  | ltlc_to_ltl (LTLcGlobal phi) = LTLRelease (LTLFalse, ltlc_to_ltl phi)
  | ltlc_to_ltl (LTLcUntil (phi, psi)) =
    LTLUntil (ltlc_to_ltl phi, ltlc_to_ltl psi)
  | ltlc_to_ltl (LTLcRelease (phi, psi)) =
    LTLRelease (ltlc_to_ltl phi, ltlc_to_ltl psi);

end; (*struct LTL*)

structure Map : sig
  val map_of : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
end = struct

fun map_of A_ ((l, v) :: ps) k =
  (if HOL.eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

end; (*struct Map*)

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

structure Multiset : sig
  val part :
    'b Orderings.linorder ->
      ('a -> 'b) -> 'b -> 'a list -> 'a list * ('a list * 'a list)
end = struct

fun part B_ f pivot (x :: xs) =
  let
    val (lts, (eqs, gts)) = part B_ f pivot xs;
    val xa = f x;
  in
    (if Orderings.less
          ((Orderings.ord_preorder o Orderings.preorder_order o
             Orderings.order_linorder)
            B_)
          xa pivot
      then (x :: lts, (eqs, gts))
      else (if Orderings.less
                 ((Orderings.ord_preorder o Orderings.preorder_order o
                    Orderings.order_linorder)
                   B_)
                 pivot xa
             then (lts, (eqs, x :: gts)) else (lts, (x :: eqs, gts))))
  end
  | part B_ f pivot [] = ([], ([], []));

end; (*struct Multiset*)

structure Arith : sig
  datatype int = Int_of_integer of IntInf.int
  datatype nat = Nat of IntInf.int
  datatype num = One | Bit0 of num | Bit1 of num
  val integer_of_int : int -> IntInf.int
  val ord_integer : IntInf.int Orderings.ord
  val nat : int -> nat
  val integer_of_nat : nat -> IntInf.int
  val plus_nata : nat -> nat -> nat
  val one_nata : nat
  val suc : nat -> nat
  type 'a times
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a dvd
  val times_dvd : 'a dvd -> 'a times
  type 'a one
  val one : 'a one -> 'a
  val times_nata : nat -> nat -> nat
  val times_nat : nat times
  val dvd_nat : nat dvd
  val one_nat : nat one
  val less_eq_nat : nat -> nat -> bool
  val less_nat : nat -> nat -> bool
  val ord_nat : nat Orderings.ord
  type 'a diva
  val dvd_div : 'a diva -> 'a dvd
  val diva : 'a diva -> 'a -> 'a -> 'a
  val moda : 'a diva -> 'a -> 'a -> 'a
  type 'a plus
  val plus : 'a plus -> 'a -> 'a -> 'a
  type 'a zero
  val zero : 'a zero -> 'a
  val plus_nat : nat plus
  val zero_nata : nat
  val zero_nat : nat zero
  type 'a semigroup_add
  val plus_semigroup_add : 'a semigroup_add -> 'a plus
  type 'a numeral
  val one_numeral : 'a numeral -> 'a one
  val semigroup_add_numeral : 'a numeral -> 'a semigroup_add
  val numeral : 'a numeral -> num -> 'a
  type 'a power
  val one_power : 'a power -> 'a one
  val times_power : 'a power -> 'a times
  val minus_nat : nat -> nat -> nat
  val equal_nata : nat -> nat -> bool
  val powera : 'a -> ('a -> 'a -> 'a) -> 'a -> nat -> 'a
  val power : 'a power -> 'a -> nat -> 'a
  val less_int : int -> int -> bool
  val plus_int : int -> int -> int
  val zero_int : int
  val equal_nat : nat HOL.equal
  val preorder_nat : nat Orderings.preorder
  val order_nat : nat Orderings.order
  val sgn_integer : IntInf.int -> IntInf.int
  val abs_integer : IntInf.int -> IntInf.int
  val divmod_integer : IntInf.int -> IntInf.int -> IntInf.int * IntInf.int
  val mod_integer : IntInf.int -> IntInf.int -> IntInf.int
  val mod_nat : nat -> nat -> nat
  val div_integer : IntInf.int -> IntInf.int -> IntInf.int
  val div_nata : nat -> nat -> nat
  val div_nat : nat diva
  val uminus_int : int -> int
  val semigroup_add_nat : nat semigroup_add
  val numeral_nat : nat numeral
  val less_eq_int : int -> int -> bool
  val linorder_nat : nat Orderings.linorder
  val divmod_nat : nat -> nat -> nat * nat
  val one_integera : IntInf.int
  val one_integer : IntInf.int one
  val plus_integer : IntInf.int plus
  val equal_integer : IntInf.int HOL.equal
  val preorder_integer : IntInf.int Orderings.preorder
  val order_integer : IntInf.int Orderings.order
  val times_integer : IntInf.int times
  val power_integer : IntInf.int power
  val int_of_nat : nat -> int
  val nat_of_integer : IntInf.int -> nat
  val semigroup_add_integer : IntInf.int semigroup_add
  val numeral_integer : IntInf.int numeral
  val linorder_integer : IntInf.int Orderings.linorder
end = struct

datatype int = Int_of_integer of IntInf.int;

datatype nat = Nat of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

fun integer_of_int (Int_of_integer k) = k;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int Orderings.ord;

fun nat k = Nat (Orderings.max ord_integer 0 (integer_of_int k));

fun integer_of_nat (Nat x) = x;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nata : nat = Nat (1 : IntInf.int);

fun suc n = plus_nata n one_nata;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

val one_nat = {one = one_nata} : nat one;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat Orderings.ord;

type 'a diva = {dvd_div : 'a dvd, diva : 'a -> 'a -> 'a, moda : 'a -> 'a -> 'a};
val dvd_div = #dvd_div : 'a diva -> 'a dvd;
val diva = #diva : 'a diva -> 'a -> 'a -> 'a;
val moda = #moda : 'a diva -> 'a -> 'a -> 'a;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat 0;

val zero_nat = {zero = zero_nata} : nat zero;

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

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

fun minus_nat m n =
  Nat (Orderings.max ord_integer 0
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

fun powera one times a n =
  (if equal_nata n zero_nata then one
    else times a (powera one times a (minus_nat n one_nata)));

fun power A_ = powera (one (one_power A_)) (times (times_power A_));

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun plus_int k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

val zero_int : int = Int_of_integer 0;

val equal_nat = {equal = equal_nata} : nat HOL.equal;

val preorder_nat = {ord_preorder = ord_nat} : nat Orderings.preorder;

val order_nat = {preorder_order = preorder_nat} : nat Orderings.order;

fun sgn_integer k =
  (if ((k : IntInf.int) = 0) then 0
    else (if IntInf.< (k, 0) then IntInf.~ (1 : IntInf.int)
           else (1 : IntInf.int)));

fun abs_integer k = (if IntInf.< (k, 0) then IntInf.~ k else k);

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

fun mod_integer k l = Product_Type.snd (divmod_integer k l);

fun mod_nat m n = Nat (mod_integer (integer_of_nat m) (integer_of_nat n));

fun div_integer k l = Product_Type.fst (divmod_integer k l);

fun div_nata m n = Nat (div_integer (integer_of_nat m) (integer_of_nat n));

val div_nat = {dvd_div = dvd_nat, diva = div_nata, moda = mod_nat} : nat diva;

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

val linorder_nat = {order_linorder = order_nat} : nat Orderings.linorder;

fun divmod_nat m n = (div_nata m n, mod_nat m n);

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

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

fun int_of_nat n = Int_of_integer (integer_of_nat n);

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
  val filter : ('a -> bool) -> 'a list -> 'a list
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val insert : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val butlast : 'a list -> 'a list
  val remdups : 'a HOL.equal -> 'a list -> 'a list
  val gen_length : Arith.nat -> 'a list -> Arith.nat
  val size_list : 'a list -> Arith.nat
  val sort_key : 'b Orderings.linorder -> ('a -> 'b) -> 'a list -> 'a list
  val enumerate : Arith.nat -> 'a list -> (Arith.nat * 'a) list
  val equal_lista : 'a HOL.equal -> 'a list -> 'a list -> bool
  val equal_list : 'a HOL.equal -> ('a list) HOL.equal
  val replicate : Arith.nat -> 'a -> 'a list
  val insort_key :
    'b Orderings.linorder -> ('a -> 'b) -> 'a -> 'a list -> 'a list
  val list_update : 'a list -> Arith.nat -> 'a -> 'a list
  val all_interval_nat : (Arith.nat -> bool) -> Arith.nat -> Arith.nat -> bool
end = struct

fun hd (x :: xs) = x;

fun tl [] = []
  | tl (x :: xs) = xs;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs;

fun nth (x :: xs) n =
  (if Arith.equal_nata n Arith.zero_nata then x
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

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = HOL.eq A_ x y orelse member A_ xs y;

fun insert A_ x xs = (if member A_ xs x then xs else x :: xs);

fun butlast [] = []
  | butlast (x :: xs) = (if null xs then [] else x :: butlast xs);

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun gen_length n (x :: xs) = gen_length (Arith.suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length Arith.zero_nata x;

fun sort_key B_ f xs =
  (case xs of [] => [] | [x] => xs
    | [x, y] =>
      (if Orderings.less_eq
            ((Orderings.ord_preorder o Orderings.preorder_order o
               Orderings.order_linorder)
              B_)
            (f x) (f y)
        then xs else [y, x])
    | x :: y :: _ :: _ =>
      let
        val (lts, (eqs, gts)) =
          Multiset.part B_ f
            (f (nth xs
                 (Arith.div_nata (size_list xs)
                   (Arith.nat_of_integer (2 : IntInf.int)))))
            xs;
      in
        sort_key B_ f lts @ eqs @ sort_key B_ f gts
      end);

fun enumerate n (x :: xs) = (n, x) :: enumerate (Arith.suc n) xs
  | enumerate n [] = [];

fun equal_lista A_ (a :: lista) [] = false
  | equal_lista A_ [] (a :: lista) = false
  | equal_lista A_ (aa :: listaa) (a :: lista) =
    HOL.eq A_ aa a andalso equal_lista A_ listaa lista
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) HOL.equal;

fun replicate n x =
  (if Arith.equal_nata n Arith.zero_nata then []
    else x :: replicate (Arith.minus_nat n Arith.one_nata) x);

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
    (if Arith.equal_nata i Arith.zero_nata then y :: xs
      else x :: list_update xs (Arith.minus_nat i Arith.one_nata) y);

fun all_interval_nat p i j =
  Arith.less_eq_nat j i orelse p i andalso all_interval_nat p (Arith.suc i) j;

end; (*struct List*)

structure Misc : sig
  val merge :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> 'a list
  val the_default : 'a -> 'a option -> 'a
end = struct

fun merge (A1_, A2_) [] l2 = l2
  | merge (A1_, A2_) (v :: va) [] = v :: va
  | merge (A1_, A2_) (x1 :: l1) (x2 :: l2) =
    (if Orderings.less
          ((Orderings.ord_preorder o Orderings.preorder_order o
             Orderings.order_linorder)
            A2_)
          x1 x2
      then x1 :: merge (A1_, A2_) l1 (x2 :: l2)
      else (if HOL.eq A1_ x1 x2 then x1 :: merge (A1_, A2_) l1 l2
             else x2 :: merge (A1_, A2_) (x1 :: l1) l2));

fun the_default uu (SOME x) = x
  | the_default x NONE = x;

end; (*struct Misc*)

structure AList : sig
  val delete : 'a HOL.equal -> 'a -> ('a * 'b) list -> ('a * 'b) list
  val update : 'a HOL.equal -> 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
end = struct

fun delete A_ k = List.filter (fn (ka, _) => not (HOL.eq A_ k ka));

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if HOL.eq A_ (Product_Type.fst p) k then (k, v) :: ps
      else p :: update A_ k v ps);

end; (*struct AList*)

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

structure Lasso : sig
  datatype ('a, 'b) lasso_ext = Lasso_ext of 'a list * 'a * 'a list * 'b
  val lasso_reach : ('a, 'b) lasso_ext -> 'a list
  val lasso_va : ('a, 'b) lasso_ext -> 'a
  val lasso_v0 : ('a, 'b) lasso_ext -> 'a
  val lasso_cysfx : ('a, 'b) lasso_ext -> 'a list
  val map_lasso : ('a -> 'b) -> ('a, 'c) lasso_ext -> ('b, unit) lasso_ext
  val lasso_cycle : ('a, 'b) lasso_ext -> 'a list
  val lasso_of_prpl : 'a list * 'a list -> ('a, unit) lasso_ext
end = struct

datatype ('a, 'b) lasso_ext = Lasso_ext of 'a list * 'a * 'a list * 'b;

fun lasso_reach (Lasso_ext (lasso_reach, lasso_va, lasso_cysfx, more)) =
  lasso_reach;

fun lasso_va (Lasso_ext (lasso_reach, lasso_va, lasso_cysfx, more)) = lasso_va;

fun lasso_v0 l = (case lasso_reach l of [] => lasso_va l | v0 :: _ => v0);

fun lasso_cysfx (Lasso_ext (lasso_reach, lasso_va, lasso_cysfx, more)) =
  lasso_cysfx;

fun map_lasso f l =
  Lasso_ext
    (List.map f (lasso_reach l), f (lasso_va l), List.map f (lasso_cysfx l),
      ());

fun lasso_cycle l = lasso_va l :: lasso_cysfx l;

fun lasso_of_prpl prpl =
  let
    val (pr, pl) = prpl;
  in
    Lasso_ext (pr, List.hd pl, List.tl pl, ())
  end;

end; (*struct Lasso*)

structure IArray : sig
  val sub : 'a Vector.vector -> Arith.nat -> 'a
  val length : 'a Vector.vector -> Arith.nat
  val list_of : 'a Vector.vector -> 'a list
  val equal_iarray :
    'a HOL.equal -> 'a Vector.vector -> 'a Vector.vector -> bool
end = struct

fun sub asa n = Vector.sub (asa, Arith.integer_of_nat n);

fun length asa = Arith.nat_of_integer (Vector.length asa);

fun list_of asa = List.map (sub asa) (List.upt Arith.zero_nata (length asa));

fun equal_iarray A_ asa bs = List.equal_lista A_ (list_of asa) (list_of bs);

end; (*struct IArray*)

structure Option : sig
  val map : ('a -> 'b) -> 'a option -> 'b option
  val the : 'a option -> 'a
  val is_none : 'a option -> bool
  val equal_option : 'a HOL.equal -> 'a option -> 'a option -> bool
end = struct

fun map f (SOME x) = SOME (f x)
  | map f NONE = NONE;

fun the (SOME x) = x;

fun is_none (SOME x) = false
  | is_none NONE = true;

fun equal_option A_ (SOME a) NONE = false
  | equal_option A_ NONE (SOME a) = false
  | equal_option A_ (SOME aa) (SOME a) = HOL.eq A_ aa a
  | equal_option A_ NONE NONE = true;

end; (*struct Option*)

structure Bit_Int : sig
  val set_bit_integer : IntInf.int -> Arith.nat -> bool -> IntInf.int
  val test_bit_integer : IntInf.int -> Arith.nat -> bool
end = struct

fun set_bit_integer x i b = Bits_Integer.set_bit x (Arith.integer_of_nat i) b;

fun test_bit_integer x n = Bits_Integer.test_bit x (Arith.integer_of_nat n);

end; (*struct Bit_Int*)

structure Gen_Set : sig
  val gen_bex :
    ('a -> (bool -> bool) -> ('b -> 'c -> bool) -> bool -> 'd) ->
      'a -> ('b -> bool) -> 'd
  val gen_ball :
    ('a -> ('b -> 'b) -> ('c -> 'd -> bool) -> bool -> 'e) ->
      'a -> ('c -> bool) -> 'e
  val gen_card :
    'd Arith.zero ->
      ('a -> ('b -> bool) -> ('c -> Arith.nat -> Arith.nat) -> 'd -> 'e) ->
        'a -> 'e
  val gen_pick :
    ('a ->
      ('b option -> bool) ->
        ('c -> 'd -> 'c option) -> 'e option -> 'f option) ->
      'a -> 'f
  val gen_equal : ('a -> 'b -> bool) -> ('b -> 'a -> bool) -> 'a -> 'b -> bool
  val gen_image :
    ('a -> ('b -> bool) -> ('c -> 'd -> 'e) -> 'f -> 'g) ->
      'f -> ('h -> 'd -> 'e) -> ('c -> 'h) -> 'a -> 'g
  val gen_union :
    ('a -> ('b -> bool) -> ('c -> 'd -> 'd) -> 'd -> 'd) ->
      ('c -> 'd -> 'd) -> 'a -> 'd -> 'd
  val gen_subseteq :
    ('a -> ('b -> bool) -> bool) -> ('b -> 'c -> bool) -> 'a -> 'c -> bool
end = struct

fun gen_bex it s p = it s not (fn x => fn _ => p x) false;

fun gen_ball it s p = it s (fn x => x) (fn x => fn _ => p x) true;

fun gen_card D_ it s = it s (fn _ => true) (fn _ => Arith.suc) (Arith.zero D_);

fun gen_pick it s =
  Option.the
    (it s (fn a => (case a of NONE => true | SOME _ => false))
       (fn x => fn _ => SOME x)
      NONE);

fun gen_equal ss1 ss2 s1 s2 = ss1 s1 s2 andalso ss2 s2 s1;

fun gen_image it1 emp2 ins2 f s1 =
  it1 s1 (fn _ => true) (fn x => ins2 (f x)) emp2;

fun gen_union it ins a b = it a (fn _ => true) ins b;

fun gen_subseteq ball1 mem2 s1 s2 = ball1 s1 (fn x => mem2 x s2);

end; (*struct Gen_Set*)

structure Mapping : sig
  datatype ('a, 'b) mapping = Mapping of ('a * 'b) list
  val empty : ('a, 'b) mapping
  val lookup : 'a HOL.equal -> ('a, 'b) mapping -> 'a -> 'b option
  val update : 'a HOL.equal -> 'a -> 'b -> ('a, 'b) mapping -> ('a, 'b) mapping
  val ordered_keys :
    'a HOL.equal * 'a Orderings.linorder -> ('a, 'b) mapping -> 'a list
end = struct

datatype ('a, 'b) mapping = Mapping of ('a * 'b) list;

val empty : ('a, 'b) mapping = Mapping [];

fun lookup A_ (Mapping xs) = Map.map_of A_ xs;

fun update A_ k v (Mapping xs) = Mapping (AList.update A_ k v xs);

fun ordered_keys (A1_, A2_) (Mapping xs) =
  List.sort_key A2_ (fn x => x)
    (List.remdups A1_ (List.map Product_Type.fst xs));

end; (*struct Mapping*)

structure Autoref_Bindings_HOL : sig
  val is_Nil : 'a list -> bool
  val is_None : 'a option -> bool
  val prod_eq :
    ('a -> 'b -> bool) -> ('c -> 'd -> bool) -> 'a * 'c -> 'b * 'd -> bool
end = struct

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun is_None a = (case a of NONE => true | SOME _ => false);

fun prod_eq eqa eqb x1 x2 =
  let
    val (a1, b1) = x1;
    val (a2, b2) = x2;
  in
    eqa a1 a2 andalso eqb b1 b2
  end;

end; (*struct Autoref_Bindings_HOL*)

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

structure Impl_List_Map : sig
  val list_map_lookup : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b option
  val list_map_update_aux :
    ('a -> 'a -> bool) ->
      'a -> 'b -> ('a * 'b) list -> ('a * 'b) list -> ('a * 'b) list
  val list_map_update :
    ('a -> 'a -> bool) -> 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
  val list_map_isEmpty : ('a * 'b) list -> bool
  val list_map_pick_remove : 'a list -> 'a * 'a list
end = struct

fun list_map_lookup eq uu [] = NONE
  | list_map_lookup eq k (y :: ys) =
    (if eq (Product_Type.fst y) k then SOME (Product_Type.snd y)
      else list_map_lookup eq k ys);

fun list_map_update_aux eq k v [] accu = (k, v) :: accu
  | list_map_update_aux eq k v (x :: xs) accu =
    (if eq (Product_Type.fst x) k then (k, v) :: xs @ accu
      else list_map_update_aux eq k v xs (x :: accu));

fun list_map_update eq k v m = list_map_update_aux eq k v m [];

fun list_map_isEmpty x = List.null x;

fun list_map_pick_remove [] = (raise Fail "undefined")
  | list_map_pick_remove (kv :: l) = (kv, l);

end; (*struct Impl_List_Map*)

structure Idx_Iterator : sig
  val idx_iteratei_aux :
    ('a -> Arith.nat -> 'b) ->
      Arith.nat ->
        Arith.nat -> 'a -> ('c -> bool) -> ('b -> 'c -> 'c) -> 'c -> 'c
  val idx_iteratei :
    ('a -> Arith.nat -> 'b) ->
      ('a -> Arith.nat) -> 'a -> ('c -> bool) -> ('b -> 'c -> 'c) -> 'c -> 'c
end = struct

fun idx_iteratei_aux get sz i l c f sigma =
  (if Arith.equal_nata i Arith.zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux get sz (Arith.minus_nat i Arith.one_nata) l c f
           (f (get l (Arith.minus_nat sz i)) sigma));

fun idx_iteratei get sz l c f sigma =
  idx_iteratei_aux get (sz l) (sz l) l c f sigma;

end; (*struct Idx_Iterator*)

structure Diff_Array : sig
  val array_get : 'a FArray.IsabelleMapping.ArrayType -> Arith.nat -> 'a
  val array_set :
    'a FArray.IsabelleMapping.ArrayType ->
      Arith.nat -> 'a -> 'a FArray.IsabelleMapping.ArrayType
  val new_array : 'a -> Arith.nat -> 'a FArray.IsabelleMapping.ArrayType
  val array_grow :
    'a FArray.IsabelleMapping.ArrayType ->
      Arith.nat -> 'a -> 'a FArray.IsabelleMapping.ArrayType
  val array_get_oo :
    'a -> 'a FArray.IsabelleMapping.ArrayType -> Arith.nat -> 'a
  val array_length : 'a FArray.IsabelleMapping.ArrayType -> Arith.nat
  val array_set_oo :
    (unit -> 'a FArray.IsabelleMapping.ArrayType) ->
      'a FArray.IsabelleMapping.ArrayType ->
        Arith.nat -> 'a -> 'a FArray.IsabelleMapping.ArrayType
  val array_shrink :
    'a FArray.IsabelleMapping.ArrayType ->
      Arith.nat -> 'a FArray.IsabelleMapping.ArrayType
end = struct

fun array_get a = FArray.IsabelleMapping.array_get a o Arith.integer_of_nat;

fun array_set a = FArray.IsabelleMapping.array_set a o Arith.integer_of_nat;

fun new_array v = FArray.IsabelleMapping.new_array v o Arith.integer_of_nat;

fun array_grow a = FArray.IsabelleMapping.array_grow a o Arith.integer_of_nat;

fun array_get_oo x a =
  FArray.IsabelleMapping.array_get_oo x a o Arith.integer_of_nat;

fun array_length x =
  (Arith.nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun array_set_oo f a =
  FArray.IsabelleMapping.array_set_oo f a o Arith.integer_of_nat;

fun array_shrink a =
  FArray.IsabelleMapping.array_shrink a o Arith.integer_of_nat;

end; (*struct Diff_Array*)

structure Impl_Array_Hash_Map : sig
  datatype ('a, 'b) hashmap =
    HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * Arith.nat
  val hm_grow : ('a, 'b) hashmap -> Arith.nat
  val new_hashmap_with : Arith.nat -> ('a, 'b) hashmap
  val ahm_empty : Arith.nat -> ('a, 'b) hashmap
  val load_factor : Arith.nat
  val ahm_filled : ('a, 'b) hashmap -> bool
  val ahm_lookup_aux :
    ('a -> 'a -> bool) ->
      (Arith.nat -> 'a -> Arith.nat) ->
        'a -> (('a * 'b) list) FArray.IsabelleMapping.ArrayType -> 'b option
  val ahm_lookup :
    ('a -> 'a -> bool) ->
      (Arith.nat -> 'a -> Arith.nat) -> 'a -> ('a, 'b) hashmap -> 'b option
  val ahm_iteratei_aux :
    (('a * 'b) list) FArray.IsabelleMapping.ArrayType ->
      ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val ahm_rehash_auxa :
    (Arith.nat -> 'a -> Arith.nat) ->
      Arith.nat ->
        'a * 'b ->
          (('a * 'b) list) FArray.IsabelleMapping.ArrayType ->
            (('a * 'b) list) FArray.IsabelleMapping.ArrayType
  val ahm_rehash_aux :
    (Arith.nat -> 'a -> Arith.nat) ->
      (('a * 'b) list) FArray.IsabelleMapping.ArrayType ->
        Arith.nat -> (('a * 'b) list) FArray.IsabelleMapping.ArrayType
  val ahm_rehash :
    (Arith.nat -> 'a -> Arith.nat) ->
      ('a, 'b) hashmap -> Arith.nat -> ('a, 'b) hashmap
  val ahm_update_aux :
    ('a -> 'a -> bool) ->
      (Arith.nat -> 'a -> Arith.nat) ->
        ('a, 'b) hashmap -> 'a -> 'b -> ('a, 'b) hashmap
  val ahm_update :
    ('a -> 'a -> bool) ->
      (Arith.nat -> 'a -> Arith.nat) ->
        'a -> 'b -> ('a, 'b) hashmap -> ('a, 'b) hashmap
end = struct

datatype ('a, 'b) hashmap =
  HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * Arith.nat;

fun hm_grow (HashMap (a, n)) =
  Arith.plus_nata
    (Arith.times_nata (Arith.nat_of_integer (2 : IntInf.int))
      (Diff_Array.array_length a))
    (Arith.nat_of_integer (3 : IntInf.int));

fun new_hashmap_with size =
  HashMap (Diff_Array.new_array [] size, Arith.zero_nata);

fun ahm_empty def_size = new_hashmap_with def_size;

val load_factor : Arith.nat = Arith.nat_of_integer (75 : IntInf.int);

fun ahm_filled (HashMap (a, n)) =
  Arith.less_eq_nat (Arith.times_nata (Diff_Array.array_length a) load_factor)
    (Arith.times_nata n (Arith.nat_of_integer (100 : IntInf.int)));

fun ahm_lookup_aux eq bhc k a =
  Impl_List_Map.list_map_lookup eq k
    (Diff_Array.array_get a (bhc (Diff_Array.array_length a) k));

fun ahm_lookup eq bhc k (HashMap (a, uu)) = ahm_lookup_aux eq bhc k a;

fun ahm_iteratei_aux a c f sigma =
  Idx_Iterator.idx_iteratei Diff_Array.array_get Diff_Array.array_length a c
    (fn x => Foldi.foldli x c f) sigma;

fun ahm_rehash_auxa bhc n kv a =
  let
    val h = bhc n (Product_Type.fst kv);
  in
    Diff_Array.array_set a h (kv :: Diff_Array.array_get a h)
  end;

fun ahm_rehash_aux bhc a sz =
  ahm_iteratei_aux a (fn _ => true) (ahm_rehash_auxa bhc sz)
    (Diff_Array.new_array [] sz);

fun ahm_rehash bhc (HashMap (a, n)) sz = HashMap (ahm_rehash_aux bhc a sz, n);

fun ahm_update_aux eq bhc (HashMap (a, n)) k v =
  let
    val h = bhc (Diff_Array.array_length a) k;
    val m = Diff_Array.array_get a h;
    val insert = Option.is_none (Impl_List_Map.list_map_lookup eq k m);
  in
    HashMap
      (Diff_Array.array_set a h (Impl_List_Map.list_map_update eq k v m),
        (if insert then Arith.plus_nata n Arith.one_nata else n))
  end;

fun ahm_update eq bhc k v hm =
  let
    val hma = ahm_update_aux eq bhc hm k v;
  in
    (if ahm_filled hma then ahm_rehash bhc hma (hm_grow hma) else hma)
  end;

end; (*struct Impl_Array_Hash_Map*)

structure HashCode : sig
  type 'a hashable
  val hashcode : 'a hashable -> 'a -> Arith.nat
  val bounded_hashcode : 'a hashable -> Arith.nat -> 'a -> Arith.nat
  val def_hashmap_size : 'a hashable -> 'a HOL.itself -> Arith.nat
  val def_hashmap_size_nat : Arith.nat HOL.itself -> Arith.nat
  val bounded_hashcode_nat : Arith.nat -> Arith.nat -> Arith.nat
  val hashcode_nat : Arith.nat -> Arith.nat
  val hashable_nat : Arith.nat hashable
  val def_hashmap_size_prod :
    'a hashable -> 'b hashable -> ('a * 'b) HOL.itself -> Arith.nat
  val bounded_hashcode_prod :
    'a hashable -> 'b hashable -> Arith.nat -> 'a * 'b -> Arith.nat
  val hashcode_prod : 'a hashable -> 'b hashable -> 'a * 'b -> Arith.nat
  val hashable_prod : 'a hashable -> 'b hashable -> ('a * 'b) hashable
end = struct

type 'a hashable =
  {hashcode : 'a -> Arith.nat, bounded_hashcode : Arith.nat -> 'a -> Arith.nat,
    def_hashmap_size : 'a HOL.itself -> Arith.nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Arith.nat;
val bounded_hashcode = #bounded_hashcode :
  'a hashable -> Arith.nat -> 'a -> Arith.nat;
val def_hashmap_size = #def_hashmap_size :
  'a hashable -> 'a HOL.itself -> Arith.nat;

fun def_hashmap_size_nat x = (fn _ => Arith.nat_of_integer (16 : IntInf.int)) x;

fun bounded_hashcode_nat na n = Arith.mod_nat n na;

fun hashcode_nat n = n;

val hashable_nat =
  {hashcode = hashcode_nat, bounded_hashcode = bounded_hashcode_nat,
    def_hashmap_size = def_hashmap_size_nat}
  : Arith.nat hashable;

fun def_hashmap_size_prod A_ B_ =
  (fn _ =>
    Arith.plus_nata (def_hashmap_size A_ HOL.Type)
      (def_hashmap_size B_ HOL.Type));

fun bounded_hashcode_prod A_ B_ n x =
  Arith.mod_nat
    (Arith.plus_nata
      (Arith.times_nata (bounded_hashcode A_ n (Product_Type.fst x))
        (Arith.nat_of_integer (33 : IntInf.int)))
      (bounded_hashcode B_ n (Product_Type.snd x)))
    n;

fun hashcode_prod A_ B_ x =
  Arith.plus_nata
    (Arith.times_nata (hashcode A_ (Product_Type.fst x))
      (Arith.nat_of_integer (33 : IntInf.int)))
    (hashcode B_ (Product_Type.snd x));

fun hashable_prod A_ B_ =
  {hashcode = hashcode_prod A_ B_,
    bounded_hashcode = bounded_hashcode_prod A_ B_,
    def_hashmap_size = def_hashmap_size_prod A_ B_}
  : ('a * 'b) hashable;

end; (*struct HashCode*)

structure Uint32a : sig
  val uint32_of_int : Arith.int -> Word32.word
end = struct

fun uint32_of_int i = Word32.fromInt (Arith.integer_of_int i);

end; (*struct Uint32a*)

structure Stringa : sig
  datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
    Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC |
    NibbleD | NibbleE | NibbleF
  val equal_char : char HOL.equal
  val nat_of_char : char -> Arith.nat
  val equal_literal : string HOL.equal
end = struct

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

val equal_char = {equal = (fn a => fn b => ((a : char) = b))} : char HOL.equal;

fun nat_of_char x = (Arith.nat_of_integer o (IntInf.fromInt o Char.ord)) x;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string HOL.equal;

end; (*struct Stringa*)

structure Collections_Patch1 : sig
  val bs_eq : IntInf.int -> IntInf.int -> bool
  val bs_mem : Arith.nat -> IntInf.int -> bool
  val bs_empty : unit -> IntInf.int
  val bs_union : IntInf.int -> IntInf.int -> IntInf.int
  val bs_insert : Arith.nat -> IntInf.int -> IntInf.int
  val bs_subset_eq : IntInf.int -> IntInf.int -> bool
  val nat_of_uint32 : Word32.word -> Arith.nat
  val nat_of_hashcode_uint : Word32.word -> Arith.nat
  type 'a hashable_uint
  val hashcode_uint : 'a hashable_uint -> 'a -> Word32.word
  val def_hashmap_size_uint : 'a hashable_uint -> 'a HOL.itself -> Arith.nat
  val hashcode_nat : 'a hashable_uint -> 'a -> Arith.nat
  val def_hashmap_size_uint_integer : IntInf.int HOL.itself -> Arith.nat
  val def_hashmap_size_integer : IntInf.int HOL.itself -> Arith.nat
  val hashcode_uint_integer : IntInf.int -> Word32.word
  val hashable_uint_integer : IntInf.int hashable_uint
  val bounded_hashcode_nat : 'a hashable_uint -> Arith.nat -> 'a -> Arith.nat
  val bounded_hashcode_integer : Arith.nat -> IntInf.int -> Arith.nat
  val hashcode_integer : IntInf.int -> Arith.nat
  val hashable_integer : IntInf.int HashCode.hashable
  val def_hashmap_size_uint_nat : Arith.nat HOL.itself -> Arith.nat
  val hashcode_uint_nat : Arith.nat -> Word32.word
  val hashable_uint_nat : Arith.nat hashable_uint
  val def_hashmap_size_uint_bool : bool HOL.itself -> Arith.nat
  val hashcode_uint_bool : bool -> Word32.word
  val hashable_uint_bool : bool hashable_uint
  val def_hashmap_size_uint_char : char HOL.itself -> Arith.nat
  val hashcode_uint_char : char -> Word32.word
  val hashable_uint_char : char hashable_uint
  val def_hashmap_size_uint_list :
    'a hashable_uint -> ('a list) HOL.itself -> Arith.nat
  val hashcode_uint_list : 'a hashable_uint -> 'a list -> Word32.word
  val hashable_uint_list : 'a hashable_uint -> ('a list) hashable_uint
  val def_hashmap_size_uint_prod :
    'a hashable_uint -> 'b hashable_uint -> ('a * 'b) HOL.itself -> Arith.nat
  val hashcode_uint_prod :
    'a hashable_uint -> 'b hashable_uint -> 'a * 'b -> Word32.word
  val hashable_uint_prod :
    'a hashable_uint -> 'b hashable_uint -> ('a * 'b) hashable_uint
  val def_hashmap_size_uint_unit : unit HOL.itself -> Arith.nat
  val hashcode_uint_unit : unit -> Word32.word
  val hashable_uint_unit : unit hashable_uint
end = struct

fun bs_eq s1 s2 = ((s1 : IntInf.int) = s2);

fun bs_mem i s = Bit_Int.test_bit_integer s i;

fun bs_empty x = (fn _ => 0) x;

fun bs_union s1 s2 = IntInf.orb (s1, s2);

fun bs_insert i s = Bit_Int.set_bit_integer s i true;

fun bs_subset_eq s1 s2 =
  (((IntInf.andb (s1, IntInf.notb s2)) : IntInf.int) = 0);

fun nat_of_uint32 x = Arith.nat_of_integer (Word32.toInt x : IntInf.int);

fun nat_of_hashcode_uint x = nat_of_uint32 x;

type 'a hashable_uint =
  {hashcode_uint : 'a -> Word32.word,
    def_hashmap_size_uint : 'a HOL.itself -> Arith.nat};
val hashcode_uint = #hashcode_uint : 'a hashable_uint -> 'a -> Word32.word;
val def_hashmap_size_uint = #def_hashmap_size_uint :
  'a hashable_uint -> 'a HOL.itself -> Arith.nat;

fun hashcode_nat A_ = nat_of_hashcode_uint o hashcode_uint A_;

fun def_hashmap_size_uint_integer x =
  (fn _ => Arith.nat_of_integer (16 : IntInf.int)) x;

fun def_hashmap_size_integer x = def_hashmap_size_uint_integer x;

fun hashcode_uint_integer i = Word32.fromInt i;

val hashable_uint_integer =
  {hashcode_uint = hashcode_uint_integer,
    def_hashmap_size_uint = def_hashmap_size_uint_integer}
  : IntInf.int hashable_uint;

fun bounded_hashcode_nat A_ n x = Arith.mod_nat (hashcode_nat A_ x) n;

fun bounded_hashcode_integer x = bounded_hashcode_nat hashable_uint_integer x;

fun hashcode_integer x = hashcode_nat hashable_uint_integer x;

val hashable_integer =
  {hashcode = hashcode_integer, bounded_hashcode = bounded_hashcode_integer,
    def_hashmap_size = def_hashmap_size_integer}
  : IntInf.int HashCode.hashable;

fun def_hashmap_size_uint_nat x =
  (fn _ => Arith.nat_of_integer (16 : IntInf.int)) x;

fun hashcode_uint_nat n = Uint32a.uint32_of_int (Arith.int_of_nat n);

val hashable_uint_nat =
  {hashcode_uint = hashcode_uint_nat,
    def_hashmap_size_uint = def_hashmap_size_uint_nat}
  : Arith.nat hashable_uint;

fun def_hashmap_size_uint_bool x =
  (fn _ => Arith.nat_of_integer (2 : IntInf.int)) x;

fun hashcode_uint_bool b =
  (if b then (Word32.fromInt 1) else (Word32.fromInt 0));

val hashable_uint_bool =
  {hashcode_uint = hashcode_uint_bool,
    def_hashmap_size_uint = def_hashmap_size_uint_bool}
  : bool hashable_uint;

fun def_hashmap_size_uint_char x =
  (fn _ => Arith.nat_of_integer (32 : IntInf.int)) x;

fun hashcode_uint_char c =
  Uint32a.uint32_of_int (Arith.int_of_nat (Stringa.nat_of_char c));

val hashable_uint_char =
  {hashcode_uint = hashcode_uint_char,
    def_hashmap_size_uint = def_hashmap_size_uint_char}
  : char hashable_uint;

fun def_hashmap_size_uint_list A_ =
  (fn _ =>
    Arith.times_nata (Arith.nat_of_integer (2 : IntInf.int))
      (def_hashmap_size_uint A_ HOL.Type));

fun hashcode_uint_list A_ =
  List.foldl
    (fn h => fn x =>
      Word32.+ (Word32.* (h, Word32.fromInt
                               (33 : IntInf.int)), hashcode_uint A_ x))
    (Word32.fromInt (5381 : IntInf.int));

fun hashable_uint_list A_ =
  {hashcode_uint = hashcode_uint_list A_,
    def_hashmap_size_uint = def_hashmap_size_uint_list A_}
  : ('a list) hashable_uint;

fun def_hashmap_size_uint_prod A_ B_ =
  (fn _ =>
    Arith.plus_nata (def_hashmap_size_uint A_ HOL.Type)
      (def_hashmap_size_uint B_ HOL.Type));

fun hashcode_uint_prod A_ B_ x =
  Word32.+ (Word32.* (hashcode_uint A_
                        (Product_Type.fst
                          x), Word32.fromInt
                                (33 : IntInf.int)), hashcode_uint B_
              (Product_Type.snd x));

fun hashable_uint_prod A_ B_ =
  {hashcode_uint = hashcode_uint_prod A_ B_,
    def_hashmap_size_uint = def_hashmap_size_uint_prod A_ B_}
  : ('a * 'b) hashable_uint;

fun def_hashmap_size_uint_unit x =
  (fn _ => Arith.nat_of_integer (2 : IntInf.int)) x;

fun hashcode_uint_unit u = (Word32.fromInt 0);

val hashable_uint_unit =
  {hashcode_uint = hashcode_uint_unit,
    def_hashmap_size_uint = def_hashmap_size_uint_unit}
  : unit hashable_uint;

end; (*struct Collections_Patch1*)

structure Digraph_Impl : sig
  datatype ('a, 'b, 'c, 'd) gen_frg_impl_ext =
    Gen_frg_impl_ext of 'a * 'b * 'c * 'd
  val frgi_E : ('a, 'b, 'c, 'd) gen_frg_impl_ext -> 'b
  val frgi_V : ('a, 'b, 'c, 'd) gen_frg_impl_ext -> 'a
  val frgi_V0 : ('a, 'b, 'c, 'd) gen_frg_impl_ext -> 'c
  val graph_restrict_left_impl :
    ('a -> 'b -> bool) -> 'b -> ('a -> 'a list) -> 'a -> 'a list
  val graph_restrict_right_impl :
    ('a -> 'b -> bool) -> 'b -> ('a -> 'a list) -> 'a -> 'a list
end = struct

datatype ('a, 'b, 'c, 'd) gen_frg_impl_ext =
  Gen_frg_impl_ext of 'a * 'b * 'c * 'd;

fun frgi_E (Gen_frg_impl_ext (frgi_V, frgi_E, frgi_V0, more)) = frgi_E;

fun frgi_V (Gen_frg_impl_ext (frgi_V, frgi_E, frgi_V0, more)) = frgi_V;

fun frgi_V0 (Gen_frg_impl_ext (frgi_V, frgi_E, frgi_V0, more)) = frgi_V0;

fun graph_restrict_left_impl meml =
  (fn x => fn xa => fn xb => (if meml xb x then xa xb else []));

fun graph_restrict_right_impl memr =
  (fn x => fn xa => fn xb => List.filter (fn xc => memr xc x) (xa xb));

end; (*struct Digraph_Impl*)

structure Automata_Impl : sig
  datatype ('a, 'b) gen_bg_impl_ext = Gen_bg_impl_ext of 'a * 'b
  val bgi_F :
    ('a, 'b, 'c, ('d, 'e) gen_bg_impl_ext) Digraph_Impl.gen_frg_impl_ext -> 'd
  datatype ('a, 'b) gen_sa_impl_ext = Gen_sa_impl_ext of 'a * 'b
  val sai_L :
    ('a, 'b, 'c, ('d, 'e) gen_sa_impl_ext) Digraph_Impl.gen_frg_impl_ext -> 'd
  datatype ('a, 'b) gen_gbg_impl_ext = Gen_gbg_impl_ext of 'a * 'b
  datatype ('a, 'b) gen_gba_impl_ext = Gen_gba_impl_ext of 'a * 'b
  val gbai_L :
    ('a, 'b, 'c, ('d, ('e, 'f) gen_gba_impl_ext) gen_gbg_impl_ext)
      Digraph_Impl.gen_frg_impl_ext ->
      'e
  val gbgi_F :
    ('a, 'b, 'c, ('d, 'e) gen_gbg_impl_ext) Digraph_Impl.gen_frg_impl_ext -> 'd
  datatype ('a, 'b) gen_igbg_impl_ext = Gen_igbg_impl_ext of Arith.nat * 'a * 'b
  datatype ('a, 'b) gen_igba_impl_ext = Gen_igba_impl_ext of 'a * 'b
  val igbai_L :
    ('a, 'b, 'c, ('d, ('e, 'f) gen_igba_impl_ext) gen_igbg_impl_ext)
      Digraph_Impl.gen_frg_impl_ext ->
      'e
  val igbgi_acc :
    ('a, 'b, 'c, ('d, 'e) gen_igbg_impl_ext) Digraph_Impl.gen_frg_impl_ext -> 'd
  val igbgi_num_acc :
    ('a, 'b, 'c, ('d, 'e) gen_igbg_impl_ext) Digraph_Impl.gen_frg_impl_ext ->
      Arith.nat
  val gbg_to_idx_ext_code :
    Arith.nat ->
      ('a -> 'a -> bool) ->
        (Arith.nat -> 'a -> Arith.nat) ->
          ((('a list), ('a -> 'a list), ('a list),
             ((('a list) list), 'b) gen_gbg_impl_ext)
             Digraph_Impl.gen_frg_impl_ext ->
            'c) ->
            (('a list), ('a -> 'a list), ('a list),
              ((('a list) list), 'b) gen_gbg_impl_ext)
              Digraph_Impl.gen_frg_impl_ext ->
              (('a list), ('a -> 'a list), ('a list),
                (('a -> IntInf.int), 'c) gen_igbg_impl_ext)
                Digraph_Impl.gen_frg_impl_ext
  val gba_to_idx_ext_code :
    Arith.nat ->
      ('a -> 'a -> bool) ->
        (Arith.nat -> 'a -> Arith.nat) ->
          ((('a list), ('a -> 'a list), ('a list),
             ((('a list) list), (('a -> 'b -> bool), 'c) gen_gba_impl_ext)
               gen_gbg_impl_ext)
             Digraph_Impl.gen_frg_impl_ext ->
            'd) ->
            (('a list), ('a -> 'a list), ('a list),
              ((('a list) list), (('a -> 'b -> bool), 'c) gen_gba_impl_ext)
                gen_gbg_impl_ext)
              Digraph_Impl.gen_frg_impl_ext ->
              (('a list), ('a -> 'a list), ('a list),
                (('a -> IntInf.int), (('a -> 'b -> bool), 'd) gen_igba_impl_ext)
                  gen_igbg_impl_ext)
                Digraph_Impl.gen_frg_impl_ext
  val degeneralize_ext_impl :
    (('a -> bool), ('a -> 'a list), ('a list),
      (('a -> IntInf.int), 'b) gen_igbg_impl_ext)
      Digraph_Impl.gen_frg_impl_ext ->
      ((('a -> bool), ('a -> 'a list), ('a list),
         (('a -> IntInf.int), 'b) gen_igbg_impl_ext)
         Digraph_Impl.gen_frg_impl_ext ->
        'c) ->
        (('a * Arith.nat -> bool), ('a * Arith.nat -> ('a * Arith.nat) list),
          (('a * Arith.nat) list),
          (('a * Arith.nat -> bool), 'c) gen_bg_impl_ext)
          Digraph_Impl.gen_frg_impl_ext
end = struct

datatype ('a, 'b) gen_bg_impl_ext = Gen_bg_impl_ext of 'a * 'b;

fun bgi_F
  (Digraph_Impl.Gen_frg_impl_ext
    (frgi_V, frgi_E, frgi_V0, Gen_bg_impl_ext (bgi_F, more)))
  = bgi_F;

datatype ('a, 'b) gen_sa_impl_ext = Gen_sa_impl_ext of 'a * 'b;

fun sai_L
  (Digraph_Impl.Gen_frg_impl_ext
    (frgi_V, frgi_E, frgi_V0, Gen_sa_impl_ext (sai_L, more)))
  = sai_L;

datatype ('a, 'b) gen_gbg_impl_ext = Gen_gbg_impl_ext of 'a * 'b;

datatype ('a, 'b) gen_gba_impl_ext = Gen_gba_impl_ext of 'a * 'b;

fun gbai_L
  (Digraph_Impl.Gen_frg_impl_ext
    (frgi_V, frgi_E, frgi_V0,
      Gen_gbg_impl_ext (gbgi_F, Gen_gba_impl_ext (gbai_L, more))))
  = gbai_L;

fun gbgi_F
  (Digraph_Impl.Gen_frg_impl_ext
    (frgi_V, frgi_E, frgi_V0, Gen_gbg_impl_ext (gbgi_F, more)))
  = gbgi_F;

datatype ('a, 'b) gen_igbg_impl_ext = Gen_igbg_impl_ext of Arith.nat * 'a * 'b;

datatype ('a, 'b) gen_igba_impl_ext = Gen_igba_impl_ext of 'a * 'b;

fun igbai_L
  (Digraph_Impl.Gen_frg_impl_ext
    (frgi_V, frgi_E, frgi_V0,
      Gen_igbg_impl_ext
        (igbgi_num_acc, igbgi_acc, Gen_igba_impl_ext (igbai_L, more))))
  = igbai_L;

fun igbgi_acc
  (Digraph_Impl.Gen_frg_impl_ext
    (frgi_V, frgi_E, frgi_V0,
      Gen_igbg_impl_ext (igbgi_num_acc, igbgi_acc, more)))
  = igbgi_acc;

fun igbgi_num_acc
  (Digraph_Impl.Gen_frg_impl_ext
    (frgi_V, frgi_E, frgi_V0,
      Gen_igbg_impl_ext (igbgi_num_acc, igbgi_acc, more)))
  = igbgi_num_acc;

fun gbg_to_idx_ext_code def_size eq bhc ecnv g =
  let
    val (a, b) =
      let
        val x = Fun.id (gbgi_F g);
        val xa = List.size_list x;
        val a =
          let
            val xb = Impl_Array_Hash_Map.ahm_empty def_size;
            val (_, b) =
              Foldi.foldli x (fn _ => true)
                (fn xc => fn (a, b) =>
                  let
                    val ba =
                      Foldi.foldli (Fun.id xc) (fn _ => true)
                        (fn xd => fn sigma =>
                          Impl_Array_Hash_Map.ahm_update eq bhc xd
                            (Collections_Patch1.bs_insert a
                              (Misc.the_default (Collections_Patch1.bs_empty ())
                                (Impl_Array_Hash_Map.ahm_lookup eq bhc xd
                                  sigma)))
                            sigma)
                        b;
                  in
                    (Arith.suc a, ba)
                  end)
                (Arith.zero_nata, xb);
          in
            (fn xg =>
              Misc.the_default (Collections_Patch1.bs_empty ())
                (Impl_Array_Hash_Map.ahm_lookup eq bhc xg b))
          end;
      in
        (xa, a)
      end;
  in
    Digraph_Impl.Gen_frg_impl_ext
      (Digraph_Impl.frgi_V g, Digraph_Impl.frgi_E g, Digraph_Impl.frgi_V0 g,
        Gen_igbg_impl_ext (a, b, ecnv g))
  end;

fun gba_to_idx_ext_code eq bhc def_size ecnv g =
  gbg_to_idx_ext_code eq bhc def_size
    (fn xa => Gen_igba_impl_ext (gbai_L xa, ecnv xa)) g;

fun degeneralize_ext_impl gi x =
  (if Arith.equal_nata (igbgi_num_acc gi) Arith.zero_nata
    then Digraph_Impl.Gen_frg_impl_ext
           ((fn (xa, xb) =>
              Arith.equal_nata xb Arith.zero_nata andalso
                Digraph_Impl.frgi_V gi xa),
             (fn (xa, xb) =>
               (if Arith.equal_nata xb Arith.zero_nata
                 then List.map (fn xc => (xc, Arith.zero_nata))
                        (Digraph_Impl.frgi_E gi xa)
                 else [])),
             List.map (fn xa => (xa, Arith.zero_nata))
               (Digraph_Impl.frgi_V0 gi),
             Gen_bg_impl_ext
               ((fn (xa, xb) =>
                  Arith.equal_nata xb Arith.zero_nata andalso
                    Digraph_Impl.frgi_V gi xa),
                 x gi))
    else Digraph_Impl.Gen_frg_impl_ext
           ((fn (xa, xb) =>
              Arith.less_nat xb (igbgi_num_acc gi) andalso
                Digraph_Impl.frgi_V gi xa),
             (fn (xa, xb) =>
               (if Arith.less_nat xb (igbgi_num_acc gi)
                 then let
                        val xc =
                          (if Collections_Patch1.bs_mem xb (igbgi_acc gi xa)
                            then Arith.mod_nat
                                   (Arith.plus_nata xb Arith.one_nata)
                                   (igbgi_num_acc gi)
                            else xb);
                      in
                        List.map (fn xd => (xd, xc)) (Digraph_Impl.frgi_E gi xa)
                      end
                 else [])),
             List.map (fn xa => (xa, Arith.zero_nata))
               (Digraph_Impl.frgi_V0 gi),
             Gen_bg_impl_ext
               ((fn (xa, xb) =>
                  Arith.equal_nata xb Arith.zero_nata andalso
                    Collections_Patch1.bs_mem Arith.zero_nata
                      (igbgi_acc gi xa)),
                 x gi)));

end; (*struct Automata_Impl*)

structure ArrayHashMap_Impl : sig
  datatype ('a, 'b) hashmap =
    HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * Arith.nat
  val hm_grow : 'a HashCode.hashable -> ('a, 'b) hashmap -> Arith.nat
  val ahm_alpha_aux :
    'a HOL.equal * 'a HashCode.hashable ->
      (('a * 'b) list) FArray.IsabelleMapping.ArrayType -> 'a -> 'b option
  val ahm_alpha :
    'a HOL.equal * 'a HashCode.hashable -> ('a, 'b) hashmap -> 'a -> 'b option
  val new_hashmap_with : 'a HashCode.hashable -> Arith.nat -> ('a, 'b) hashmap
  val ahm_empty : 'a HashCode.hashable -> unit -> ('a, 'b) hashmap
  val ahm_delete :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, 'b) hashmap -> ('a, 'b) hashmap
  val load_factor : Arith.nat
  val ahm_filled : 'a HashCode.hashable -> ('a, 'b) hashmap -> bool
  val ahm_lookup :
    'a HOL.equal * 'a HashCode.hashable -> 'a -> ('a, 'b) hashmap -> 'b option
  val idx_iteratei_aux_array_get :
    Arith.nat ->
      Arith.nat ->
        'a FArray.IsabelleMapping.ArrayType ->
          ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val idx_iteratei_array_length_array_get :
    'a FArray.IsabelleMapping.ArrayType ->
      ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val ahm_iteratei_aux :
    'a HashCode.hashable ->
      (('a * 'b) list) FArray.IsabelleMapping.ArrayType ->
        ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val ahm_rehash_auxa :
    'a HashCode.hashable ->
      Arith.nat ->
        'a * 'b ->
          (('a * 'b) list) FArray.IsabelleMapping.ArrayType ->
            (('a * 'b) list) FArray.IsabelleMapping.ArrayType
  val ahm_rehash_aux :
    'a HashCode.hashable ->
      (('a * 'b) list) FArray.IsabelleMapping.ArrayType ->
        Arith.nat -> (('a * 'b) list) FArray.IsabelleMapping.ArrayType
  val ahm_rehash :
    'a HashCode.hashable -> ('a, 'b) hashmap -> Arith.nat -> ('a, 'b) hashmap
  val ahm_update_aux :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, 'b) hashmap -> 'a -> 'b -> ('a, 'b) hashmap
  val ahm_update :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> 'b -> ('a, 'b) hashmap -> ('a, 'b) hashmap
end = struct

datatype ('a, 'b) hashmap =
  HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * Arith.nat;

fun hm_grow A_ (HashMap (a, n)) =
  Arith.plus_nata
    (Arith.times_nata (Arith.nat_of_integer (2 : IntInf.int))
      (Diff_Array.array_length a))
    (Arith.nat_of_integer (3 : IntInf.int));

fun ahm_alpha_aux (A1_, A2_) a k =
  Map.map_of A1_
    (Diff_Array.array_get a
      (HashCode.bounded_hashcode A2_ (Diff_Array.array_length a) k))
    k;

fun ahm_alpha (A1_, A2_) (HashMap (a, uu)) = ahm_alpha_aux (A1_, A2_) a;

fun new_hashmap_with A_ size =
  HashMap (Diff_Array.new_array [] size, Arith.zero_nata);

fun ahm_empty A_ =
  (fn _ => new_hashmap_with A_ (HashCode.def_hashmap_size A_ HOL.Type));

fun ahm_delete (A1_, A2_) k (HashMap (a, n)) =
  let
    val h = HashCode.bounded_hashcode A2_ (Diff_Array.array_length a) k;
    val m = Diff_Array.array_get a h;
    val deleted = not (Option.is_none (Map.map_of A1_ m k));
  in
    HashMap
      (Diff_Array.array_set a h (AList.delete A1_ k m),
        (if deleted then Arith.minus_nat n Arith.one_nata else n))
  end;

val load_factor : Arith.nat = Arith.nat_of_integer (75 : IntInf.int);

fun ahm_filled A_ (HashMap (a, n)) =
  Arith.less_eq_nat (Arith.times_nata (Diff_Array.array_length a) load_factor)
    (Arith.times_nata n (Arith.nat_of_integer (100 : IntInf.int)));

fun ahm_lookup (A1_, A2_) k hm = ahm_alpha (A1_, A2_) hm k;

fun idx_iteratei_aux_array_get sz i l c f sigma =
  (if Arith.equal_nata i Arith.zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux_array_get sz (Arith.minus_nat i Arith.one_nata) l c f
           (f (Diff_Array.array_get l (Arith.minus_nat sz i)) sigma));

fun idx_iteratei_array_length_array_get l c f sigma =
  idx_iteratei_aux_array_get (Diff_Array.array_length l)
    (Diff_Array.array_length l) l c f sigma;

fun ahm_iteratei_aux A_ a c f sigma =
  idx_iteratei_array_length_array_get a c (fn x => Foldi.foldli x c f) sigma;

fun ahm_rehash_auxa A_ n kv a =
  let
    val h = HashCode.bounded_hashcode A_ n (Product_Type.fst kv);
  in
    Diff_Array.array_set a h (kv :: Diff_Array.array_get a h)
  end;

fun ahm_rehash_aux A_ a sz =
  ahm_iteratei_aux A_ a (fn _ => true) (ahm_rehash_auxa A_ sz)
    (Diff_Array.new_array [] sz);

fun ahm_rehash A_ (HashMap (a, n)) sz = HashMap (ahm_rehash_aux A_ a sz, n);

fun ahm_update_aux (A1_, A2_) (HashMap (a, n)) k v =
  let
    val h = HashCode.bounded_hashcode A2_ (Diff_Array.array_length a) k;
    val m = Diff_Array.array_get a h;
    val insert = Option.is_none (Map.map_of A1_ m k);
  in
    HashMap
      (Diff_Array.array_set a h (AList.update A1_ k v m),
        (if insert then Arith.plus_nata n Arith.one_nata else n))
  end;

fun ahm_update (A1_, A2_) k v hm =
  let
    val hma = ahm_update_aux (A1_, A2_) hm k v;
  in
    (if ahm_filled A2_ hma then ahm_rehash A2_ hma (hm_grow A2_ hma) else hma)
  end;

end; (*struct ArrayHashMap_Impl*)

structure ArrayHashMap : sig
  datatype ('a, 'b) hashmap = HashMap of ('a, 'b) ArrayHashMap_Impl.hashmap
  val impl_of :
    'a HashCode.hashable ->
      ('a, 'b) hashmap -> ('a, 'b) ArrayHashMap_Impl.hashmap
  val ahm_empty_const : 'a HashCode.hashable -> ('a, 'b) hashmap
  val ahm_empty : 'a HashCode.hashable -> unit -> ('a, 'b) hashmap
  val ahm_delete :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, 'b) hashmap -> ('a, 'b) hashmap
  val ahm_lookup :
    'a HOL.equal * 'a HashCode.hashable -> 'a -> ('a, 'b) hashmap -> 'b option
  val ahm_update :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> 'b -> ('a, 'b) hashmap -> ('a, 'b) hashmap
end = struct

datatype ('a, 'b) hashmap = HashMap of ('a, 'b) ArrayHashMap_Impl.hashmap;

fun impl_of A_ (HashMap x) = x;

fun ahm_empty_const A_ = HashMap (ArrayHashMap_Impl.ahm_empty A_ ());

fun ahm_empty A_ = (fn _ => ahm_empty_const A_);

fun ahm_delete (A1_, A2_) k hm =
  HashMap (ArrayHashMap_Impl.ahm_delete (A1_, A2_) k (impl_of A2_ hm));

fun ahm_lookup (A1_, A2_) k hm =
  ArrayHashMap_Impl.ahm_lookup (A1_, A2_) k (impl_of A2_ hm);

fun ahm_update (A1_, A2_) k v hm =
  HashMap (ArrayHashMap_Impl.ahm_update (A1_, A2_) k v (impl_of A2_ hm));

end; (*struct ArrayHashMap*)

structure ArrayHashSet : sig
  val ins_ahm_basic_ops :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
  val memb_ahm_basic_ops :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, unit) ArrayHashMap.hashmap -> bool
  val empty_ahm_basic_ops :
    'a HashCode.hashable -> unit -> ('a, unit) ArrayHashMap.hashmap
  val delete_ahm_basic_ops :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
end = struct

fun ins_ahm_basic_ops (A1_, A2_) x s =
  ArrayHashMap.ahm_update (A1_, A2_) x () s;

fun memb_ahm_basic_ops (A1_, A2_) x s =
  not (Option.is_none (ArrayHashMap.ahm_lookup (A1_, A2_) x s));

fun empty_ahm_basic_ops A_ = ArrayHashMap.ahm_empty A_;

fun delete_ahm_basic_ops (A1_, A2_) x s =
  ArrayHashMap.ahm_delete (A1_, A2_) x s;

end; (*struct ArrayHashSet*)

structure NDFS_SI : sig
  datatype 'a blue_witness = NO_CYC | Reach of 'a * 'a list |
    Circ of 'a list * 'a list
  val extract_res : 'a blue_witness -> ('a list * 'a list) option
  val prep_wit_red : 'a -> ('a list * 'a) option -> ('a list * 'a) option
  val init_wit_blue :
    'a HOL.equal -> 'a -> ('a list * 'a) option -> 'a blue_witness
  val prep_wit_blue : 'a HOL.equal -> 'a -> 'a blue_witness -> 'a blue_witness
  val red_init_witness : 'a -> 'a -> ('a list * 'a) option
  val code_red_dfs_ahs_0 :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a -> 'a list) ->
        ('a, unit) ArrayHashMap.hashmap ->
          ('a, unit) ArrayHashMap.hashmap * 'a ->
            (('a, unit) ArrayHashMap.hashmap * ('a list * 'a) option)
              Refine_Det.dres
  val code_red_dfs_ahs :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a -> 'a list) ->
        ('a, unit) ArrayHashMap.hashmap ->
          ('a, unit) ArrayHashMap.hashmap ->
            'a -> ('a, unit) ArrayHashMap.hashmap * ('a list * 'a) option
  val init_wit_blue_early : 'a HOL.equal -> 'a -> 'a -> 'a blue_witness
  val equal_blue_witness :
    'a HOL.equal -> 'a blue_witness -> 'a blue_witness -> bool
  val code_blue_dfs_ahs_0 :
    'a HOL.equal * 'a HashCode.hashable ->
      (('a -> bool), ('a -> 'a list), ('a list),
        (('a -> bool), 'b) Automata_Impl.gen_bg_impl_ext)
        Digraph_Impl.gen_frg_impl_ext ->
        ('a, unit) ArrayHashMap.hashmap *
          (('a, unit) ArrayHashMap.hashmap *
            (('a, unit) ArrayHashMap.hashmap * 'a)) ->
          (('a, unit) ArrayHashMap.hashmap *
            (('a, unit) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap * 'a blue_witness)))
            Refine_Det.dres
  val code_blue_dfs_ahs :
    'a HOL.equal * 'a HashCode.hashable ->
      (('a -> bool), ('a -> 'a list), ('a list),
        (('a -> bool), 'b) Automata_Impl.gen_bg_impl_ext)
        Digraph_Impl.gen_frg_impl_ext ->
        ('a list * 'a list) option
end = struct

datatype 'a blue_witness = NO_CYC | Reach of 'a * 'a list |
  Circ of 'a list * 'a list;

fun extract_res cyc =
  (case cyc of NO_CYC => NONE | Reach (_, _) => NONE
    | Circ (pr, pl) => SOME (pr, pl));

fun prep_wit_red v NONE = NONE
  | prep_wit_red v (SOME (p, u)) = SOME (v :: p, u);

fun init_wit_blue A_ u0 NONE = NO_CYC
  | init_wit_blue A_ u0 (SOME (p, u)) =
    (if HOL.eq A_ u u0 then Circ ([], p) else Reach (u, p));

fun prep_wit_blue A_ u0 NO_CYC = NO_CYC
  | prep_wit_blue A_ u0 (Reach (u, p)) =
    (if HOL.eq A_ u0 u then Circ ([], u0 :: p) else Reach (u, u0 :: p))
  | prep_wit_blue A_ u0 (Circ (pr, pl)) = Circ (u0 :: pr, pl);

fun red_init_witness u v = SOME ([u], v);

fun code_red_dfs_ahs_0 (A1_, A2_) e onstack x =
  let
    val (a, b) = x;
    val xa = ArrayHashSet.ins_ahm_basic_ops (A1_, A2_) b a;
  in
    Refine_Det.dbind (Refine_Det.DRETURN (NDFS_SI_Statistics.vis_red ()))
      (fn _ =>
        Refine_Det.dbind
          (Refine_Det.dbind (Refine_Det.DRETURN (Fun.id (e b)))
            (fn xs =>
              Foldi.foldli xs
                (fn aa =>
                  (case aa of Refine_Det.DSUCCEEDi => false
                    | Refine_Det.DFAILi => false
                    | Refine_Det.DRETURN ab => Autoref_Bindings_HOL.is_None ab))
                (fn xb => fn s =>
                  Refine_Det.dbind s
                    (fn _ =>
                      (if ArrayHashSet.memb_ahm_basic_ops (A1_, A2_) xb onstack
                        then Refine_Det.DRETURN (red_init_witness b xb)
                        else Refine_Det.DRETURN NONE)))
                (Refine_Det.DRETURN NONE)))
          (fn xc =>
            (case xc
              of NONE =>
                Refine_Det.dbind (Refine_Det.DRETURN (Fun.id (e b)))
                  (fn xs =>
                    Foldi.foldli xs
                      (fn aa =>
                        (case aa of Refine_Det.DSUCCEEDi => false
                          | Refine_Det.DFAILi => false
                          | Refine_Det.DRETURN (_, ab) =>
                            Autoref_Bindings_HOL.is_None ab))
                      (fn xb => fn s =>
                        Refine_Det.dbind s
                          (fn (aa, _) =>
                            (if not (ArrayHashSet.memb_ahm_basic_ops (A1_, A2_)
                                      xb aa)
                              then Refine_Det.dbind
                                     (code_red_dfs_ahs_0 (A1_, A2_) e onstack
                                       (aa, xb))
                                     (fn (ab, bb) =>
                                       Refine_Det.DRETURN
 (ab, prep_wit_red b bb))
                              else Refine_Det.DRETURN (aa, NONE))))
                      (Refine_Det.DRETURN (xa, NONE)))
              | SOME _ => Refine_Det.DRETURN (xa, xc))))
  end;

fun code_red_dfs_ahs (A1_, A2_) e onstack v u =
  Refine_Transfer.the_res (code_red_dfs_ahs_0 (A1_, A2_) e onstack (v, u));

fun init_wit_blue_early A_ s t =
  (if HOL.eq A_ s t then Circ ([], [s]) else Reach (t, [s]));

fun equal_blue_witness A_ (Circ (list1, list2)) (Reach (v, lista)) = false
  | equal_blue_witness A_ (Reach (v, lista)) (Circ (list1, list2)) = false
  | equal_blue_witness A_ (Circ (list1, list2)) NO_CYC = false
  | equal_blue_witness A_ NO_CYC (Circ (list1, list2)) = false
  | equal_blue_witness A_ (Reach (v, lista)) NO_CYC = false
  | equal_blue_witness A_ NO_CYC (Reach (v, lista)) = false
  | equal_blue_witness A_ (Circ (list1a, list2a)) (Circ (list1, list2)) =
    List.equal_lista A_ list1a list1 andalso List.equal_lista A_ list2a list2
  | equal_blue_witness A_ (Reach (va, listaa)) (Reach (v, lista)) =
    HOL.eq A_ va v andalso List.equal_lista A_ listaa lista
  | equal_blue_witness A_ NO_CYC NO_CYC = true;

fun code_blue_dfs_ahs_0 (A1_, A2_) g x =
  let
    val (ab, (ac, (ad, bd))) = x;
    val xc = ArrayHashSet.ins_ahm_basic_ops (A1_, A2_) bd ab;
    val xd = ArrayHashSet.ins_ahm_basic_ops (A1_, A2_) bd ad;
    val xe = Automata_Impl.bgi_F g bd;
  in
    Refine_Det.dbind (Refine_Det.DRETURN (NDFS_SI_Statistics.vis_blue ()))
      (fn _ =>
        Refine_Det.dbind
          (Refine_Det.dbind
            (Refine_Det.DRETURN (Fun.id (Digraph_Impl.frgi_E g bd)))
            (fn xs =>
              Foldi.foldli xs
                (fn a =>
                  (case a of Refine_Det.DSUCCEEDi => false
                    | Refine_Det.DFAILi => false
                    | Refine_Det.DRETURN (_, (_, (_, xr))) =>
                      equal_blue_witness A1_ xr NO_CYC))
                (fn xa => fn s =>
                  Refine_Det.dbind s
                    (fn (ae, (af, (ag, bg))) =>
                      (if ArrayHashSet.memb_ahm_basic_ops (A1_, A2_) xa
                            ag andalso
                            (xe orelse Automata_Impl.bgi_F g xa)
                        then Refine_Det.DRETURN
                               (ae, (af, (ag, init_wit_blue_early A1_ bd xa)))
                        else (if not (ArrayHashSet.memb_ahm_basic_ops (A1_, A2_)
                                       xa ae)
                               then Refine_Det.dbind
                                      (code_blue_dfs_ahs_0 (A1_, A2_) g
(ae, (af, (ag, xa))))
                                      (fn (ah, (ai, (aj, bj))) =>
Refine_Det.DRETURN (ah, (ai, (aj, prep_wit_blue A1_ bd bj))))
                               else Refine_Det.dbind
                                      (Refine_Det.DRETURN
(NDFS_SI_Statistics.match_blue ()))
                                      (fn _ =>
Refine_Det.DRETURN (ae, (af, (ag, bg))))))))
                (Refine_Det.DRETURN (xc, (ac, (xd, NO_CYC))))))
          (fn (ae, (af, (ag, bg))) =>
            Refine_Det.dbind
              (if equal_blue_witness A1_ bg NO_CYC andalso xe
                then Refine_Det.dbind
                       (Refine_Det.DRETURN
                         (code_red_dfs_ahs (A1_, A2_) (Digraph_Impl.frgi_E g) ag
                           af bd))
                       (fn (ah, bh) =>
                         Refine_Det.DRETURN (ah, init_wit_blue A1_ bd bh))
                else Refine_Det.DRETURN (af, bg))
              (fn (ah, bh) =>
                let
                  val xi = ArrayHashSet.delete_ahm_basic_ops (A1_, A2_) bd ag;
                in
                  Refine_Det.DRETURN (ae, (ah, (xi, bh)))
                end)))
  end;

fun code_blue_dfs_ahs (A1_, A2_) g =
  Refine_Transfer.the_res
    (Refine_Det.dbind (Refine_Det.DRETURN (NDFS_SI_Statistics.start ()))
      (fn _ =>
        Refine_Det.dbind
          (Refine_Det.dbind
            (Refine_Det.DRETURN (Fun.id (Digraph_Impl.frgi_V0 g)))
            (fn xs =>
              Foldi.foldli xs
                (fn a =>
                  (case a of Refine_Det.DSUCCEEDi => false
                    | Refine_Det.DFAILi => false
                    | Refine_Det.DRETURN (_, (_, xd)) =>
                      equal_blue_witness A1_ xd NO_CYC))
                (fn x => fn s =>
                  Refine_Det.dbind s
                    (fn (a, (aa, _)) =>
                      (if not (ArrayHashSet.memb_ahm_basic_ops (A1_, A2_) x a)
                        then Refine_Det.dbind
                               (code_blue_dfs_ahs_0 (A1_, A2_) g
                                 (a, (aa, (ArrayHashSet.empty_ahm_basic_ops A2_
     (),
    x))))
                               (fn (ab, (ac, (_, bd))) =>
                                 Refine_Det.DRETURN (ab, (ac, bd)))
                        else Refine_Det.DRETURN (a, (aa, NO_CYC)))))
                (Refine_Det.DRETURN
                  (ArrayHashSet.empty_ahm_basic_ops A2_ (),
                    (ArrayHashSet.empty_ahm_basic_ops A2_ (), NO_CYC)))))
          (fn (_, (_, ba)) =>
            Refine_Det.dbind (Refine_Det.DRETURN (NDFS_SI_Statistics.stop ()))
              (fn _ => Refine_Det.DRETURN (extract_res ba)))));

end; (*struct NDFS_SI*)

structure While_Combinator : sig
  val whilea : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a
end = struct

fun whilea b c s = (if b s then whilea b c (c s) else s);

end; (*struct While_Combinator*)

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
  val g_to_list_ls_basic_ops : 'a Dlist.dlist -> 'a list
end = struct

fun g_sng_ls_basic_ops A_ x = Dlist.insert A_ x Dlist.empty;

fun iteratei_bset_op_list_it_ls_basic_ops s = Dlist_add.dlist_iteratei s;

fun g_union_ls_basic_ops A_ s1 s2 =
  iteratei_bset_op_list_it_ls_basic_ops s1 (fn _ => true) (Dlist.insert A_) s2;

fun g_isEmpty_ls_basic_ops s =
  iteratei_bset_op_list_it_ls_basic_ops s (fn c => c) (fn _ => fn _ => false)
    true;

fun g_to_list_ls_basic_ops s =
  iteratei_bset_op_list_it_ls_basic_ops s (fn _ => true)
    (fn a => fn b => a :: b) [];

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
    Arith.zero_nata;

fun g_list_to_map_lm_basic_ops A_ l =
  List.foldl (fn m => fn (k, v) => Assoc_List.update A_ k v m) Assoc_List.empty
    (List.rev l);

fun iteratei_map_op_list_it_lm_ops s = Assoc_List.iteratei s;

end; (*struct ListMapImpl*)

structure Code_String : sig
  val def_hashmap_size_uint_literal : string HOL.itself -> Arith.nat
  val hashcode_uint_literal : string -> Word32.word
  val hashable_uint_literal : string Collections_Patch1.hashable_uint
end = struct

fun def_hashmap_size_uint_literal uu = Arith.nat_of_integer (10 : IntInf.int);

fun hashcode_uint_literal s =
  Collections_Patch1.hashcode_uint_list Collections_Patch1.hashable_uint_char
    (String.explode s);

val hashable_uint_literal =
  {hashcode_uint = hashcode_uint_literal,
    def_hashmap_size_uint = def_hashmap_size_uint_literal}
  : string Collections_Patch1.hashable_uint;

end; (*struct Code_String*)

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
  val withChannela :
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
  val withChannel :
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
  val cleanChans : IntInf.int list -> channel list -> channel list
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
  val states :
    'a program_ext ->
      ((IntInf.int * unit edge_ext list) Vector.vector) Vector.vector
  val else_update :
    (bool -> bool) -> 'a gState_I_ext gState_ext -> 'a gState_I_ext gState_ext
  val pc : 'a pState_ext -> Arith.nat
  val sort_by_pri : Arith.nat -> 'a edge_ext list -> ('a edge_ext list) list
  val executable_impl :
    ((IntInf.int * unit edge_ext list) Vector.vector) Vector.vector ->
      unit gState_I_ext gState_ext -> (unit edge_ext * unit pState_ext) list
  val exclusive_update :
    (Arith.nat -> Arith.nat) ->
      'a gState_I_ext gState_ext -> 'a gState_I_ext gState_ext
  val pc_update : (Arith.nat -> Arith.nat) -> 'a pState_ext -> 'a pState_ext
  val effect : 'a edge_ext -> edgeEffect
  val removeProcs :
    'a pState_ext list -> bool * (bool * ('a pState_ext list * IntInf.int list))
  val checkDeadProcs : 'a gState_ext -> 'a gState_ext
  val applyEdge_impl :
    unit program_ext ->
      unit edge_ext ->
        unit pState_ext ->
          unit gState_I_ext gState_ext -> unit gState_I_ext gState_ext
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
  val equal_binOp : binOp -> binOp -> bool
  val equal_unOp : unOp -> unOp -> bool
  val equal_expr : expr HOL.equal
  val equal_varRef : varRef -> varRef -> bool
  val equal_chanRef : chanRef -> chanRef -> bool
  val equal_recvArga : recvArg -> recvArg -> bool
  val equal_recvArg : recvArg HOL.equal
  val equal_expra : expr -> expr -> bool
  val preprocess :
    PromelaAST.module list ->
      varDecl list * (proc list * (string * string) list)
  val printEdges :
    (IntInf.int -> char list) ->
      (IntInf.int * unit edge_ext list) Vector.vector -> (char list) list
  val gState2HASH :
    'a gState_ext ->
      (string, variable) Assoc_List.assoc_list *
        (channel list * (bool * (unit pState_ext list * 'a)))
  val pState2HASH :
    'a pState_ext ->
      Arith.nat *
        ((string, variable) Assoc_List.assoc_list *
          (Arith.nat * (IntInf.int list * (Arith.nat * 'a))))
  val printLabels :
    (IntInf.int -> char list) ->
      (string, Arith.nat) Assoc_List.assoc_list -> (char list) list
  val walk_iarraya :
    ('a -> 'b -> 'a) -> 'b Vector.vector -> 'a -> Arith.nat -> Arith.nat -> 'a
  val walk_iarray : ('a -> 'b -> 'a) -> 'b Vector.vector -> 'a -> 'a
  val printProcesses :
    (IntInf.int -> char list) -> unit program_ext -> (char list) list
  val equal_gState_ext : 'a HOL.equal -> 'a gState_ext HOL.equal
  val def_hashmap_size_uint_gState_ext :
    'a Collections_Patch1.hashable_uint -> 'a gState_ext HOL.itself -> Arith.nat
  val def_hashmap_size_gState_ext :
    'a Collections_Patch1.hashable_uint -> 'a gState_ext HOL.itself -> Arith.nat
  val def_hashmap_size_uint_pState_ext :
    'a Collections_Patch1.hashable_uint -> 'a pState_ext HOL.itself -> Arith.nat
  val def_hashmap_size_uint_assoc_list :
    'a Collections_Patch1.hashable_uint ->
      'b Collections_Patch1.hashable_uint ->
      ('a, 'b) Assoc_List.assoc_list HOL.itself -> Arith.nat
  val hashcode_uint_assoc_list :
    'a Collections_Patch1.hashable_uint ->
      'b Collections_Patch1.hashable_uint ->
      ('a, 'b) Assoc_List.assoc_list -> Word32.word
  val hashable_uint_assoc_list :
    'a Collections_Patch1.hashable_uint ->
      'b Collections_Patch1.hashable_uint ->
      ('a, 'b) Assoc_List.assoc_list Collections_Patch1.hashable_uint
  val def_hashmap_size_uint_variable : variable HOL.itself -> Arith.nat
  val def_hashmap_size_uint_varType : varType HOL.itself -> Arith.nat
  val hashcode_uint_varType : varType -> Word32.word
  val hashable_uint_varType : varType Collections_Patch1.hashable_uint
  val def_hashmap_size_uint_iarray :
    'a Collections_Patch1.hashable_uint ->
      ('a Vector.vector) HOL.itself -> Arith.nat
  val hashcode_uint_iarray :
    'a Collections_Patch1.hashable_uint -> 'a Vector.vector -> Word32.word
  val hashable_uint_iarray :
    'a Collections_Patch1.hashable_uint ->
      ('a Vector.vector) Collections_Patch1.hashable_uint
  val hashcode_uint_variable : variable -> Word32.word
  val hashable_uint_variable : variable Collections_Patch1.hashable_uint
  val hashcode_uint_pState_ext :
    'a Collections_Patch1.hashable_uint -> 'a pState_ext -> Word32.word
  val hashable_uint_pState_ext :
    'a Collections_Patch1.hashable_uint ->
      'a pState_ext Collections_Patch1.hashable_uint
  val def_hashmap_size_uint_channel : channel HOL.itself -> Arith.nat
  val hashcode_uint_channel : channel -> Word32.word
  val hashable_uint_channel : channel Collections_Patch1.hashable_uint
  val hashcode_uint_gState_ext :
    'a Collections_Patch1.hashable_uint -> 'a gState_ext -> Word32.word
  val hashable_uint_gState_ext :
    'a Collections_Patch1.hashable_uint ->
      'a gState_ext Collections_Patch1.hashable_uint
  val bounded_hashcode_gState_ext :
    'a Collections_Patch1.hashable_uint ->
      Arith.nat -> 'a gState_ext -> Arith.nat
  val hashcode_gState_ext :
    'a Collections_Patch1.hashable_uint -> 'a gState_ext -> Arith.nat
  val hashable_gState_ext :
    'a Collections_Patch1.hashable_uint -> 'a gState_ext HashCode.hashable
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
      GState_I_ext (Arith.zero_nata, [], Arith.zero_nata, false, ()));

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
                  Arith.equal_nata (List.size_list x)
                    (List.size_list ts) andalso
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
  | lookupVar (VArray (uy, uz, vals)) NONE = IArray.sub vals Arith.zero_nata
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

fun withChannela gl v idx f g p =
  let
    val error =
      (fn _ =>
        (raise Fail
          (String.implode
            ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #" ", #"i", #"s",
               #" ", #"n", #"o", #"t", #" ", #"a", #" ", #"c", #"h", #"a", #"n",
               #"n", #"e", #"l", #":", #" "] @
              String.explode v)))
          (fn _ => f Arith.zero_nata InvChannel));
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
                       (raise Fail msg) (fn _ => f Arith.zero_nata InvChannel))
                 end)
        end)
      g p
  end;

fun exprArith g p (ExprConst x) = x
  | exprArith g p (ExprMConst (x, uu)) = x
  | exprArith g p ExprTimeOut = (if timeout g then (1 : IntInf.int) else 0)
  | exprArith g p (ExprLen (ChanRef (VarRef (gl, name, NONE)))) =
    withChannela gl name NONE
      (fn _ => fn a =>
        (case a of Channel (_, _, q) => Arith.integer_of_nat (List.size_list q)
          | HSChannel _ => 0))
      g p
  | exprArith g p (ExprLen (ChanRef (VarRef (gl, name, SOME idx)))) =
    withChannela gl name (SOME (exprArith g p idx))
      (fn _ => fn a =>
        (case a of Channel (_, _, q) => Arith.integer_of_nat (List.size_list q)
          | HSChannel _ => 0))
      g p
  | exprArith g p (ExprEmpty (ChanRef (VarRef (gl, name, NONE)))) =
    (if withChannela gl name NONE
          (fn _ => fn a =>
            (case a of Channel (_, _, aa) => List.null aa
              | HSChannel _ => true))
          g p
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprEmpty (ChanRef (VarRef (gl, name, SOME idx)))) =
    (if withChannela gl name (SOME (exprArith g p idx))
          (fn _ => fn a =>
            (case a of Channel (_, _, aa) => List.null aa
              | HSChannel _ => true))
          g p
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprFull (ChanRef (VarRef (gl, name, NONE)))) =
    (if withChannela gl name NONE
          (fn _ => fn a =>
            (case a
              of Channel (cap, _, q) =>
                IntInf.<= (cap, Arith.integer_of_nat (List.size_list q))
              | HSChannel _ => false))
          g p
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprFull (ChanRef (VarRef (gl, name, SOME idx)))) =
    (if withChannela gl name (SOME (exprArith g p idx))
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
    (if withChannela gl name NONE (fn _ => fn c => pollCheck g p c rs srt) g p
      then (1 : IntInf.int) else 0)
  | exprArith g p (ExprPoll (ChanRef (VarRef (gl, name, SOME idx)), rs, srt)) =
    (if withChannela gl name (SOME (exprArith g p idx))
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
        (fn _ => Arith.zero_nata)
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
      (fn _ => ([], (Index Arith.zero_nata, Assoc_List.empty)))
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
  [Edge_ext (ECFalse, EEEnd, Index Arith.zero_nata, 0, NonAtomic, ())];

fun toStates steps =
  let
    val (states, (pos, lbls)) =
      step_fold stepToState steps Assoc_List.empty 0 Arith.one_nata
        (Index Arith.zero_nata) NONE false;
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
             (fn _ => (Vector.fromList statesc, (Index Arith.zero_nata, lbls))))
  end;

fun toProcess sidx (ProcType (act, name, args, decls, steps)) =
  let
    val (states, (start, lbls)) = toStates steps;
    val acta =
      (case act of NONE => Arith.zero_nata | SOME NONE => Arith.one_nata
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
    (Arith.zero_nata, Assoc_List.empty, Arith.zero_nata, [], Arith.zero_nata,
      ());

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
        | LabelJump (_, _) => (raise Fail "UGH!") (fn _ => Arith.zero_nata));
  in
    (if not (Arith.equal_nata (List.size_list args) (List.size_list argDecls))
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
        ((Arith.zero_nata, (Index Arith.zero_nata, ([], []))) ::
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
      val v = List.list_update lv Arith.zero_nata (checkVarValue typea vala);
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
        (Arith.zero_nata,
          (if not (Arith.equal_nata hs Arith.zero_nata) then hsd else []),
          Arith.zero_nata, false, ()));

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

fun withChannel (ChanRef v) = liftVar withChannela v;

fun evalCond ECTrue uu uv = true
  | evalCond ECFalse uw ux = false
  | evalCond (ECExpr e) g l = not (((exprArith g l e) : IntInf.int) = 0)
  | evalCond (ECRun uy) g l =
    Arith.less_nat (List.size_list (procs g))
      (Arith.nat_of_integer (255 : IntInf.int))
  | evalCond ECElse g l = elsea g
  | evalCond (ECSend v) g l =
    withChannel v
      (fn _ => fn a =>
        (case a
          of Channel (cap, _, q) =>
            IntInf.< (Arith.integer_of_nat (List.size_list q), cap)
          | HSChannel _ => true))
      g l
  | evalCond (ECRecv (v, rs, srt)) g l =
    withChannel v
      (fn _ => fn c =>
        (case c of Channel (_, _, _) => pollCheck g l c rs srt
          | HSChannel _ =>
            not (Arith.equal_nata (handshake g) Arith.zero_nata) andalso
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

fun cleanChans dchans cs =
  Product_Type.snd
    (List.foldl
      (fn (i, csa) => fn c =>
        (if List.member Arith.equal_integer dchans i
          then (IntInf.+ (i, (1 : IntInf.int)), csa @ [InvChannel])
          else (IntInf.+ (i, (1 : IntInf.int)), csa @ [c])))
      (0, []) cs);

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
    withChannel v
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
                     (if not (Arith.equal_nata (List.size_list ts)
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
                     (if not (Arith.equal_nata (List.size_list ts)
                               (List.size_list esa))
                       then aborta ()
                       else (handshake_update (fn _ => i)
                               (hsdata_update (fn _ => esa) g),
                              l))
                   | InvChannel => (raise Fail "INVALID") (fn _ => (g, l))))
        end)
      g l
  | evalEffect (EERecv (v, rs, srt, rem)) vb g l =
    withChannel v
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
                  (handshake_update (fn _ => Arith.zero_nata) ga);
            in
              (gb, la)
            end
          | InvChannel => (raise Fail "INVALID") (fn _ => (g, l))))
      g l;

fun cond (Edge_ext (cond, effect, target, prio, atomic, more)) = cond;

fun evalHandshake (ECRecv (v, uu, uv)) h g l =
  Arith.equal_nata h Arith.zero_nata orelse
    withChannel v
      (fn i => fn a =>
        (case a of Channel (_, _, _) => false
          | HSChannel _ => Arith.equal_nata i h))
      g l
  | evalHandshake ECElse h ux uy = Arith.equal_nata h Arith.zero_nata
  | evalHandshake ECTrue h ux uy = Arith.equal_nata h Arith.zero_nata
  | evalHandshake ECFalse h ux uy = Arith.equal_nata h Arith.zero_nata
  | evalHandshake (ECExpr v) h ux uy = Arith.equal_nata h Arith.zero_nata
  | evalHandshake (ECRun v) h ux uy = Arith.equal_nata h Arith.zero_nata
  | evalHandshake (ECSend v) h ux uy = Arith.equal_nata h Arith.zero_nata;

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

fun states
  (Program_ext (processes, labels, states, proc_names, proc_data, more)) =
  states;

fun else_update elseaa
  (GState_ext
    (vars, channels, timeout, procs,
      GState_I_ext (handshake, hsdata, exclusive, elsea, more)))
  = GState_ext
      (vars, channels, timeout, procs,
        GState_I_ext (handshake, hsdata, exclusive, elseaa elsea, more));

fun pc (PState_ext (pid, vars, pc, channels, idx, more)) = pc;

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
        (if Arith.equal_nata (exclusive g) Arith.zero_nata orelse
              Arith.equal_nata (exclusive g) (pid xa)
          then let
                 val (xb, xc) = IArray.sub (IArray.sub s (idx xa)) (pc xa);
                 val (xd, (_, _)) =
                   (if ((xb : IntInf.int) = 0)
                     then While_Combinator.whilea
                            (fn (e, (brk, _)) =>
                              List.null e andalso
                                Arith.equal_nata brk Arith.zero_nata)
                            (fn (_, (_, xab)) =>
                              let
                                val xba = else_update (fn _ => xab) g;
                                val xd = getChoices xba xa xc;
                              in
                                (if List.null xd
                                  then (if not xab
 then (xd, (Arith.zero_nata, true)) else (xd, (Arith.one_nata, false)))
                                  else (xd, (Arith.one_nata, xab)))
                              end)
                            ([], (Arith.zero_nata, false))
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
                              ([], (Arith.zero_nata, false))
                          end);
               in
                 xd @ xaa
               end
          else xaa))
      []
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

fun effect (Edge_ext (cond, effect, target, prio, atomic, more)) = effect;

fun removeProcs ps =
  List.foldr
    (fn p => fn (dead, (sd, (psa, dcs))) =>
      (if dead andalso Arith.equal_nata (pc p) Arith.zero_nata
        then (true, (true, (psa, channelsa p @ dcs)))
        else (false, (sd, (p :: psa, dcs)))))
    ps (true, (false, ([], [])));

fun checkDeadProcs g =
  (case removeProcs (procs g)
    of (_, (true, (procsa, dchans))) =>
      channels_update (fn _ => cleanChans dchans (channels g))
        (procs_update (fn _ => procsa) g)
    | (_, (false, (procsa, dchans))) => g);

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
      (if isAtomic e andalso Arith.equal_nata (handshake xb) Arith.zero_nata
        then exclusive_update (fn _ => pid xaa) xb else xb);
    val xd =
      (if Arith.equal_nata (pc xaa) Arith.zero_nata then checkDeadProcs xc
        else xc);
  in
    xd
  end;

fun nexts_code_0 A_ prog b x =
  Refine_Det.dbind (Refine_Det.DRETURN (executable_impl (states prog) x))
    (fn xa =>
      (if List.null xa
        then (if not (Arith.equal_nata (handshake x) Arith.zero_nata)
               then Refine_Det.DRETURN Dlist.empty
               else (if not (Arith.equal_nata (exclusive x) Arith.zero_nata)
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
                             (if not (Arith.equal_nata (handshake xd)
                                       Arith.zero_nata) orelse
                                   isAtomic xab
                               then Refine_Det.dbind (nexts_code_0 A_ prog b xd)
                                      (fn xac =>
(if ListSetImpl.g_isEmpty_ls_basic_ops xac andalso
      Arith.equal_nata (handshake xd) Arith.zero_nata
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
      (Arith.equal_nata nata nat andalso
        IArray.equal_iarray Arith.equal_integer iarraya iarray)
  | equal_variablea (Var (varTypea, integera)) (Var (varType, integer)) =
    equal_varTypea varTypea varType andalso ((integera : IntInf.int) = integer);

val equal_variable = {equal = equal_variablea} : variable HOL.equal;

fun equal_pState_exta A_ (PState_ext (pida, varsa, pca, channelsa, idxa, morea))
  (PState_ext (pid, vars, pc, channels, idx, more)) =
  Arith.equal_nata pida pid andalso
    (Assoc_List.equal_assoc_list Stringa.equal_literal equal_variable varsa
       vars andalso
      (Arith.equal_nata pca pc andalso
        (List.equal_lista Arith.equal_integer channelsa channels andalso
          (Arith.equal_nata idxa idx andalso HOL.eq A_ morea more))));

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
                                     Arith.equal_nata (handshake xd)
                                       Arith.zero_nata
                                 then exclusive_update (fn _ => pid xbc) xd
                                 else xd);
                             val aa =
                               (if Arith.equal_nata (pc xbc) Arith.zero_nata
                                 then checkDeadProcs xe else xe);
                           in
                             Refine_Det.DRETURN aa
                           end
                           (fn xc =>
                             (if not (Arith.equal_nata (handshake xc)
                                       Arith.zero_nata) orelse
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
          (if not (Arith.equal_nata (List.size_list names)
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

fun equal_binOp BinOpOr BinOpAnd = false
  | equal_binOp BinOpAnd BinOpOr = false
  | equal_binOp BinOpOr BinOpNEq = false
  | equal_binOp BinOpNEq BinOpOr = false
  | equal_binOp BinOpAnd BinOpNEq = false
  | equal_binOp BinOpNEq BinOpAnd = false
  | equal_binOp BinOpOr BinOpEq = false
  | equal_binOp BinOpEq BinOpOr = false
  | equal_binOp BinOpAnd BinOpEq = false
  | equal_binOp BinOpEq BinOpAnd = false
  | equal_binOp BinOpNEq BinOpEq = false
  | equal_binOp BinOpEq BinOpNEq = false
  | equal_binOp BinOpOr BinOpLEq = false
  | equal_binOp BinOpLEq BinOpOr = false
  | equal_binOp BinOpAnd BinOpLEq = false
  | equal_binOp BinOpLEq BinOpAnd = false
  | equal_binOp BinOpNEq BinOpLEq = false
  | equal_binOp BinOpLEq BinOpNEq = false
  | equal_binOp BinOpEq BinOpLEq = false
  | equal_binOp BinOpLEq BinOpEq = false
  | equal_binOp BinOpOr BinOpGEq = false
  | equal_binOp BinOpGEq BinOpOr = false
  | equal_binOp BinOpAnd BinOpGEq = false
  | equal_binOp BinOpGEq BinOpAnd = false
  | equal_binOp BinOpNEq BinOpGEq = false
  | equal_binOp BinOpGEq BinOpNEq = false
  | equal_binOp BinOpEq BinOpGEq = false
  | equal_binOp BinOpGEq BinOpEq = false
  | equal_binOp BinOpLEq BinOpGEq = false
  | equal_binOp BinOpGEq BinOpLEq = false
  | equal_binOp BinOpOr BinOpLe = false
  | equal_binOp BinOpLe BinOpOr = false
  | equal_binOp BinOpAnd BinOpLe = false
  | equal_binOp BinOpLe BinOpAnd = false
  | equal_binOp BinOpNEq BinOpLe = false
  | equal_binOp BinOpLe BinOpNEq = false
  | equal_binOp BinOpEq BinOpLe = false
  | equal_binOp BinOpLe BinOpEq = false
  | equal_binOp BinOpLEq BinOpLe = false
  | equal_binOp BinOpLe BinOpLEq = false
  | equal_binOp BinOpGEq BinOpLe = false
  | equal_binOp BinOpLe BinOpGEq = false
  | equal_binOp BinOpOr BinOpGr = false
  | equal_binOp BinOpGr BinOpOr = false
  | equal_binOp BinOpAnd BinOpGr = false
  | equal_binOp BinOpGr BinOpAnd = false
  | equal_binOp BinOpNEq BinOpGr = false
  | equal_binOp BinOpGr BinOpNEq = false
  | equal_binOp BinOpEq BinOpGr = false
  | equal_binOp BinOpGr BinOpEq = false
  | equal_binOp BinOpLEq BinOpGr = false
  | equal_binOp BinOpGr BinOpLEq = false
  | equal_binOp BinOpGEq BinOpGr = false
  | equal_binOp BinOpGr BinOpGEq = false
  | equal_binOp BinOpLe BinOpGr = false
  | equal_binOp BinOpGr BinOpLe = false
  | equal_binOp BinOpOr BinOpMod = false
  | equal_binOp BinOpMod BinOpOr = false
  | equal_binOp BinOpAnd BinOpMod = false
  | equal_binOp BinOpMod BinOpAnd = false
  | equal_binOp BinOpNEq BinOpMod = false
  | equal_binOp BinOpMod BinOpNEq = false
  | equal_binOp BinOpEq BinOpMod = false
  | equal_binOp BinOpMod BinOpEq = false
  | equal_binOp BinOpLEq BinOpMod = false
  | equal_binOp BinOpMod BinOpLEq = false
  | equal_binOp BinOpGEq BinOpMod = false
  | equal_binOp BinOpMod BinOpGEq = false
  | equal_binOp BinOpLe BinOpMod = false
  | equal_binOp BinOpMod BinOpLe = false
  | equal_binOp BinOpGr BinOpMod = false
  | equal_binOp BinOpMod BinOpGr = false
  | equal_binOp BinOpOr BinOpDiv = false
  | equal_binOp BinOpDiv BinOpOr = false
  | equal_binOp BinOpAnd BinOpDiv = false
  | equal_binOp BinOpDiv BinOpAnd = false
  | equal_binOp BinOpNEq BinOpDiv = false
  | equal_binOp BinOpDiv BinOpNEq = false
  | equal_binOp BinOpEq BinOpDiv = false
  | equal_binOp BinOpDiv BinOpEq = false
  | equal_binOp BinOpLEq BinOpDiv = false
  | equal_binOp BinOpDiv BinOpLEq = false
  | equal_binOp BinOpGEq BinOpDiv = false
  | equal_binOp BinOpDiv BinOpGEq = false
  | equal_binOp BinOpLe BinOpDiv = false
  | equal_binOp BinOpDiv BinOpLe = false
  | equal_binOp BinOpGr BinOpDiv = false
  | equal_binOp BinOpDiv BinOpGr = false
  | equal_binOp BinOpMod BinOpDiv = false
  | equal_binOp BinOpDiv BinOpMod = false
  | equal_binOp BinOpOr BinOpMul = false
  | equal_binOp BinOpMul BinOpOr = false
  | equal_binOp BinOpAnd BinOpMul = false
  | equal_binOp BinOpMul BinOpAnd = false
  | equal_binOp BinOpNEq BinOpMul = false
  | equal_binOp BinOpMul BinOpNEq = false
  | equal_binOp BinOpEq BinOpMul = false
  | equal_binOp BinOpMul BinOpEq = false
  | equal_binOp BinOpLEq BinOpMul = false
  | equal_binOp BinOpMul BinOpLEq = false
  | equal_binOp BinOpGEq BinOpMul = false
  | equal_binOp BinOpMul BinOpGEq = false
  | equal_binOp BinOpLe BinOpMul = false
  | equal_binOp BinOpMul BinOpLe = false
  | equal_binOp BinOpGr BinOpMul = false
  | equal_binOp BinOpMul BinOpGr = false
  | equal_binOp BinOpMod BinOpMul = false
  | equal_binOp BinOpMul BinOpMod = false
  | equal_binOp BinOpDiv BinOpMul = false
  | equal_binOp BinOpMul BinOpDiv = false
  | equal_binOp BinOpOr BinOpSub = false
  | equal_binOp BinOpSub BinOpOr = false
  | equal_binOp BinOpAnd BinOpSub = false
  | equal_binOp BinOpSub BinOpAnd = false
  | equal_binOp BinOpNEq BinOpSub = false
  | equal_binOp BinOpSub BinOpNEq = false
  | equal_binOp BinOpEq BinOpSub = false
  | equal_binOp BinOpSub BinOpEq = false
  | equal_binOp BinOpLEq BinOpSub = false
  | equal_binOp BinOpSub BinOpLEq = false
  | equal_binOp BinOpGEq BinOpSub = false
  | equal_binOp BinOpSub BinOpGEq = false
  | equal_binOp BinOpLe BinOpSub = false
  | equal_binOp BinOpSub BinOpLe = false
  | equal_binOp BinOpGr BinOpSub = false
  | equal_binOp BinOpSub BinOpGr = false
  | equal_binOp BinOpMod BinOpSub = false
  | equal_binOp BinOpSub BinOpMod = false
  | equal_binOp BinOpDiv BinOpSub = false
  | equal_binOp BinOpSub BinOpDiv = false
  | equal_binOp BinOpMul BinOpSub = false
  | equal_binOp BinOpSub BinOpMul = false
  | equal_binOp BinOpOr BinOpAdd = false
  | equal_binOp BinOpAdd BinOpOr = false
  | equal_binOp BinOpAnd BinOpAdd = false
  | equal_binOp BinOpAdd BinOpAnd = false
  | equal_binOp BinOpNEq BinOpAdd = false
  | equal_binOp BinOpAdd BinOpNEq = false
  | equal_binOp BinOpEq BinOpAdd = false
  | equal_binOp BinOpAdd BinOpEq = false
  | equal_binOp BinOpLEq BinOpAdd = false
  | equal_binOp BinOpAdd BinOpLEq = false
  | equal_binOp BinOpGEq BinOpAdd = false
  | equal_binOp BinOpAdd BinOpGEq = false
  | equal_binOp BinOpLe BinOpAdd = false
  | equal_binOp BinOpAdd BinOpLe = false
  | equal_binOp BinOpGr BinOpAdd = false
  | equal_binOp BinOpAdd BinOpGr = false
  | equal_binOp BinOpMod BinOpAdd = false
  | equal_binOp BinOpAdd BinOpMod = false
  | equal_binOp BinOpDiv BinOpAdd = false
  | equal_binOp BinOpAdd BinOpDiv = false
  | equal_binOp BinOpMul BinOpAdd = false
  | equal_binOp BinOpAdd BinOpMul = false
  | equal_binOp BinOpSub BinOpAdd = false
  | equal_binOp BinOpAdd BinOpSub = false
  | equal_binOp BinOpOr BinOpOr = true
  | equal_binOp BinOpAnd BinOpAnd = true
  | equal_binOp BinOpNEq BinOpNEq = true
  | equal_binOp BinOpEq BinOpEq = true
  | equal_binOp BinOpLEq BinOpLEq = true
  | equal_binOp BinOpGEq BinOpGEq = true
  | equal_binOp BinOpLe BinOpLe = true
  | equal_binOp BinOpGr BinOpGr = true
  | equal_binOp BinOpMod BinOpMod = true
  | equal_binOp BinOpDiv BinOpDiv = true
  | equal_binOp BinOpMul BinOpMul = true
  | equal_binOp BinOpSub BinOpSub = true
  | equal_binOp BinOpAdd BinOpAdd = true;

fun equal_unOp UnOpNeg UnOpMinus = false
  | equal_unOp UnOpMinus UnOpNeg = false
  | equal_unOp UnOpNeg UnOpNeg = true
  | equal_unOp UnOpMinus UnOpMinus = true;

fun equal_expr () = {equal = equal_expra} : expr HOL.equal
and equal_varRef (VarRef (boolaa, literala, optionaa))
  (VarRef (boola, literal, optiona)) =
  Product_Type.equal_bool boolaa boola andalso
    (((literala : string) = literal) andalso
      Option.equal_option (equal_expr ()) optionaa optiona)
and equal_chanRef (ChanRef varRefa) (ChanRef varRef) =
  equal_varRef varRefa varRef
and equal_recvArga (RecvArgMConst (integera, literal)) (RecvArgConst integer) =
  false
  | equal_recvArga (RecvArgConst integera) (RecvArgMConst (integer, literal)) =
    false
  | equal_recvArga (RecvArgMConst (integer, literal)) (RecvArgEval expr) = false
  | equal_recvArga (RecvArgEval expr) (RecvArgMConst (integer, literal)) = false
  | equal_recvArga (RecvArgConst integer) (RecvArgEval expr) = false
  | equal_recvArga (RecvArgEval expr) (RecvArgConst integer) = false
  | equal_recvArga (RecvArgMConst (integer, literal)) (RecvArgVar varRef) =
    false
  | equal_recvArga (RecvArgVar varRef) (RecvArgMConst (integer, literal)) =
    false
  | equal_recvArga (RecvArgConst integer) (RecvArgVar varRef) = false
  | equal_recvArga (RecvArgVar varRef) (RecvArgConst integer) = false
  | equal_recvArga (RecvArgEval expr) (RecvArgVar varRef) = false
  | equal_recvArga (RecvArgVar varRef) (RecvArgEval expr) = false
  | equal_recvArga (RecvArgMConst (integera, literala))
    (RecvArgMConst (integer, literal)) =
    ((integera : IntInf.int) = integer) andalso ((literala : string) = literal)
  | equal_recvArga (RecvArgConst integera) (RecvArgConst integer) =
    ((integera : IntInf.int) = integer)
  | equal_recvArga (RecvArgEval expra) (RecvArgEval expr) =
    equal_expra expra expr
  | equal_recvArga (RecvArgVar varRefa) (RecvArgVar varRef) =
    equal_varRef varRefa varRef
and equal_recvArg () = {equal = equal_recvArga} : recvArg HOL.equal
and equal_expra (ExprPoll (chanRefa, lista, boola)) (ExprEmpty chanRef) = false
  | equal_expra (ExprEmpty chanRefa) (ExprPoll (chanRef, lista, boola)) = false
  | equal_expra (ExprPoll (chanRefa, lista, boola)) (ExprFull chanRef) = false
  | equal_expra (ExprFull chanRefa) (ExprPoll (chanRef, lista, boola)) = false
  | equal_expra (ExprEmpty chanRefa) (ExprFull chanRef) = false
  | equal_expra (ExprFull chanRefa) (ExprEmpty chanRef) = false
  | equal_expra (ExprPoll (chanRef, lista, boola)) ExprTimeOut = false
  | equal_expra ExprTimeOut (ExprPoll (chanRef, lista, boola)) = false
  | equal_expra (ExprEmpty chanRef) ExprTimeOut = false
  | equal_expra ExprTimeOut (ExprEmpty chanRef) = false
  | equal_expra (ExprFull chanRef) ExprTimeOut = false
  | equal_expra ExprTimeOut (ExprFull chanRef) = false
  | equal_expra (ExprPoll (chanRef, lista, boola))
    (ExprMConst (integer, literal)) = false
  | equal_expra (ExprMConst (integer, literal))
    (ExprPoll (chanRef, lista, boola)) = false
  | equal_expra (ExprEmpty chanRef) (ExprMConst (integer, literal)) = false
  | equal_expra (ExprMConst (integer, literal)) (ExprEmpty chanRef) = false
  | equal_expra (ExprFull chanRef) (ExprMConst (integer, literal)) = false
  | equal_expra (ExprMConst (integer, literal)) (ExprFull chanRef) = false
  | equal_expra ExprTimeOut (ExprMConst (integer, literal)) = false
  | equal_expra (ExprMConst (integer, literal)) ExprTimeOut = false
  | equal_expra (ExprPoll (chanRef, lista, boola)) (ExprConst integer) = false
  | equal_expra (ExprConst integer) (ExprPoll (chanRef, lista, boola)) = false
  | equal_expra (ExprEmpty chanRef) (ExprConst integer) = false
  | equal_expra (ExprConst integer) (ExprEmpty chanRef) = false
  | equal_expra (ExprFull chanRef) (ExprConst integer) = false
  | equal_expra (ExprConst integer) (ExprFull chanRef) = false
  | equal_expra ExprTimeOut (ExprConst integer) = false
  | equal_expra (ExprConst integer) ExprTimeOut = false
  | equal_expra (ExprMConst (integera, literal)) (ExprConst integer) = false
  | equal_expra (ExprConst integera) (ExprMConst (integer, literal)) = false
  | equal_expra (ExprPoll (chanRef, lista, boola)) (ExprVarRef varRef) = false
  | equal_expra (ExprVarRef varRef) (ExprPoll (chanRef, lista, boola)) = false
  | equal_expra (ExprEmpty chanRef) (ExprVarRef varRef) = false
  | equal_expra (ExprVarRef varRef) (ExprEmpty chanRef) = false
  | equal_expra (ExprFull chanRef) (ExprVarRef varRef) = false
  | equal_expra (ExprVarRef varRef) (ExprFull chanRef) = false
  | equal_expra ExprTimeOut (ExprVarRef varRef) = false
  | equal_expra (ExprVarRef varRef) ExprTimeOut = false
  | equal_expra (ExprMConst (integer, literal)) (ExprVarRef varRef) = false
  | equal_expra (ExprVarRef varRef) (ExprMConst (integer, literal)) = false
  | equal_expra (ExprConst integer) (ExprVarRef varRef) = false
  | equal_expra (ExprVarRef varRef) (ExprConst integer) = false
  | equal_expra (ExprPoll (chanRefa, lista, boola)) (ExprLen chanRef) = false
  | equal_expra (ExprLen chanRefa) (ExprPoll (chanRef, lista, boola)) = false
  | equal_expra (ExprEmpty chanRefa) (ExprLen chanRef) = false
  | equal_expra (ExprLen chanRefa) (ExprEmpty chanRef) = false
  | equal_expra (ExprFull chanRefa) (ExprLen chanRef) = false
  | equal_expra (ExprLen chanRefa) (ExprFull chanRef) = false
  | equal_expra ExprTimeOut (ExprLen chanRef) = false
  | equal_expra (ExprLen chanRef) ExprTimeOut = false
  | equal_expra (ExprMConst (integer, literal)) (ExprLen chanRef) = false
  | equal_expra (ExprLen chanRef) (ExprMConst (integer, literal)) = false
  | equal_expra (ExprConst integer) (ExprLen chanRef) = false
  | equal_expra (ExprLen chanRef) (ExprConst integer) = false
  | equal_expra (ExprVarRef varRef) (ExprLen chanRef) = false
  | equal_expra (ExprLen chanRef) (ExprVarRef varRef) = false
  | equal_expra (ExprPoll (chanRef, lista, boola))
    (ExprCond (expr1, expr2, expr3)) = false
  | equal_expra (ExprCond (expr1, expr2, expr3))
    (ExprPoll (chanRef, lista, boola)) = false
  | equal_expra (ExprEmpty chanRef) (ExprCond (expr1, expr2, expr3)) = false
  | equal_expra (ExprCond (expr1, expr2, expr3)) (ExprEmpty chanRef) = false
  | equal_expra (ExprFull chanRef) (ExprCond (expr1, expr2, expr3)) = false
  | equal_expra (ExprCond (expr1, expr2, expr3)) (ExprFull chanRef) = false
  | equal_expra ExprTimeOut (ExprCond (expr1, expr2, expr3)) = false
  | equal_expra (ExprCond (expr1, expr2, expr3)) ExprTimeOut = false
  | equal_expra (ExprMConst (integer, literal)) (ExprCond (expr1, expr2, expr3))
    = false
  | equal_expra (ExprCond (expr1, expr2, expr3)) (ExprMConst (integer, literal))
    = false
  | equal_expra (ExprConst integer) (ExprCond (expr1, expr2, expr3)) = false
  | equal_expra (ExprCond (expr1, expr2, expr3)) (ExprConst integer) = false
  | equal_expra (ExprVarRef varRef) (ExprCond (expr1, expr2, expr3)) = false
  | equal_expra (ExprCond (expr1, expr2, expr3)) (ExprVarRef varRef) = false
  | equal_expra (ExprLen chanRef) (ExprCond (expr1, expr2, expr3)) = false
  | equal_expra (ExprCond (expr1, expr2, expr3)) (ExprLen chanRef) = false
  | equal_expra (ExprPoll (chanRef, lista, boola)) (ExprUnOp (unOp, expr)) =
    false
  | equal_expra (ExprUnOp (unOp, expr)) (ExprPoll (chanRef, lista, boola)) =
    false
  | equal_expra (ExprEmpty chanRef) (ExprUnOp (unOp, expr)) = false
  | equal_expra (ExprUnOp (unOp, expr)) (ExprEmpty chanRef) = false
  | equal_expra (ExprFull chanRef) (ExprUnOp (unOp, expr)) = false
  | equal_expra (ExprUnOp (unOp, expr)) (ExprFull chanRef) = false
  | equal_expra ExprTimeOut (ExprUnOp (unOp, expr)) = false
  | equal_expra (ExprUnOp (unOp, expr)) ExprTimeOut = false
  | equal_expra (ExprMConst (integer, literal)) (ExprUnOp (unOp, expr)) = false
  | equal_expra (ExprUnOp (unOp, expr)) (ExprMConst (integer, literal)) = false
  | equal_expra (ExprConst integer) (ExprUnOp (unOp, expr)) = false
  | equal_expra (ExprUnOp (unOp, expr)) (ExprConst integer) = false
  | equal_expra (ExprVarRef varRef) (ExprUnOp (unOp, expr)) = false
  | equal_expra (ExprUnOp (unOp, expr)) (ExprVarRef varRef) = false
  | equal_expra (ExprLen chanRef) (ExprUnOp (unOp, expr)) = false
  | equal_expra (ExprUnOp (unOp, expr)) (ExprLen chanRef) = false
  | equal_expra (ExprCond (expr1, expr2, expr3)) (ExprUnOp (unOp, expr)) = false
  | equal_expra (ExprUnOp (unOp, expr)) (ExprCond (expr1, expr2, expr3)) = false
  | equal_expra (ExprPoll (chanRef, lista, boola))
    (ExprBinOp (binOp, expr1, expr2)) = false
  | equal_expra (ExprBinOp (binOp, expr1, expr2))
    (ExprPoll (chanRef, lista, boola)) = false
  | equal_expra (ExprEmpty chanRef) (ExprBinOp (binOp, expr1, expr2)) = false
  | equal_expra (ExprBinOp (binOp, expr1, expr2)) (ExprEmpty chanRef) = false
  | equal_expra (ExprFull chanRef) (ExprBinOp (binOp, expr1, expr2)) = false
  | equal_expra (ExprBinOp (binOp, expr1, expr2)) (ExprFull chanRef) = false
  | equal_expra ExprTimeOut (ExprBinOp (binOp, expr1, expr2)) = false
  | equal_expra (ExprBinOp (binOp, expr1, expr2)) ExprTimeOut = false
  | equal_expra (ExprMConst (integer, literal))
    (ExprBinOp (binOp, expr1, expr2)) = false
  | equal_expra (ExprBinOp (binOp, expr1, expr2))
    (ExprMConst (integer, literal)) = false
  | equal_expra (ExprConst integer) (ExprBinOp (binOp, expr1, expr2)) = false
  | equal_expra (ExprBinOp (binOp, expr1, expr2)) (ExprConst integer) = false
  | equal_expra (ExprVarRef varRef) (ExprBinOp (binOp, expr1, expr2)) = false
  | equal_expra (ExprBinOp (binOp, expr1, expr2)) (ExprVarRef varRef) = false
  | equal_expra (ExprLen chanRef) (ExprBinOp (binOp, expr1, expr2)) = false
  | equal_expra (ExprBinOp (binOp, expr1, expr2)) (ExprLen chanRef) = false
  | equal_expra (ExprCond (expr1a, expr2a, expr3))
    (ExprBinOp (binOp, expr1, expr2)) = false
  | equal_expra (ExprBinOp (binOp, expr1a, expr2a))
    (ExprCond (expr1, expr2, expr3)) = false
  | equal_expra (ExprUnOp (unOp, expr)) (ExprBinOp (binOp, expr1, expr2)) =
    false
  | equal_expra (ExprBinOp (binOp, expr1, expr2)) (ExprUnOp (unOp, expr)) =
    false
  | equal_expra (ExprPoll (chanRefa, listaa, boolaa))
    (ExprPoll (chanRef, lista, boola)) =
    equal_chanRef chanRefa chanRef andalso
      (List.equal_lista (equal_recvArg ()) listaa lista andalso
        Product_Type.equal_bool boolaa boola)
  | equal_expra (ExprEmpty chanRefa) (ExprEmpty chanRef) =
    equal_chanRef chanRefa chanRef
  | equal_expra (ExprFull chanRefa) (ExprFull chanRef) =
    equal_chanRef chanRefa chanRef
  | equal_expra (ExprMConst (integera, literala))
    (ExprMConst (integer, literal)) =
    ((integera : IntInf.int) = integer) andalso ((literala : string) = literal)
  | equal_expra (ExprConst integera) (ExprConst integer) =
    ((integera : IntInf.int) = integer)
  | equal_expra (ExprVarRef varRefa) (ExprVarRef varRef) =
    equal_varRef varRefa varRef
  | equal_expra (ExprLen chanRefa) (ExprLen chanRef) =
    equal_chanRef chanRefa chanRef
  | equal_expra (ExprCond (expr1a, expr2a, expr3a))
    (ExprCond (expr1, expr2, expr3)) =
    equal_expra expr1a expr1 andalso
      (equal_expra expr2a expr2 andalso equal_expra expr3a expr3)
  | equal_expra (ExprUnOp (unOpa, expra)) (ExprUnOp (unOp, expr)) =
    equal_unOp unOpa unOp andalso equal_expra expra expr
  | equal_expra (ExprBinOp (binOpa, expr1a, expr2a))
    (ExprBinOp (binOp, expr1, expr2)) =
    equal_binOp binOpa binOp andalso
      (equal_expra expr1a expr1 andalso equal_expra expr2a expr2)
  | equal_expra ExprTimeOut ExprTimeOut = true;
val equal_expr = equal_expr ();
val equal_recvArg = equal_recvArg ();

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
    (List.rev (List.upt Arith.zero_nata (IArray.length es)));

fun gState2HASH (GState_ext (v, ch, t, p, m)) = (v, (ch, (t, (p, m))));

fun pState2HASH (PState_ext (p, v, c, ch, s, m)) = (p, (v, (c, (ch, (s, m)))));

fun printLabels f ls =
  ListMapImpl.iteratei_map_op_list_it_lm_ops ls (fn _ => true)
    (fn (k, l) =>
      (fn a =>
        ([#"L", #"a", #"b", #"e", #"l", #" "] @
          String.explode k @ [#":", #" "] @ f (Arith.integer_of_nat l)) ::
          a))
    [];

fun walk_iarraya uu uv x l uw =
  (if Arith.equal_nata l Arith.zero_nata then x
    else let
           val y = uu x (IArray.sub uv uw);
         in
           walk_iarraya uu uv y (Arith.minus_nat l Arith.one_nata)
             (Arith.plus_nata uw Arith.one_nata)
         end);

fun walk_iarray f a x = walk_iarraya f a x (IArray.length a) Arith.zero_nata;

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

fun equal_gState_ext A_ = {equal = equal_gState_exta A_} :
  'a gState_ext HOL.equal;

fun def_hashmap_size_uint_gState_ext A_ uu =
  Arith.nat_of_integer (10 : IntInf.int);

fun def_hashmap_size_gState_ext A_ = def_hashmap_size_uint_gState_ext A_;

fun def_hashmap_size_uint_pState_ext A_ uu =
  Arith.nat_of_integer (10 : IntInf.int);

fun def_hashmap_size_uint_assoc_list A_ B_ uu =
  Arith.nat_of_integer (10 : IntInf.int);

fun hashcode_uint_assoc_list A_ B_ =
  Collections_Patch1.hashcode_uint_list
    (Collections_Patch1.hashable_uint_prod A_ B_) o
    Assoc_List.impl_of;

fun hashable_uint_assoc_list A_ B_ =
  {hashcode_uint = hashcode_uint_assoc_list A_ B_,
    def_hashmap_size_uint = def_hashmap_size_uint_assoc_list A_ B_}
  : ('a, 'b) Assoc_List.assoc_list Collections_Patch1.hashable_uint;

fun def_hashmap_size_uint_variable uu = Arith.nat_of_integer (10 : IntInf.int);

fun def_hashmap_size_uint_varType uu = Arith.nat_of_integer (10 : IntInf.int);

fun hashcode_uint_varType (VTBounded (i1, i2)) =
  Collections_Patch1.hashcode_uint_prod Collections_Patch1.hashable_uint_integer
    Collections_Patch1.hashable_uint_integer (i1, i2)
  | hashcode_uint_varType VTChan = Word32.fromInt (23 : IntInf.int);

val hashable_uint_varType =
  {hashcode_uint = hashcode_uint_varType,
    def_hashmap_size_uint = def_hashmap_size_uint_varType}
  : varType Collections_Patch1.hashable_uint;

fun def_hashmap_size_uint_iarray A_ =
  (fn _ => Arith.nat_of_integer (10 : IntInf.int));

fun hashcode_uint_iarray A_ a =
  walk_iarray
    (fn h => fn v =>
      Word32.+ (Word32.* (h, Word32.fromInt
                               (33 : IntInf.int)), Collections_Patch1.hashcode_uint
             A_ v))
    a (Word32.fromInt 0);

fun hashable_uint_iarray A_ =
  {hashcode_uint = hashcode_uint_iarray A_,
    def_hashmap_size_uint = def_hashmap_size_uint_iarray A_}
  : ('a Vector.vector) Collections_Patch1.hashable_uint;

fun hashcode_uint_variable (Var (i1, i2)) =
  Collections_Patch1.hashcode_uint_prod hashable_uint_varType
    Collections_Patch1.hashable_uint_integer (i1, i2)
  | hashcode_uint_variable (VArray (i1, i2, ia)) =
    Collections_Patch1.hashcode_uint_prod hashable_uint_varType
      (Collections_Patch1.hashable_uint_prod
        Collections_Patch1.hashable_uint_nat
        (hashable_uint_iarray Collections_Patch1.hashable_uint_integer))
      (i1, (i2, ia));

val hashable_uint_variable =
  {hashcode_uint = hashcode_uint_variable,
    def_hashmap_size_uint = def_hashmap_size_uint_variable}
  : variable Collections_Patch1.hashable_uint;

fun hashcode_uint_pState_ext A_ =
  Collections_Patch1.hashcode_uint_prod Collections_Patch1.hashable_uint_nat
    (Collections_Patch1.hashable_uint_prod
      (hashable_uint_assoc_list Code_String.hashable_uint_literal
        hashable_uint_variable)
      (Collections_Patch1.hashable_uint_prod
        Collections_Patch1.hashable_uint_nat
        (Collections_Patch1.hashable_uint_prod
          (Collections_Patch1.hashable_uint_list
            Collections_Patch1.hashable_uint_integer)
          (Collections_Patch1.hashable_uint_prod
            Collections_Patch1.hashable_uint_nat A_)))) o
    pState2HASH;

fun hashable_uint_pState_ext A_ =
  {hashcode_uint = hashcode_uint_pState_ext A_,
    def_hashmap_size_uint = def_hashmap_size_uint_pState_ext A_}
  : 'a pState_ext Collections_Patch1.hashable_uint;

fun def_hashmap_size_uint_channel uu = Arith.nat_of_integer (10 : IntInf.int);

fun hashcode_uint_channel (Channel (io, vs, iss)) =
  Collections_Patch1.hashcode_uint_prod Collections_Patch1.hashable_uint_integer
    (Collections_Patch1.hashable_uint_prod
      (Collections_Patch1.hashable_uint_list hashable_uint_varType)
      (Collections_Patch1.hashable_uint_list
        (Collections_Patch1.hashable_uint_list
          Collections_Patch1.hashable_uint_integer)))
    (io, (vs, iss))
  | hashcode_uint_channel (HSChannel vs) =
    Word32.* (Word32.fromInt
                (42 : IntInf.int), Collections_Patch1.hashcode_uint_list
                                     hashable_uint_varType vs)
  | hashcode_uint_channel InvChannel = Word32.fromInt (4711 : IntInf.int);

val hashable_uint_channel =
  {hashcode_uint = hashcode_uint_channel,
    def_hashmap_size_uint = def_hashmap_size_uint_channel}
  : channel Collections_Patch1.hashable_uint;

fun hashcode_uint_gState_ext A_ =
  Collections_Patch1.hashcode_uint_prod
    (hashable_uint_assoc_list Code_String.hashable_uint_literal
      hashable_uint_variable)
    (Collections_Patch1.hashable_uint_prod
      (Collections_Patch1.hashable_uint_list hashable_uint_channel)
      (Collections_Patch1.hashable_uint_prod
        Collections_Patch1.hashable_uint_bool
        (Collections_Patch1.hashable_uint_prod
          (Collections_Patch1.hashable_uint_list
            (hashable_uint_pState_ext Collections_Patch1.hashable_uint_unit))
          A_))) o
    gState2HASH;

fun hashable_uint_gState_ext A_ =
  {hashcode_uint = hashcode_uint_gState_ext A_,
    def_hashmap_size_uint = def_hashmap_size_uint_gState_ext A_}
  : 'a gState_ext Collections_Patch1.hashable_uint;

fun bounded_hashcode_gState_ext A_ =
  Collections_Patch1.bounded_hashcode_nat (hashable_uint_gState_ext A_);

fun hashcode_gState_ext A_ =
  Collections_Patch1.hashcode_nat (hashable_uint_gState_ext A_);

fun hashable_gState_ext A_ =
  {hashcode = hashcode_gState_ext A_,
    bounded_hashcode = bounded_hashcode_gState_ext A_,
    def_hashmap_size = def_hashmap_size_gState_ext A_}
  : 'a gState_ext HashCode.hashable;

end; (*struct Promela*)

structure RBT_Impl : sig
  datatype color = R | B
  datatype compare = Lt | Gt | Eq
  datatype ('a, 'b) rbt = Empty |
    Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt
  val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) rbt -> 'c -> 'c
  val paint : color -> ('a, 'b) rbt -> ('a, 'b) rbt
  val balance : ('a, 'b) rbt -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val gen_entries :
    (('a * 'b) * ('a, 'b) rbt) list -> ('a, 'b) rbt -> ('a * 'b) list
  val entries : ('a, 'b) rbt -> ('a * 'b) list
  val rbt_ins :
    ('a -> 'a -> bool) ->
      ('a -> 'b -> 'b -> 'b) -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_insa :
    'a Orderings.ord ->
      ('a -> 'b -> 'b -> 'b) -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val skip_red : ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_insert_with_key :
    ('a -> 'a -> bool) ->
      ('a -> 'b -> 'b -> 'b) -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val skip_black : ('a, 'b) rbt -> ('a, 'b) rbt
  val compare_height :
    ('a, 'b) rbt -> ('a, 'b) rbt -> ('a, 'b) rbt -> ('a, 'b) rbt -> compare
  val sunion_with :
    ('a -> 'a -> bool) ->
      ('a -> 'b -> 'b -> 'b) ->
        ('a * 'b) list -> ('a * 'b) list -> ('a * 'b) list
  val rbtreeify_g : Arith.nat -> ('a * 'b) list -> ('a, 'b) rbt * ('a * 'b) list
  val rbtreeify_f : Arith.nat -> ('a * 'b) list -> ('a, 'b) rbt * ('a * 'b) list
  val rbtreeify : ('a * 'b) list -> ('a, 'b) rbt
  val rbt_union_with_key :
    ('a -> 'a -> bool) ->
      ('a -> 'b -> 'b -> 'b) -> ('a, 'b) rbt -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_union :
    ('a -> 'a -> bool) -> ('a, 'b) rbt -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_insert_with_keya :
    'a Orderings.ord ->
      ('a -> 'b -> 'b -> 'b) -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_insert : 'a Orderings.ord -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_lookup : ('a -> 'a -> bool) -> ('a, 'b) rbt -> 'a -> 'b option
  val rbt_inserta :
    ('a -> 'a -> bool) -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
end = struct

datatype color = R | B;

datatype compare = Lt | Gt | Eq;

datatype ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;

fun fold f (Branch (c, lt, k, v, rt)) x = fold f rt (f k v (fold f lt x))
  | fold f Empty x = x;

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

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

fun gen_entries kvts (Branch (c, l, k, v, r)) =
  gen_entries (((k, v), r) :: kvts) l
  | gen_entries ((kv, t) :: kvts) Empty = kv :: gen_entries kvts t
  | gen_entries [] Empty = [];

fun entries x = gen_entries [] x;

fun rbt_ins less f k v (Branch (R, l, x, y, r)) =
  (if less k x then Branch (R, rbt_ins less f k v l, x, y, r)
    else (if less x k then Branch (R, l, x, y, rbt_ins less f k v r)
           else Branch (R, l, x, f k y v, r)))
  | rbt_ins less f k v (Branch (B, l, x, y, r)) =
    (if less k x then balance (rbt_ins less f k v l) x y r
      else (if less x k then balance l x y (rbt_ins less f k v r)
             else Branch (B, l, x, f k y v, r)))
  | rbt_ins less f k v Empty = Branch (R, Empty, k, v, Empty);

fun rbt_insa A_ f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_insa A_ f k v (Branch (B, l, x, y, r)) =
    (if Orderings.less A_ k x then balance (rbt_insa A_ f k v l) x y r
      else (if Orderings.less A_ x k then balance l x y (rbt_insa A_ f k v r)
             else Branch (B, l, x, f k y v, r)))
  | rbt_insa A_ f k v (Branch (R, l, x, y, r)) =
    (if Orderings.less A_ k x then Branch (R, rbt_insa A_ f k v l, x, y, r)
      else (if Orderings.less A_ x k
             then Branch (R, l, x, y, rbt_insa A_ f k v r)
             else Branch (R, l, x, f k y v, r)));

fun skip_red (Branch (R, l, k, v, r)) = l
  | skip_red Empty = Empty
  | skip_red (Branch (B, va, vb, vc, vd)) = Branch (B, va, vb, vc, vd);

fun rbt_insert_with_key less f k v t = paint B (rbt_ins less f k v t);

fun skip_black t =
  let
    val ta = skip_red t;
  in
    (case ta of Empty => ta | Branch (R, l, _, _, _) => ta
      | Branch (B, l, _, _, _) => l)
  end;

fun compare_height sx s t tx =
  (case (skip_red sx, (skip_red s, (skip_red t, skip_red tx)))
    of (Empty, (Empty, (_, Empty))) => Eq
    | (Empty, (Empty, (_, Branch (_, _, _, _, _)))) => Lt
    | (Empty, (Branch (_, sa, _, _, _), (Empty, b))) => Eq
    | (Empty, (Branch (_, sa, _, _, _), (Branch (_, ta, _, _, _), Empty))) => Eq
    | (Empty,
        (Branch (_, sa, _, _, _),
          (Branch (_, ta, _, _, _), Branch (_, txa, _, _, _))))
      => compare_height Empty sa ta (skip_black txa)
    | (Branch (_, sxa, _, _, _), (Empty, (Empty, Empty))) => Gt
    | (Branch (_, sxa, _, _, _), (Empty, (Empty, Branch (_, _, _, _, _)))) => Lt
    | (Branch (_, sxa, _, _, _), (Empty, (Branch (_, _, _, _, _), Empty))) => Eq
    | (Branch (_, sxa, _, _, _),
        (Empty, (Branch (_, _, _, _, _), Branch (_, _, _, _, _))))
      => Lt
    | (Branch (_, sxa, _, _, _), (Branch (_, sa, _, _, _), (Empty, xf))) => Gt
    | (Branch (_, sxa, _, _, _),
        (Branch (_, sa, _, _, _), (Branch (_, ta, _, _, _), Empty)))
      => compare_height (skip_black sxa) sa ta Empty
    | (Branch (_, sxa, _, _, _),
        (Branch (_, sa, _, _, _),
          (Branch (_, ta, _, _, _), Branch (_, txa, _, _, _))))
      => compare_height (skip_black sxa) sa ta (skip_black txa));

fun sunion_with less f asa [] = asa
  | sunion_with less f [] bs = bs
  | sunion_with less f ((ka, va) :: asa) ((k, v) :: bs) =
    (if less k ka then (k, v) :: sunion_with less f ((ka, va) :: asa) bs
      else (if less ka k then (ka, va) :: sunion_with less f asa ((k, v) :: bs)
             else (ka, f ka va v) :: sunion_with less f asa bs));

fun rbtreeify_g n kvs =
  (if Arith.equal_nata n Arith.zero_nata orelse
        Arith.equal_nata n Arith.one_nata
    then (Empty, kvs)
    else let
           val (na, r) =
             Arith.divmod_nat n (Arith.nat_of_integer (2 : IntInf.int));
         in
           (if Arith.equal_nata r Arith.zero_nata
             then let
                    val (t1, (k, v) :: kvsa) = rbtreeify_g na kvs;
                  in
                    Product_Type.apfst (fn a => Branch (B, t1, k, v, a))
                      (rbtreeify_g na kvsa)
                  end
             else let
                    val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                  in
                    Product_Type.apfst (fn a => Branch (B, t1, k, v, a))
                      (rbtreeify_g na kvsa)
                  end)
         end)
and rbtreeify_f n kvs =
  (if Arith.equal_nata n Arith.zero_nata then (Empty, kvs)
    else (if Arith.equal_nata n Arith.one_nata
           then let
                  val (k, v) :: kvsa = kvs;
                in
                  (Branch (R, Empty, k, v, Empty), kvsa)
                end
           else let
                  val (na, r) =
                    Arith.divmod_nat n (Arith.nat_of_integer (2 : IntInf.int));
                in
                  (if Arith.equal_nata r Arith.zero_nata
                    then let
                           val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                         in
                           Product_Type.apfst (fn a => Branch (B, t1, k, v, a))
                             (rbtreeify_g na kvsa)
                         end
                    else let
                           val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                         in
                           Product_Type.apfst (fn a => Branch (B, t1, k, v, a))
                             (rbtreeify_f na kvsa)
                         end)
                end));

fun rbtreeify kvs =
  Product_Type.fst (rbtreeify_g (Arith.suc (List.size_list kvs)) kvs);

fun rbt_union_with_key less f t1 t2 =
  (case compare_height t1 t1 t2 t2
    of Lt =>
      fold (rbt_insert_with_key less (fn k => fn v => fn w => f k w v)) t1 t2
    | Gt => fold (rbt_insert_with_key less f) t2 t1
    | Eq => rbtreeify (sunion_with less f (entries t1) (entries t2)));

fun rbt_union less = rbt_union_with_key less (fn _ => fn _ => fn rv => rv);

fun rbt_insert_with_keya A_ f k v t = paint B (rbt_insa A_ f k v t);

fun rbt_insert A_ = rbt_insert_with_keya A_ (fn _ => fn _ => fn nv => nv);

fun rbt_lookup less (Branch (uu, l, x, y, r)) k =
  (if less k x then rbt_lookup less l k
    else (if less x k then rbt_lookup less r k else SOME y))
  | rbt_lookup less Empty k = NONE;

fun rbt_inserta less = rbt_insert_with_key less (fn _ => fn _ => fn nv => nv);

end; (*struct RBT_Impl*)

structure RBT_add : sig
  val rm_iterateoi :
    ('a, 'b) RBT_Impl.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

fun rm_iterateoi RBT_Impl.Empty c f sigma = sigma
  | rm_iterateoi (RBT_Impl.Branch (col, l, k, v, r)) c f sigma =
    (if c sigma
      then let
             val sigmaa = rm_iterateoi l c f sigma;
           in
             (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa) else sigmaa)
           end
      else sigma);

end; (*struct RBT_add*)

structure Char_ord : sig
  val ord_char : char Orderings.ord
  val preorder_char : char Orderings.preorder
  val order_char : char Orderings.order
  val linorder_char : char Orderings.linorder
end = struct

val ord_char =
  {less_eq = (fn a => fn b => ((a : char) <= b)),
    less = (fn a => fn b => ((a : char) < b))}
  : char Orderings.ord;

val preorder_char = {ord_preorder = ord_char} : char Orderings.preorder;

val order_char = {preorder_order = preorder_char} : char Orderings.order;

val linorder_char = {order_linorder = order_char} : char Orderings.linorder;

end; (*struct Char_ord*)

structure BoolProgs : sig
  datatype bexp = Tt | Ff | V of Arith.nat | Not of bexp | And of bexp * bexp |
    Or of bexp * bexp
  datatype com = Skip | Assign of Arith.nat list * bexp list | Seq of com * com
    | Gc of (bexp * com) list | IfTE of bexp * com * com | While of bexp * com
  datatype instr = AssI of Arith.nat list * bexp list |
    TestI of bexp * Arith.int | ChoiceI of (bexp * Arith.int) list |
    GotoI of Arith.int
  val opta : instr -> instr list -> instr list
  val opt : instr list -> instr list
  val bval : bexp -> IntInf.int -> bool
  val comp : com -> instr list
  val exec :
    instr FArray.IsabelleMapping.ArrayType ->
      IntInf.int -> Arith.nat -> Arith.nat list
  val execa : instr -> Arith.nat * IntInf.int -> (Arith.nat * IntInf.int) list
  val nexts1 :
    instr FArray.IsabelleMapping.ArrayType ->
      Arith.nat * IntInf.int -> (Arith.nat * IntInf.int) list
  val nexts :
    instr FArray.IsabelleMapping.ArrayType ->
      Arith.nat * IntInf.int -> (Arith.nat * IntInf.int) list
  val optcomp : com -> instr FArray.IsabelleMapping.ArrayType
  val print_config :
    (Arith.nat -> char list) ->
      (IntInf.int -> char list) -> Arith.nat * IntInf.int -> char list
end = struct

datatype bexp = Tt | Ff | V of Arith.nat | Not of bexp | And of bexp * bexp |
  Or of bexp * bexp;

datatype com = Skip | Assign of Arith.nat list * bexp list | Seq of com * com |
  Gc of (bexp * com) list | IfTE of bexp * com * com | While of bexp * com;

datatype instr = AssI of Arith.nat list * bexp list | TestI of bexp * Arith.int
  | ChoiceI of (bexp * Arith.int) list | GotoI of Arith.int;

fun opta (GotoI d) ys =
  let
    val next =
      (fn a =>
        (case a of AssI (_, _) => Arith.zero_int
          | TestI (_, _) => Arith.zero_int | ChoiceI _ => Arith.zero_int
          | GotoI da =>
            Arith.plus_int da (Arith.Int_of_integer (1 : IntInf.int))));
  in
    (if Arith.less_int d Arith.zero_int orelse
          Arith.less_eq_nat (List.size_list ys) (Arith.nat d)
      then GotoI d :: ys
      else let
             val da = Arith.plus_int d (next (List.nth ys (Arith.nat d)));
           in
             GotoI da :: ys
           end)
  end
  | opta (AssI (v, va)) ys = AssI (v, va) :: ys
  | opta (TestI (v, va)) ys = TestI (v, va) :: ys
  | opta (ChoiceI v) ys = ChoiceI v :: ys;

fun opt instr = List.foldr opta instr [];

fun bval Tt s = true
  | bval Ff s = false
  | bval (V n) s = Collections_Patch1.bs_mem n s
  | bval (Not b) s = not (bval b s)
  | bval (And (b_1, b_2)) s = bval b_1 s andalso bval b_2 s
  | bval (Or (b_1, b_2)) s = bval b_1 s orelse bval b_2 s;

fun comp Skip = []
  | comp (Assign (n, b)) = [AssI (n, b)]
  | comp (Seq (c1, c2)) = comp c1 @ comp c2
  | comp (Gc gcs) =
    let
      val cgcs = List.map (fn (b, c) => (b, comp c)) gcs;
      val addbc =
        (fn (b, cc) => fn (bis, ins) =>
          let
            val cca =
              cc @ (if List.null ins then []
                     else [GotoI (Arith.int_of_nat (List.size_list ins))]);
            val bisa =
              List.map
                (fn (ba, i) =>
                  (ba, Arith.plus_int i
                         (Arith.int_of_nat (List.size_list cca))))
                bis;
          in
            ((b, Arith.zero_int) :: bisa, cca @ ins)
          end);
      val (bis, a) = List.foldr addbc cgcs ([], []);
    in
      ChoiceI bis :: a
    end
  | comp (IfTE (b, c1, c2)) =
    let
      val ins1 = comp c1;
      val ins2 = comp c2;
      val i1 =
        Arith.int_of_nat (Arith.plus_nata (List.size_list ins1) Arith.one_nata);
      val i2 = Arith.int_of_nat (List.size_list ins2);
    in
      TestI (b, i1) :: ins1 @ GotoI i2 :: ins2
    end
  | comp (While (b, c)) =
    let
      val ins = comp c;
      val i =
        Arith.int_of_nat (Arith.plus_nata (List.size_list ins) Arith.one_nata);
    in
      TestI (b, i) ::
        ins @ [GotoI (Arith.uminus_int
                       (Arith.plus_int i
                         (Arith.Int_of_integer (1 : IntInf.int))))]
    end;

fun exec ins s pc =
  (if Arith.less_nat pc (Diff_Array.array_length ins)
    then (case Diff_Array.array_get ins pc of AssI (_, _) => [pc]
           | TestI (b, d) =>
             (if bval b s then exec ins s (Arith.plus_nata pc Arith.one_nata)
               else let
                      val pca =
                        Arith.nat
                          (Arith.plus_int
                            (Arith.int_of_nat
                              (Arith.plus_nata pc Arith.one_nata))
                            d);
                    in
                      (if Arith.less_nat pc pca then exec ins s pca else [pca])
                    end)
           | ChoiceI bis =>
             let
               val succs =
                 List.maps
                   (fn (b, i) =>
                     (if bval b s
                       then [Arith.nat
                               (Arith.plus_int
                                 (Arith.int_of_nat
                                   (Arith.plus_nata pc Arith.one_nata))
                                 i)]
                       else []))
                   bis;
             in
               (if List.null succs then [pc]
                 else List.maps
                        (fn pca =>
                          (if Arith.less_nat pc pca then exec ins s pca
                            else [pca]))
                        succs)
             end
           | GotoI d =>
             let
               val pca =
                 Arith.nat
                   (Arith.plus_int
                     (Arith.int_of_nat (Arith.plus_nata pc Arith.one_nata)) d);
             in
               (if Arith.less_nat pc pca then exec ins s pca else [pca])
             end)
    else [pc]);

fun execa instr (pc, s) =
  (case instr
    of AssI (ns, bs) =>
      let
        val bvs = List.zip ns (List.map (fn b => bval b s) bs);
      in
        [(Arith.plus_nata pc Arith.one_nata,
           List.foldl (fn sa => fn (a, b) => Bit_Int.set_bit_integer sa a b) s
             bvs)]
      end
    | TestI (b, d) =>
      [(if bval b s then (Arith.plus_nata pc Arith.one_nata, s)
         else (Arith.nat
                 (Arith.plus_int
                   (Arith.int_of_nat (Arith.plus_nata pc Arith.one_nata)) d),
                s))]
    | ChoiceI bis =>
      let
        val succs =
          List.maps
            (fn (b, i) =>
              (if bval b s
                then [(Arith.nat
                         (Arith.plus_int
                           (Arith.int_of_nat
                             (Arith.plus_nata pc Arith.one_nata))
                           i),
                        s)]
                else []))
            bis;
      in
        (if List.null succs then [(pc, s)] else succs)
      end
    | GotoI d =>
      [(Arith.nat
          (Arith.plus_int (Arith.int_of_nat (Arith.plus_nata pc Arith.one_nata))
            d),
         s)]);

fun nexts1 ins (pc, s) =
  (if Arith.less_nat pc (Diff_Array.array_length ins)
    then execa (Diff_Array.array_get ins pc) (pc, s) else [(pc, s)]);

fun nexts ins (pc, s) =
  List.maps (fn (pca, sa) => List.map (fn pcb => (pcb, sa)) (exec ins sa pca))
    (nexts1 ins (pc, s));

fun optcomp x = (FArray.IsabelleMapping.array_of_list o opt o comp) x;

fun print_config f fx (p, s) = f p @ [#" "] @ fx s;

end; (*struct BoolProgs*)

structure SetIteratorOperations : sig
  val set_iterator_image :
    ('a -> 'b) ->
      (('c -> bool) -> ('a -> 'c -> 'c) -> 'c -> 'c) ->
        ('c -> bool) -> ('b -> 'c -> 'c) -> 'c -> 'c
  val map_iterator_dom :
    (('a -> bool) -> ('b * 'c -> 'a -> 'a) -> 'a -> 'a) ->
      ('a -> bool) -> ('b -> 'a -> 'a) -> 'a -> 'a
end = struct

fun set_iterator_image g it = (fn c => fn f => it c (fn x => f (g x)));

fun map_iterator_dom it = set_iterator_image Product_Type.fst it;

end; (*struct SetIteratorOperations*)

structure Sorted_List_Operations : sig
  val memb_sorted : 'a HOL.equal * 'a Orderings.ord -> 'a list -> 'a -> bool
  val delete_sorted :
    'a HOL.equal * 'a Orderings.ord -> 'a -> 'a list -> 'a list
  val insertion_sort :
    'a HOL.equal * 'a Orderings.ord -> 'a -> 'a list -> 'a list
end = struct

fun memb_sorted (A1_, A2_) [] x = false
  | memb_sorted (A1_, A2_) (y :: xs) x =
    (if Orderings.less A2_ y x then memb_sorted (A1_, A2_) xs x
      else HOL.eq A1_ x y);

fun delete_sorted (A1_, A2_) x [] = []
  | delete_sorted (A1_, A2_) x (y :: xs) =
    (if Orderings.less A2_ y x then y :: delete_sorted (A1_, A2_) x xs
      else (if HOL.eq A1_ x y then xs else y :: xs));

fun insertion_sort (A1_, A2_) x [] = [x]
  | insertion_sort (A1_, A2_) x (y :: xs) =
    (if Orderings.less A2_ y x then y :: insertion_sort (A1_, A2_) x xs
      else (if HOL.eq A1_ x y then y :: xs else x :: y :: xs));

end; (*struct Sorted_List_Operations*)

structure ListSetImpl_Sorted : sig
  val lss_ins : 'a HOL.equal * 'a Orderings.linorder -> 'a -> 'a list -> 'a list
  val lss_memb : 'a HOL.equal * 'a Orderings.linorder -> 'a -> 'a list -> bool
  val lss_empty : unit -> 'a list
  val lss_union :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> 'a list
  val lss_delete :
    'a HOL.equal * 'a Orderings.linorder -> 'a -> 'a list -> 'a list
  val lss_ins_dj :
    'a HOL.equal * 'a Orderings.linorder -> 'a -> 'a list -> 'a list
  val lss_isEmpty : 'a list -> bool
  val lss_iteratei : 'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val lss_union_dj :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> 'a list
  val iteratei_bset_op_list_it_lss_basic_ops :
    'a Orderings.linorder ->
      'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val g_sel_lss_basic_ops :
    'a Orderings.linorder -> 'a list -> ('a -> bool) -> 'a option
  val g_ball_lss_basic_ops :
    'a Orderings.linorder -> 'a list -> ('a -> bool) -> bool
  val g_subset_lss_basic_ops :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> bool
  val g_equal_lss_basic_ops :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> bool
  val iteratei_set_op_list_it_lss_ops :
    'a Orderings.linorder ->
      'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
end = struct

fun lss_ins (A1_, A2_) x l =
  Sorted_List_Operations.insertion_sort
    (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
            Orderings.order_linorder)
            A2_)
    x l;

fun lss_memb (A1_, A2_) x l =
  Sorted_List_Operations.memb_sorted
    (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
            Orderings.order_linorder)
            A2_)
    l x;

fun lss_empty x = (fn _ => []) x;

fun lss_union (A1_, A2_) s1 s2 = Misc.merge (A1_, A2_) s1 s2;

fun lss_delete (A1_, A2_) x l =
  Sorted_List_Operations.delete_sorted
    (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
            Orderings.order_linorder)
            A2_)
    x l;

fun lss_ins_dj (A1_, A2_) = lss_ins (A1_, A2_);

fun lss_isEmpty s = List.null s;

fun lss_iteratei l = Foldi.foldli l;

fun lss_union_dj (A1_, A2_) = lss_union (A1_, A2_);

fun iteratei_bset_op_list_it_lss_basic_ops A_ s = lss_iteratei s;

fun g_sel_lss_basic_ops A_ s p =
  iteratei_bset_op_list_it_lss_basic_ops A_ s Option.is_none
    (fn x => fn _ => (if p x then SOME x else NONE)) NONE;

fun g_ball_lss_basic_ops A_ s p =
  iteratei_bset_op_list_it_lss_basic_ops A_ s (fn c => c) (fn x => fn _ => p x)
    true;

fun g_subset_lss_basic_ops (A1_, A2_) s1 s2 =
  g_ball_lss_basic_ops A2_ s1 (fn x => lss_memb (A1_, A2_) x s2);

fun g_equal_lss_basic_ops (A1_, A2_) s1 s2 =
  g_subset_lss_basic_ops (A1_, A2_) s1 s2 andalso
    g_subset_lss_basic_ops (A1_, A2_) s2 s1;

fun iteratei_set_op_list_it_lss_ops A_ s = lss_iteratei s;

end; (*struct ListSetImpl_Sorted*)

structure Proper_Iterator : sig
  val it_to_list :
    ('a -> ('b -> bool) -> ('c -> 'c list -> 'c list) -> 'd list -> 'e) ->
      'a -> 'e
end = struct

fun it_to_list it s = it s (fn _ => true) (fn x => fn l => l @ [x]) [];

end; (*struct Proper_Iterator*)

structure Impl_Array_Map : sig
  val iam_alpha :
    ('a option) FArray.IsabelleMapping.ArrayType -> Arith.nat -> 'a option
  val iam_empty : unit -> ('a option) FArray.IsabelleMapping.ArrayType
  val iam_increment : Arith.nat -> Arith.nat -> Arith.nat
  val iam_update :
    Arith.nat ->
      'a -> ('a option) FArray.IsabelleMapping.ArrayType ->
              ('a option) FArray.IsabelleMapping.ArrayType
end = struct

fun iam_alpha a i = Diff_Array.array_get_oo NONE a i;

fun iam_empty x = (fn _ => FArray.IsabelleMapping.array_of_list []) x;

fun iam_increment l idx =
  Orderings.max Arith.ord_nat
    (Arith.minus_nat (Arith.plus_nata idx Arith.one_nata) l)
    (Arith.plus_nata
      (Arith.times_nata (Arith.nat_of_integer (2 : IntInf.int)) l)
      (Arith.nat_of_integer (3 : IntInf.int)));

fun iam_update k v a =
  Diff_Array.array_set_oo
    (fn _ =>
      let
        val l = Diff_Array.array_length a;
      in
        Diff_Array.array_set (Diff_Array.array_grow a (iam_increment l k) NONE)
          k (SOME v)
      end)
    a k (SOME v);

end; (*struct Impl_Array_Map*)

structure Impl_List_Set : sig
  val rev_append : 'a list -> 'a list -> 'a list
  val glist_delete_aux :
    ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list -> 'a list
  val glist_delete : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
  val glist_member : ('a -> 'a -> bool) -> 'a -> 'a list -> bool
  val glist_insert : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
end = struct

fun rev_append [] ac = ac
  | rev_append (x :: xs) ac = rev_append xs (x :: ac);

fun glist_delete_aux eq x [] asa = asa
  | glist_delete_aux eq x (y :: ys) asa =
    (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y :: asa));

fun glist_delete eq x l = glist_delete_aux eq x l [];

fun glist_member eq x [] = false
  | glist_member eq x (y :: ys) = eq x y orelse glist_member eq x ys;

fun glist_insert eq x xs = (if glist_member eq x xs then xs else x :: xs);

end; (*struct Impl_List_Set*)

structure Gen_Map2Set : sig
  val map2set_memb : ('a -> 'b -> 'c option) -> 'a -> 'b -> bool
  val map2set_insert : ('a -> unit -> 'b -> 'c) -> 'a -> 'b -> 'c
end = struct

fun map2set_memb l k s = (case l k s of NONE => false | SOME _ => true);

fun map2set_insert i k s = i k () s;

end; (*struct Gen_Map2Set*)

structure LTL_to_GBA : sig
  val stat_set_data : Arith.nat -> Arith.nat -> Arith.nat -> unit
end = struct

fun stat_set_data ns ni na =
  Gerth_Statistics.set_data (Arith.integer_of_nat ns) (Arith.integer_of_nat ni)
    (Arith.integer_of_nat na);

end; (*struct LTL_to_GBA*)

structure Intf_Comp : sig
  datatype comp_res = Less | Equal | Greater
  val comp2eq : ('a -> 'b -> comp_res) -> 'a -> 'b -> bool
  val comp2lt : ('a -> 'b -> comp_res) -> 'a -> 'b -> bool
  val cmp_prod :
    ('a -> 'b -> comp_res) ->
      ('c -> 'd -> comp_res) -> 'a * 'c -> 'b * 'd -> comp_res
  val dflt_cmp :
    ('a -> 'b -> bool) -> ('a -> 'b -> bool) -> 'a -> 'b -> comp_res
end = struct

datatype comp_res = Less | Equal | Greater;

fun comp2eq cmp a b =
  (case cmp a b of Less => false | Equal => true | Greater => false);

fun comp2lt cmp a b =
  (case cmp a b of Less => true | Equal => false | Greater => false);

fun cmp_prod cmp1 cmp2 (a1, a2) (b1, b2) =
  (case cmp1 a1 b1 of Less => Less | Equal => cmp2 a2 b2 | Greater => Greater);

fun dflt_cmp le lt a b =
  (if lt a b then Less else (if le a b then Equal else Greater));

end; (*struct Intf_Comp*)

structure LTL_to_GBA_impl : sig
  val less_eq_ltln :
    'a HOL.equal * 'a Orderings.ord -> 'a LTL.ltln -> 'a LTL.ltln -> bool
  val less_ltln :
    'a HOL.equal * 'a Orderings.ord -> 'a LTL.ltln -> 'a LTL.ltln -> bool
  val ord_ltln : 'a HOL.equal * 'a Orderings.ord -> 'a LTL.ltln Orderings.ord
  datatype ('a, 'b) node_impl_ext =
    Node_impl_ext of
      Arith.nat * (Arith.nat, unit) RBT_Impl.rbt * 'a LTL.ltln list *
        'a LTL.ltln list * 'a LTL.ltln list * 'b
  val new_impl : ('a, 'b) node_impl_ext -> 'a LTL.ltln list
  val old_impl : ('a, 'b) node_impl_ext -> 'a LTL.ltln list
  val name_impl : ('a, 'b) node_impl_ext -> Arith.nat
  val next_impl : ('a, 'b) node_impl_ext -> 'a LTL.ltln list
  val preorder_ltln :
    'a HOL.equal * 'a Orderings.order -> 'a LTL.ltln Orderings.preorder
  val order_ltln :
    'a HOL.equal * 'a Orderings.order -> 'a LTL.ltln Orderings.order
  val incoming_impl_update :
    ((Arith.nat, unit) RBT_Impl.rbt -> (Arith.nat, unit) RBT_Impl.rbt) ->
      ('a, 'b) node_impl_ext -> ('a, 'b) node_impl_ext
  val incoming_impl : ('a, 'b) node_impl_ext -> (Arith.nat, unit) RBT_Impl.rbt
  val linorder_ltln :
    'a HOL.equal * 'a Orderings.linorder -> 'a LTL.ltln Orderings.linorder
  val upd_incoming_impl :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a, 'b) node_impl_ext ->
        ('a, 'c) node_impl_ext list -> ('a, 'c) node_impl_ext list
  val next_impl_update :
    ('a LTL.ltln list -> 'a LTL.ltln list) ->
      ('a, 'b) node_impl_ext -> ('a, 'b) node_impl_ext
  val name_impl_update :
    (Arith.nat -> Arith.nat) -> ('a, 'b) node_impl_ext -> ('a, 'b) node_impl_ext
  val old_impl_update :
    ('a LTL.ltln list -> 'a LTL.ltln list) ->
      ('a, 'b) node_impl_ext -> ('a, 'b) node_impl_ext
  val new_impl_update :
    ('a LTL.ltln list -> 'a LTL.ltln list) ->
      ('a, 'b) node_impl_ext -> ('a, 'b) node_impl_ext
  val expand_code_0 :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a, unit) node_impl_ext * ('a, unit) node_impl_ext list ->
        (Arith.nat * ('a, unit) node_impl_ext list) Refine_Det.dres
  val expand_code :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a, unit) node_impl_ext * ('a, unit) node_impl_ext list ->
        Arith.nat * ('a, unit) node_impl_ext list
  val pn_map_code :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a, 'b) node_impl_ext list ->
        (('a list * 'a list) option) FArray.IsabelleMapping.ArrayType
  val until_frmlsn_impl :
    'a HOL.equal * 'a Orderings.linorder ->
      'a LTL.ltln -> (('a LTL.ltln * 'a LTL.ltln), unit) RBT_Impl.rbt
  val build_F_impl :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a, 'b) node_impl_ext list -> 'a LTL.ltln -> (Arith.nat list) list
  val build_succ_code :
    'a Orderings.linorder ->
      ('a, 'b) node_impl_ext list ->
        ((Arith.nat list) option) FArray.IsabelleMapping.ArrayType
  val create_graph_code :
    'a HOL.equal * 'a Orderings.linorder ->
      'a LTL.ltln -> ('a, unit) node_impl_ext list
  val cr_rename_gba_code :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a, 'b) node_impl_ext list ->
        'a LTL.ltln ->
          ((Arith.nat list), (Arith.nat -> Arith.nat list), (Arith.nat list),
            (((Arith.nat list) list),
              ((Arith.nat -> ('a -> bool) -> bool), unit)
                Automata_Impl.gen_gba_impl_ext)
              Automata_Impl.gen_gbg_impl_ext)
            Digraph_Impl.gen_frg_impl_ext
  val create_name_gba_code :
    'a HOL.equal * 'a Orderings.linorder ->
      'a LTL.ltln ->
        ((Arith.nat list), (Arith.nat -> Arith.nat list), (Arith.nat list),
          (((Arith.nat list) list),
            ((Arith.nat -> ('a -> bool) -> bool), unit)
              Automata_Impl.gen_gba_impl_ext)
            Automata_Impl.gen_gbg_impl_ext)
          Digraph_Impl.gen_frg_impl_ext
  val create_name_igba_code :
    'a HOL.equal * 'a Orderings.linorder ->
      'a LTL.ltln ->
        ((Arith.nat list), (Arith.nat -> Arith.nat list), (Arith.nat list),
          ((Arith.nat -> IntInf.int),
            ((Arith.nat -> ('a -> bool) -> bool), unit)
              Automata_Impl.gen_igba_impl_ext)
            Automata_Impl.gen_igbg_impl_ext)
          Digraph_Impl.gen_frg_impl_ext
end = struct

fun less_eq_ltln (A1_, A2_) =
  (fn x => fn y =>
    LTL.ltln_rec
      (fn a =>
        (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => true
          | LTL.LTLnProp _ => true | LTL.LTLnNProp _ => true
          | LTL.LTLnAnd (_, _) => true | LTL.LTLnOr (_, _) => true
          | LTL.LTLnNext _ => true | LTL.LTLnUntil (_, _) => true
          | LTL.LTLnRelease (_, _) => true))
      (fn a =>
        (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
          | LTL.LTLnProp _ => true | LTL.LTLnNProp _ => true
          | LTL.LTLnAnd (_, _) => true | LTL.LTLnOr (_, _) => true
          | LTL.LTLnNext _ => true | LTL.LTLnUntil (_, _) => true
          | LTL.LTLnRelease (_, _) => true))
      (fn x_0 => fn a =>
        (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
          | LTL.LTLnProp aa => Orderings.less A2_ x_0 aa
          | LTL.LTLnNProp _ => true | LTL.LTLnAnd (_, _) => true
          | LTL.LTLnOr (_, _) => true | LTL.LTLnNext _ => true
          | LTL.LTLnUntil (_, _) => true | LTL.LTLnRelease (_, _) => true))
      (fn x_0 => fn a =>
        (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
          | LTL.LTLnProp _ => false
          | LTL.LTLnNProp aa => Orderings.less A2_ x_0 aa
          | LTL.LTLnAnd (_, _) => true | LTL.LTLnOr (_, _) => true
          | LTL.LTLnNext _ => true | LTL.LTLnUntil (_, _) => true
          | LTL.LTLnRelease (_, _) => true))
      (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
        (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
          | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
          | LTL.LTLnAnd (y_0, y_1) =>
            res_0 y_0 orelse LTL.equal_ltlna A1_ x_0 y_0 andalso res_1 y_1
          | LTL.LTLnOr (_, _) => true | LTL.LTLnNext _ => true
          | LTL.LTLnUntil (_, _) => true | LTL.LTLnRelease (_, _) => true))
      (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
        (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
          | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
          | LTL.LTLnAnd (_, _) => false
          | LTL.LTLnOr (y_0, y_1) =>
            res_0 y_0 orelse LTL.equal_ltlna A1_ x_0 y_0 andalso res_1 y_1
          | LTL.LTLnNext _ => true | LTL.LTLnUntil (_, _) => true
          | LTL.LTLnRelease (_, _) => true))
      (fn _ => fn res_0 => fn a =>
        (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
          | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
          | LTL.LTLnAnd (_, _) => false | LTL.LTLnOr (_, _) => false
          | LTL.LTLnNext aa => res_0 aa | LTL.LTLnUntil (_, _) => true
          | LTL.LTLnRelease (_, _) => true))
      (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
        (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
          | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
          | LTL.LTLnAnd (_, _) => false | LTL.LTLnOr (_, _) => false
          | LTL.LTLnNext _ => false
          | LTL.LTLnUntil (y_0, y_1) =>
            res_0 y_0 orelse LTL.equal_ltlna A1_ x_0 y_0 andalso res_1 y_1
          | LTL.LTLnRelease (_, _) => true))
      (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
        (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
          | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
          | LTL.LTLnAnd (_, _) => false | LTL.LTLnOr (_, _) => false
          | LTL.LTLnNext _ => false | LTL.LTLnUntil (_, _) => false
          | LTL.LTLnRelease (y_0, y_1) =>
            res_0 y_0 orelse LTL.equal_ltlna A1_ x_0 y_0 andalso res_1 y_1))
      x y orelse
      LTL.equal_ltlna A1_ x y);

fun less_ltln (A1_, A2_) =
  LTL.ltln_rec
    (fn a =>
      (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => true
        | LTL.LTLnProp _ => true | LTL.LTLnNProp _ => true
        | LTL.LTLnAnd (_, _) => true | LTL.LTLnOr (_, _) => true
        | LTL.LTLnNext _ => true | LTL.LTLnUntil (_, _) => true
        | LTL.LTLnRelease (_, _) => true))
    (fn a =>
      (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
        | LTL.LTLnProp _ => true | LTL.LTLnNProp _ => true
        | LTL.LTLnAnd (_, _) => true | LTL.LTLnOr (_, _) => true
        | LTL.LTLnNext _ => true | LTL.LTLnUntil (_, _) => true
        | LTL.LTLnRelease (_, _) => true))
    (fn x_0 => fn a =>
      (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
        | LTL.LTLnProp aa => Orderings.less A2_ x_0 aa | LTL.LTLnNProp _ => true
        | LTL.LTLnAnd (_, _) => true | LTL.LTLnOr (_, _) => true
        | LTL.LTLnNext _ => true | LTL.LTLnUntil (_, _) => true
        | LTL.LTLnRelease (_, _) => true))
    (fn x_0 => fn a =>
      (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
        | LTL.LTLnProp _ => false
        | LTL.LTLnNProp aa => Orderings.less A2_ x_0 aa
        | LTL.LTLnAnd (_, _) => true | LTL.LTLnOr (_, _) => true
        | LTL.LTLnNext _ => true | LTL.LTLnUntil (_, _) => true
        | LTL.LTLnRelease (_, _) => true))
    (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
      (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
        | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
        | LTL.LTLnAnd (y_0, y_1) =>
          res_0 y_0 orelse LTL.equal_ltlna A1_ x_0 y_0 andalso res_1 y_1
        | LTL.LTLnOr (_, _) => true | LTL.LTLnNext _ => true
        | LTL.LTLnUntil (_, _) => true | LTL.LTLnRelease (_, _) => true))
    (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
      (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
        | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
        | LTL.LTLnAnd (_, _) => false
        | LTL.LTLnOr (y_0, y_1) =>
          res_0 y_0 orelse LTL.equal_ltlna A1_ x_0 y_0 andalso res_1 y_1
        | LTL.LTLnNext _ => true | LTL.LTLnUntil (_, _) => true
        | LTL.LTLnRelease (_, _) => true))
    (fn _ => fn res_0 => fn a =>
      (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
        | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
        | LTL.LTLnAnd (_, _) => false | LTL.LTLnOr (_, _) => false
        | LTL.LTLnNext aa => res_0 aa | LTL.LTLnUntil (_, _) => true
        | LTL.LTLnRelease (_, _) => true))
    (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
      (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
        | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
        | LTL.LTLnAnd (_, _) => false | LTL.LTLnOr (_, _) => false
        | LTL.LTLnNext _ => false
        | LTL.LTLnUntil (y_0, y_1) =>
          res_0 y_0 orelse LTL.equal_ltlna A1_ x_0 y_0 andalso res_1 y_1
        | LTL.LTLnRelease (_, _) => true))
    (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
      (case a of LTL.LTLnTrue => false | LTL.LTLnFalse => false
        | LTL.LTLnProp _ => false | LTL.LTLnNProp _ => false
        | LTL.LTLnAnd (_, _) => false | LTL.LTLnOr (_, _) => false
        | LTL.LTLnNext _ => false | LTL.LTLnUntil (_, _) => false
        | LTL.LTLnRelease (y_0, y_1) =>
          res_0 y_0 orelse LTL.equal_ltlna A1_ x_0 y_0 andalso res_1 y_1));

fun ord_ltln (A1_, A2_) =
  {less_eq = less_eq_ltln (A1_, A2_), less = less_ltln (A1_, A2_)} :
  'a LTL.ltln Orderings.ord;

datatype ('a, 'b) node_impl_ext =
  Node_impl_ext of
    Arith.nat * (Arith.nat, unit) RBT_Impl.rbt * 'a LTL.ltln list *
      'a LTL.ltln list * 'a LTL.ltln list * 'b;

fun new_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = new_impl;

fun old_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = old_impl;

fun name_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = name_impl;

fun next_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = next_impl;

fun preorder_ltln (A1_, A2_) =
  {ord_preorder =
     ord_ltln (A1_, (Orderings.ord_preorder o Orderings.preorder_order) A2_)}
  : 'a LTL.ltln Orderings.preorder;

fun order_ltln (A1_, A2_) = {preorder_order = preorder_ltln (A1_, A2_)} :
  'a LTL.ltln Orderings.order;

fun incoming_impl_update incoming_impla
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = Node_impl_ext
      (name_impl, incoming_impla incoming_impl, new_impl, old_impl, next_impl,
        more);

fun incoming_impl
  (Node_impl_ext
    (name_impl, incoming_impl, new_impl, old_impl, next_impl, more))
  = incoming_impl;

fun linorder_ltln (A1_, A2_) =
  {order_linorder = order_ltln (A1_, Orderings.order_linorder A2_)} :
  'a LTL.ltln Orderings.linorder;

fun upd_incoming_impl (A1_, A2_) =
  (fn x =>
    List.map
      (fn xa =>
        (if ListSetImpl_Sorted.g_equal_lss_basic_ops
              (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_)) (old_impl xa)
              (old_impl x) andalso
              ListSetImpl_Sorted.g_equal_lss_basic_ops
                (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_)) (next_impl xa)
                (next_impl x)
          then incoming_impl_update
                 (fn _ =>
                   RBT_Impl.rbt_union Arith.less_nat (incoming_impl x)
                     (incoming_impl xa))
                 xa
          else xa)));

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

fun expand_code_0 (A1_, A2_) x =
  let
    val (a, b) = x;
  in
    (if ListSetImpl_Sorted.lss_isEmpty (new_impl a)
      then (if Gen_Set.gen_bex (fn xa => Foldi.foldli (Fun.id xa)) b
                 (fn xc =>
                   ListSetImpl_Sorted.g_equal_lss_basic_ops
                     (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                     (old_impl xc) (old_impl a) andalso
                     ListSetImpl_Sorted.g_equal_lss_basic_ops
                       (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                       (next_impl xc) (next_impl a))
             then Refine_Det.DRETURN
                    (name_impl a, upd_incoming_impl (A1_, A2_) a b)
             else expand_code_0 (A1_, A2_)
                    (Node_impl_ext
                       (Arith.suc (name_impl a),
                         Gen_Map2Set.map2set_insert
                           (RBT_Impl.rbt_insert Arith.ord_nat) (name_impl a)
                           RBT_Impl.Empty,
                         next_impl a, ListSetImpl_Sorted.lss_empty (),
                         ListSetImpl_Sorted.lss_empty (), ()),
                      a :: b))
      else Refine_Det.dbind
             (Refine_Det.DRETURN
               (Option.the
                 (ListSetImpl_Sorted.g_sel_lss_basic_ops
                   (linorder_ltln (A1_, A2_)) (new_impl a) (fn _ => true))))
             (fn xa =>
               let
                 val xb =
                   new_impl_update
                     (fn _ =>
                       ListSetImpl_Sorted.lss_delete
                         (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_)) xa
                         (new_impl a))
                     a;
               in
                 (case xa
                   of LTL.LTLnTrue =>
                     expand_code_0 (A1_, A2_)
                       (old_impl_update
                          (fn _ =>
                            ListSetImpl_Sorted.lss_union
                              (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                              (ListSetImpl_Sorted.lss_ins_dj
                                (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                xa (ListSetImpl_Sorted.lss_empty ()))
                              (old_impl xb))
                          xb,
                         b)
                   | LTL.LTLnFalse => Refine_Det.DRETURN (name_impl xb, b)
                   | LTL.LTLnProp aa =>
                     (if ListSetImpl_Sorted.lss_memb
                           (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                           (LTL.LTLnNProp aa) (old_impl xb)
                       then Refine_Det.DRETURN (name_impl xb, b)
                       else expand_code_0 (A1_, A2_)
                              (old_impl_update
                                 (fn _ =>
                                   ListSetImpl_Sorted.lss_union
                                     (LTL.equal_ltln A1_,
                                       linorder_ltln (A1_, A2_))
                                     (ListSetImpl_Sorted.lss_ins_dj
                                       (LTL.equal_ltln A1_,
 linorder_ltln (A1_, A2_))
                                       xa (ListSetImpl_Sorted.lss_empty ()))
                                     (old_impl xb))
                                 xb,
                                b))
                   | LTL.LTLnNProp aa =>
                     (if ListSetImpl_Sorted.lss_memb
                           (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                           (LTL.LTLnProp aa) (old_impl xb)
                       then Refine_Det.DRETURN (name_impl xb, b)
                       else expand_code_0 (A1_, A2_)
                              (old_impl_update
                                 (fn _ =>
                                   ListSetImpl_Sorted.lss_union
                                     (LTL.equal_ltln A1_,
                                       linorder_ltln (A1_, A2_))
                                     (ListSetImpl_Sorted.lss_ins_dj
                                       (LTL.equal_ltln A1_,
 linorder_ltln (A1_, A2_))
                                       xa (ListSetImpl_Sorted.lss_empty ()))
                                     (old_impl xb))
                                 xb,
                                b))
                   | LTL.LTLnAnd (ltln1, ltln2) =>
                     expand_code_0 (A1_, A2_)
                       (next_impl_update (fn _ => next_impl xb)
                          (old_impl_update
                            (fn _ =>
                              ListSetImpl_Sorted.lss_union
                                (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                (ListSetImpl_Sorted.lss_ins_dj
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  xa (ListSetImpl_Sorted.lss_empty ()))
                                (old_impl xb))
                            (new_impl_update
                              (fn _ =>
                                ListSetImpl_Sorted.lss_ins
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  ltln1
                                  (ListSetImpl_Sorted.lss_ins
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    ltln2 (new_impl xb)))
                              xb)),
                         b)
                   | LTL.LTLnOr (ltln1, ltln2) =>
                     Refine_Det.dbind
                       (expand_code_0 (A1_, A2_)
                         (next_impl_update
                            (fn _ =>
                              ListSetImpl_Sorted.lss_union_dj
                                (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                (ListSetImpl_Sorted.lss_empty ())
                                (next_impl xb))
                            (old_impl_update
                              (fn _ =>
                                ListSetImpl_Sorted.lss_ins
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  xa (old_impl xb))
                              (new_impl_update
                                (fn _ =>
                                  ListSetImpl_Sorted.lss_ins
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    ltln1 (new_impl xb))
                                xb)),
                           b))
                       (fn (aa, ba) =>
                         expand_code_0 (A1_, A2_)
                           (old_impl_update
                              (fn _ =>
                                ListSetImpl_Sorted.lss_union
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  (ListSetImpl_Sorted.lss_ins_dj
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    xa (ListSetImpl_Sorted.lss_empty ()))
                                  (old_impl xb))
                              (new_impl_update
                                (fn _ =>
                                  ListSetImpl_Sorted.lss_union
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    (ListSetImpl_Sorted.lss_ins_dj
                                      (LTL.equal_ltln A1_,
linorder_ltln (A1_, A2_))
                                      ltln2 (ListSetImpl_Sorted.lss_empty ()))
                                    (new_impl xb))
                                (name_impl_update (fn _ => aa) xb)),
                             ba))
                   | LTL.LTLnNext ltln =>
                     expand_code_0 (A1_, A2_)
                       (next_impl_update
                          (fn _ =>
                            ListSetImpl_Sorted.lss_ins
                              (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                              ltln (next_impl xb))
                          (old_impl_update
                            (fn _ =>
                              ListSetImpl_Sorted.lss_union
                                (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                (ListSetImpl_Sorted.lss_ins_dj
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  xa (ListSetImpl_Sorted.lss_empty ()))
                                (old_impl xb))
                            (new_impl_update (fn _ => new_impl xb) xb)),
                         b)
                   | LTL.LTLnUntil (ltln1, ltln2) =>
                     Refine_Det.dbind
                       (expand_code_0 (A1_, A2_)
                         (next_impl_update
                            (fn _ =>
                              ListSetImpl_Sorted.lss_union
                                (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                (ListSetImpl_Sorted.lss_ins_dj
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  xa (ListSetImpl_Sorted.lss_empty ()))
                                (next_impl xb))
                            (old_impl_update
                              (fn _ =>
                                ListSetImpl_Sorted.lss_ins
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  xa (old_impl xb))
                              (new_impl_update
                                (fn _ =>
                                  ListSetImpl_Sorted.lss_ins
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    ltln1 (new_impl xb))
                                xb)),
                           b))
                       (fn (aa, ba) =>
                         expand_code_0 (A1_, A2_)
                           (old_impl_update
                              (fn _ =>
                                ListSetImpl_Sorted.lss_union
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  (ListSetImpl_Sorted.lss_ins_dj
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    xa (ListSetImpl_Sorted.lss_empty ()))
                                  (old_impl xb))
                              (new_impl_update
                                (fn _ =>
                                  ListSetImpl_Sorted.lss_union
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    (ListSetImpl_Sorted.lss_ins_dj
                                      (LTL.equal_ltln A1_,
linorder_ltln (A1_, A2_))
                                      ltln2 (ListSetImpl_Sorted.lss_empty ()))
                                    (new_impl xb))
                                (name_impl_update (fn _ => aa) xb)),
                             ba))
                   | LTL.LTLnRelease (ltln1, ltln2) =>
                     Refine_Det.dbind
                       (expand_code_0 (A1_, A2_)
                         (next_impl_update
                            (fn _ =>
                              ListSetImpl_Sorted.lss_union
                                (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                (ListSetImpl_Sorted.lss_ins_dj
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  xa (ListSetImpl_Sorted.lss_empty ()))
                                (next_impl xb))
                            (old_impl_update
                              (fn _ =>
                                ListSetImpl_Sorted.lss_ins
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  xa (old_impl xb))
                              (new_impl_update
                                (fn _ =>
                                  ListSetImpl_Sorted.lss_ins
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    ltln2 (new_impl xb))
                                xb)),
                           b))
                       (fn (aa, ba) =>
                         expand_code_0 (A1_, A2_)
                           (old_impl_update
                              (fn _ =>
                                ListSetImpl_Sorted.lss_union
                                  (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                                  (ListSetImpl_Sorted.lss_ins_dj
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    xa (ListSetImpl_Sorted.lss_empty ()))
                                  (old_impl xb))
                              (new_impl_update
                                (fn _ =>
                                  ListSetImpl_Sorted.lss_union
                                    (LTL.equal_ltln A1_,
                                      linorder_ltln (A1_, A2_))
                                    (ListSetImpl_Sorted.lss_ins
                                      (LTL.equal_ltln A1_,
linorder_ltln (A1_, A2_))
                                      ltln1
                                      (ListSetImpl_Sorted.lss_ins_dj
(LTL.equal_ltln A1_, linorder_ltln (A1_, A2_)) ltln2
(ListSetImpl_Sorted.lss_empty ())))
                                    (new_impl xb))
                                (name_impl_update (fn _ => aa) xb)),
                             ba)))
               end))
  end;

fun expand_code (A1_, A2_) n_ns =
  Refine_Transfer.the_res (expand_code_0 (A1_, A2_) n_ns);

fun pn_map_code (A1_, A2_) x =
  Foldi.foldli x (fn _ => true)
    (fn xa => fn sigma =>
      let
        val xaa =
          ListSetImpl_Sorted.iteratei_set_op_list_it_lss_ops
            (linorder_ltln (A1_, A2_)) (old_impl xa) (fn _ => true)
            (fn xaa => fn (a, b) =>
              (case xaa of LTL.LTLnTrue => (a, b) | LTL.LTLnFalse => (a, b)
                | LTL.LTLnProp aa =>
                  (Impl_List_Set.glist_insert
                     (Intf_Comp.comp2eq
                       (Intf_Comp.dflt_cmp
                         (Orderings.less_eq
                           ((Orderings.ord_preorder o Orderings.preorder_order o
                              Orderings.order_linorder)
                             A2_))
                         (Orderings.less
                           ((Orderings.ord_preorder o Orderings.preorder_order o
                              Orderings.order_linorder)
                             A2_))))
                     aa a,
                    b)
                | LTL.LTLnNProp aa =>
                  (a, Impl_List_Set.glist_insert
                        (Intf_Comp.comp2eq
                          (Intf_Comp.dflt_cmp
                            (Orderings.less_eq
                              ((Orderings.ord_preorder o
                                 Orderings.preorder_order o
                                 Orderings.order_linorder)
                                A2_))
                            (Orderings.less
                              ((Orderings.ord_preorder o
                                 Orderings.preorder_order o
                                 Orderings.order_linorder)
                                A2_))))
                        aa b)
                | LTL.LTLnAnd (_, _) => (a, b) | LTL.LTLnOr (_, _) => (a, b)
                | LTL.LTLnNext _ => (a, b) | LTL.LTLnUntil (_, _) => (a, b)
                | LTL.LTLnRelease (_, _) => (a, b)))
            ([], []);
      in
        Impl_Array_Map.iam_update (name_impl xa) xaa sigma
      end)
    (Impl_Array_Map.iam_empty ());

fun until_frmlsn_impl (A1_, A2_) =
  LTL.ltln_rec RBT_Impl.Empty RBT_Impl.Empty (fn _ => RBT_Impl.Empty)
    (fn _ => RBT_Impl.Empty)
    (fn _ => fn _ =>
      RBT_Impl.rbt_union
        (Intf_Comp.comp2lt
          (Intf_Comp.cmp_prod
            (Intf_Comp.dflt_cmp
              (less_eq_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_))
              (less_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_)))
            (Intf_Comp.dflt_cmp
              (less_eq_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_))
              (less_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_))))))
    (fn _ => fn _ =>
      RBT_Impl.rbt_union
        (Intf_Comp.comp2lt
          (Intf_Comp.cmp_prod
            (Intf_Comp.dflt_cmp
              (less_eq_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_))
              (less_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_)))
            (Intf_Comp.dflt_cmp
              (less_eq_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_))
              (less_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_))))))
    (fn _ => fn xa => xa)
    (fn x => fn xa => fn xb => fn xc =>
      Gen_Map2Set.map2set_insert
        (RBT_Impl.rbt_inserta
          (Intf_Comp.comp2lt
            (Intf_Comp.cmp_prod
              (Intf_Comp.dflt_cmp
                (less_eq_ltln
                  (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                          Orderings.order_linorder)
                          A2_))
                (less_ltln
                  (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                          Orderings.order_linorder)
                          A2_)))
              (Intf_Comp.dflt_cmp
                (less_eq_ltln
                  (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                          Orderings.order_linorder)
                          A2_))
                (less_ltln
                  (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                          Orderings.order_linorder)
                          A2_))))))
        (x, xa)
        (RBT_Impl.rbt_union
          (Intf_Comp.comp2lt
            (Intf_Comp.cmp_prod
              (Intf_Comp.dflt_cmp
                (less_eq_ltln
                  (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                          Orderings.order_linorder)
                          A2_))
                (less_ltln
                  (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                          Orderings.order_linorder)
                          A2_)))
              (Intf_Comp.dflt_cmp
                (less_eq_ltln
                  (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                          Orderings.order_linorder)
                          A2_))
                (less_ltln
                  (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                          Orderings.order_linorder)
                          A2_)))))
          xb xc))
    (fn _ => fn _ =>
      RBT_Impl.rbt_union
        (Intf_Comp.comp2lt
          (Intf_Comp.cmp_prod
            (Intf_Comp.dflt_cmp
              (less_eq_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_))
              (less_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_)))
            (Intf_Comp.dflt_cmp
              (less_eq_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_))
              (less_ltln
                (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
                        Orderings.order_linorder)
                        A2_))))));

fun build_F_impl (A1_, A2_) =
  (fn x => fn xa =>
    Gen_Set.gen_image
      (fn xb =>
        Foldi.foldli
          (Proper_Iterator.it_to_list
            (SetIteratorOperations.map_iterator_dom o
              (Foldi.foldli o Proper_Iterator.it_to_list RBT_add.rm_iterateoi))
            xb))
      [] (Impl_List_Set.glist_insert
           (Gen_Set.gen_equal
             (Gen_Set.gen_subseteq
               (Gen_Set.gen_ball (fn xb => Foldi.foldli (Fun.id xb)))
               (Impl_List_Set.glist_member Arith.equal_nata))
             (Gen_Set.gen_subseteq
               (Gen_Set.gen_ball (fn xb => Foldi.foldli (Fun.id xb)))
               (Impl_List_Set.glist_member Arith.equal_nata))))
      (fn (xb, xc) =>
        Gen_Set.gen_image (fn xd => Foldi.foldli (Fun.id xd)) []
          (Impl_List_Set.glist_insert Arith.equal_nata) name_impl
          (List.filter
            (fn xd =>
              (if ListSetImpl_Sorted.lss_memb
                    (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_))
                    (LTL.LTLnUntil (xb, xc)) (old_impl xd)
                then ListSetImpl_Sorted.lss_memb
                       (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_)) xc
                       (old_impl xd)
                else true))
            x))
      (until_frmlsn_impl (A1_, A2_) xa));

fun build_succ_code A_ x =
  Foldi.foldli x (fn _ => true)
    (fn xa =>
      (SetIteratorOperations.map_iterator_dom o RBT_add.rm_iterateoi)
        (incoming_impl xa) (fn _ => true)
        (fn xaa => fn sigma =>
          (if Arith.equal_nata xaa Arith.zero_nata then sigma
            else Impl_Array_Map.iam_update xaa
                   (Impl_List_Set.glist_insert Arith.equal_nata (name_impl xa)
                     (Misc.the_default [] (Impl_Array_Map.iam_alpha sigma xaa)))
                   sigma)))
    (Impl_Array_Map.iam_empty ());

fun create_graph_code (A1_, A2_) phi =
  let
    val (_, b) =
      expand_code (A1_, A2_)
        (Node_impl_ext
           (Arith.suc Arith.zero_nata,
             Gen_Map2Set.map2set_insert (RBT_Impl.rbt_insert Arith.ord_nat)
               Arith.zero_nata RBT_Impl.Empty,
             ListSetImpl_Sorted.lss_ins_dj
               (LTL.equal_ltln A1_, linorder_ltln (A1_, A2_)) phi
               (ListSetImpl_Sorted.lss_empty ()),
             ListSetImpl_Sorted.lss_empty (), ListSetImpl_Sorted.lss_empty (),
             ()),
          []);
  in
    b
  end;

fun cr_rename_gba_code (A1_, A2_) x y =
  let
    val xa =
      Gen_Set.gen_image Foldi.foldli []
        (Impl_List_Set.glist_insert Arith.equal_nata) name_impl x;
    val xaa =
      Gen_Set.gen_image Foldi.foldli []
        (Impl_List_Set.glist_insert Arith.equal_nata) name_impl
        (List.filter
          (fn xc =>
            Gen_Map2Set.map2set_memb
              (fn k => fn t => RBT_Impl.rbt_lookup Arith.less_nat t k)
              Arith.zero_nata (incoming_impl xc))
          x);
    val xb = build_succ_code A2_ x;
    val xc = (fn xe => Misc.the_default [] (Impl_Array_Map.iam_alpha xb xe));
    val xd = build_F_impl (A1_, A2_) x y;
    val xe = pn_map_code (A1_, A2_) x;
    val xf =
      (fn xh => fn xi =>
        (case Impl_Array_Map.iam_alpha xe xh of NONE => false
          | SOME (xj, xk) =>
            Gen_Set.gen_ball Foldi.foldli xj xi andalso
              Gen_Set.gen_ball Foldi.foldli xk (fn xl => not (xi xl))));
  in
    Digraph_Impl.Gen_frg_impl_ext
      (xa, xc, xaa,
        Automata_Impl.Gen_gbg_impl_ext
          (xd, Automata_Impl.Gen_gba_impl_ext (xf, ())))
  end;

fun create_name_gba_code (A1_, A2_) phi =
  let
    val x = create_graph_code (A1_, A2_) phi;
  in
    cr_rename_gba_code (A1_, A2_) x phi
  end;

fun create_name_igba_code (A1_, A2_) phi =
  let
    val x = create_name_gba_code (A1_, A2_) phi;
    val xa =
      Automata_Impl.gba_to_idx_ext_code (HashCode.def_hashmap_size_nat HOL.Type)
        Arith.equal_nata HashCode.bounded_hashcode_nat (fn _ => ()) x;
    val _ =
      LTL_to_GBA.stat_set_data
        (Gen_Set.gen_card Arith.zero_nat Foldi.foldli (Digraph_Impl.frgi_V x))
        (Gen_Set.gen_card Arith.zero_nat Foldi.foldli (Digraph_Impl.frgi_V0 xa))
        (Automata_Impl.igbgi_num_acc xa);
  in
    xa
  end;

end; (*struct LTL_to_GBA_impl*)

structure Impl_Array_Stack : sig
  val as_get :
    'a FArray.IsabelleMapping.ArrayType * Arith.nat -> Arith.nat -> 'a
  val as_shrink :
    'a FArray.IsabelleMapping.ArrayType * Arith.nat ->
      'a FArray.IsabelleMapping.ArrayType * Arith.nat
  val as_pop :
    'a FArray.IsabelleMapping.ArrayType * Arith.nat ->
      'a FArray.IsabelleMapping.ArrayType * Arith.nat
  val as_set :
    'a FArray.IsabelleMapping.ArrayType * Arith.nat ->
      Arith.nat -> 'a -> 'a FArray.IsabelleMapping.ArrayType * Arith.nat
  val as_top : 'a FArray.IsabelleMapping.ArrayType * Arith.nat -> 'a
  val as_push :
    'a FArray.IsabelleMapping.ArrayType * Arith.nat ->
      'a -> 'a FArray.IsabelleMapping.ArrayType * Arith.nat
  val as_take :
    Arith.nat ->
      'a FArray.IsabelleMapping.ArrayType * Arith.nat ->
        'a FArray.IsabelleMapping.ArrayType * Arith.nat
  val as_empty :
    'b Arith.zero -> unit -> 'a FArray.IsabelleMapping.ArrayType * 'b
  val as_length : 'a FArray.IsabelleMapping.ArrayType * Arith.nat -> Arith.nat
  val as_is_empty : 'a FArray.IsabelleMapping.ArrayType * Arith.nat -> bool
  val as_singleton :
    'b Arith.one -> 'a -> 'a FArray.IsabelleMapping.ArrayType * 'b
end = struct

fun as_get s i = let
                   val (a, _) = s;
                 in
                   Diff_Array.array_get a i
                 end;

fun as_shrink s =
  let
    val (a, n) = s;
    val aa =
      (if Arith.less_eq_nat
            (Arith.times_nata (Arith.nat_of_integer (128 : IntInf.int)) n)
            (Diff_Array.array_length a) andalso
            Arith.less_nat (Arith.nat_of_integer (4 : IntInf.int)) n
        then Diff_Array.array_shrink a n else a);
  in
    (aa, n)
  end;

fun as_pop s =
  let
    val (a, n) = s;
  in
    as_shrink (a, Arith.minus_nat n Arith.one_nata)
  end;

fun as_set s i x = let
                     val (a, b) = s;
                   in
                     (Diff_Array.array_set a i x, b)
                   end;

fun as_top s =
  let
    val (a, n) = s;
  in
    Diff_Array.array_get a (Arith.minus_nat n Arith.one_nata)
  end;

fun as_push s x =
  let
    val (a, n) = s;
    val aa =
      (if Arith.equal_nata n (Diff_Array.array_length a)
        then Diff_Array.array_grow a
               (Orderings.max Arith.ord_nat
                 (Arith.nat_of_integer (4 : IntInf.int))
                 (Arith.times_nata (Arith.nat_of_integer (2 : IntInf.int)) n))
               x
        else a);
    val ab = Diff_Array.array_set aa n x;
  in
    (ab, Arith.plus_nata n Arith.one_nata)
  end;

fun as_take m s =
  let
    val (a, n) = s;
  in
    (if Arith.less_nat m n then as_shrink (a, m) else (a, n))
  end;

fun as_empty B_ uu = (FArray.IsabelleMapping.array_of_list [], Arith.zero B_);

fun as_length x = Product_Type.snd x;

fun as_is_empty s = Arith.equal_nata (Product_Type.snd s) Arith.zero_nata;

fun as_singleton B_ x =
  (FArray.IsabelleMapping.array_of_list [x], Arith.one B_);

end; (*struct Impl_Array_Stack*)

structure Gabow_Skeleton : sig
  val find_max_nat : Arith.nat -> (Arith.nat -> bool) -> Arith.nat
end = struct

fun find_max_nat n uu =
  (if Arith.equal_nata n Arith.zero_nata then Arith.zero_nata
    else (if uu (Arith.minus_nat n Arith.one_nata)
           then Arith.minus_nat n Arith.one_nata
           else find_max_nat (Arith.minus_nat n Arith.one_nata) uu));

end; (*struct Gabow_Skeleton*)

structure Gabow_Skeleton_Code : sig
  val pop_tr :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a FArray.IsabelleMapping.ArrayType * Arith.nat) *
        ((Arith.nat FArray.IsabelleMapping.ArrayType * Arith.nat) *
          (('a, Arith.int) Impl_Array_Hash_Map.hashmap *
            ((Arith.nat * 'a list) FArray.IsabelleMapping.ArrayType *
              Arith.nat))) ->
        ('a FArray.IsabelleMapping.ArrayType * Arith.nat) *
          ((Arith.nat FArray.IsabelleMapping.ArrayType * Arith.nat) *
            (('a, Arith.int) Impl_Array_Hash_Map.hashmap *
              ((Arith.nat * 'a list) FArray.IsabelleMapping.ArrayType *
                Arith.nat)))
  val idx_of_tr :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a FArray.IsabelleMapping.ArrayType * Arith.nat) *
              ((Arith.nat FArray.IsabelleMapping.ArrayType * Arith.nat) *
                (('a, Arith.int) Impl_Array_Hash_Map.hashmap *
                  ((Arith.nat * 'a list) FArray.IsabelleMapping.ArrayType *
                    Arith.nat))) ->
              Arith.nat
  val push_code :
    'a HOL.equal * 'a HashCode.hashable ->
      (('a -> bool), ('a -> 'a list), ('a list), 'b)
        Digraph_Impl.gen_frg_impl_ext ->
        'a -> ('a FArray.IsabelleMapping.ArrayType * Arith.nat) *
                ((Arith.nat FArray.IsabelleMapping.ArrayType * Arith.nat) *
                  (('a, Arith.int) Impl_Array_Hash_Map.hashmap *
                    ((Arith.nat * 'a list) FArray.IsabelleMapping.ArrayType *
                      Arith.nat))) ->
                ('a FArray.IsabelleMapping.ArrayType * Arith.nat) *
                  ((Arith.nat FArray.IsabelleMapping.ArrayType * Arith.nat) *
                    (('a, Arith.int) Impl_Array_Hash_Map.hashmap *
                      ((Arith.nat * 'a list) FArray.IsabelleMapping.ArrayType *
                        Arith.nat)))
  val select_edge_tr :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a FArray.IsabelleMapping.ArrayType * Arith.nat) *
        ((Arith.nat FArray.IsabelleMapping.ArrayType * Arith.nat) *
          (('a, Arith.int) Impl_Array_Hash_Map.hashmap *
            ((Arith.nat * 'a list) FArray.IsabelleMapping.ArrayType *
              Arith.nat))) ->
        'a option *
          (('a FArray.IsabelleMapping.ArrayType * Arith.nat) *
            ((Arith.nat FArray.IsabelleMapping.ArrayType * Arith.nat) *
              (('a, Arith.int) Impl_Array_Hash_Map.hashmap *
                ((Arith.nat * 'a list) FArray.IsabelleMapping.ArrayType *
                  Arith.nat))))
end = struct

fun pop_tr (A1_, A2_) s =
  let
    val (a, (aa, (ab, bb))) = s;
    val x = Arith.minus_nat (Impl_Array_Stack.as_length aa) Arith.one_nata;
    val xa =
      let
        val (_, bc) =
          While_Combinator.whilea
            (fn (xf, _) =>
              Arith.less_nat xf
                (if Arith.equal_nata (Arith.plus_nata x Arith.one_nata)
                      (Impl_Array_Stack.as_length aa)
                  then Impl_Array_Stack.as_length a
                  else Impl_Array_Stack.as_get aa
                         (Arith.plus_nata x Arith.one_nata)))
            (fn (ac, bc) =>
              (Arith.suc ac,
                Impl_Array_Hash_Map.ahm_update (HOL.eq A1_)
                  (HashCode.bounded_hashcode A2_) (Impl_Array_Stack.as_get a ac)
                  (Arith.Int_of_integer (~1 : IntInf.int)) bc))
            (Impl_Array_Stack.as_get aa x, ab);
      in
        bc
      end;
    val xb = Impl_Array_Stack.as_take (Impl_Array_Stack.as_top aa) a;
    val xc = Impl_Array_Stack.as_pop aa;
  in
    (xb, (xc, (xa, bb)))
  end;

fun idx_of_tr (A1_, A2_) s v =
  let
    val (_, (aa, (ab, _))) = v;
    val x =
      let
        val SOME i =
          Impl_Array_Hash_Map.ahm_lookup (HOL.eq A1_)
            (HashCode.bounded_hashcode A2_) s ab;
        val true = Arith.less_eq_int Arith.zero_int i;
      in
        Arith.nat i
      end;
    val xa =
      Gabow_Skeleton.find_max_nat (Impl_Array_Stack.as_length aa)
        (fn j => Arith.less_eq_nat (Impl_Array_Stack.as_get aa j) x);
  in
    xa
  end;

fun push_code (A1_, A2_) g_impl =
  (fn x => fn (xa, (xb, (xc, xd))) =>
    let
      val _ = Gabow_Skeleton_Statistics.newnode ();
      val xf = Impl_Array_Stack.as_length xa;
      val xg = Impl_Array_Stack.as_push xa x;
      val xh = Impl_Array_Stack.as_push xb xf;
      val xi =
        Impl_Array_Hash_Map.ahm_update (HOL.eq A1_)
          (HashCode.bounded_hashcode A2_) x (Arith.int_of_nat xf) xc;
      val xj =
        (if Autoref_Bindings_HOL.is_Nil (Digraph_Impl.frgi_E g_impl x) then xd
          else Impl_Array_Stack.as_push xd (xf, Digraph_Impl.frgi_E g_impl x));
    in
      (xg, (xh, (xi, xj)))
    end);

fun select_edge_tr (A1_, A2_) s =
  let
    val (a, (aa, (ab, bb))) = s;
  in
    (if Impl_Array_Stack.as_is_empty bb then (NONE, (a, (aa, (ab, bb))))
      else let
             val (ac, bc) = Impl_Array_Stack.as_top bb;
           in
             (if Arith.less_eq_nat
                   (Impl_Array_Stack.as_get aa
                     (Arith.minus_nat (Impl_Array_Stack.as_length aa)
                       Arith.one_nata))
                   ac
               then let
                      val xa =
                        Gen_Set.gen_pick (fn x => Foldi.foldli (Fun.id x)) bc;
                      val xb = Impl_List_Set.glist_delete (HOL.eq A1_) xa bc;
                      val xc =
                        (if Autoref_Bindings_HOL.is_Nil xb
                          then Impl_Array_Stack.as_pop bb
                          else Impl_Array_Stack.as_set bb
                                 (Arith.minus_nat
                                   (Impl_Array_Stack.as_length bb)
                                   Arith.one_nata)
                                 (ac, xb));
                    in
                      (SOME xa, (a, (aa, (ab, xc))))
                    end
               else (NONE, (a, (aa, (ab, bb)))))
           end)
  end;

end; (*struct Gabow_Skeleton_Code*)

structure Collections_Patch2 : sig
  val atLeastLessThan_tr :
    'a -> (Arith.nat -> 'a -> 'a) -> Arith.nat -> Arith.nat -> 'a
end = struct

fun atLeastLessThan_tr emp ins a b =
  let
    val (_, ba) =
      While_Combinator.whilea (fn (xc, _) => Arith.less_nat xc b)
        (fn (aa, ba) => (Arith.plus_nata aa Arith.one_nata, ins aa ba))
        (a, emp);
  in
    ba
  end;

end; (*struct Collections_Patch2*)

structure Find_Path_Impl : sig
  val wset_find_path_code :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a -> 'a list) -> 'a list -> ('a -> bool) -> ('a list * 'a) option
  val find_path1_code :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a -> 'a list) -> 'a -> ('a -> bool) -> ('a list * 'a) option
end = struct

fun wset_find_path_code (A1_, A2_) e u0 p =
  let
    val x =
      let
        val (a, b) =
          Foldi.foldli u0 (fn _ => true)
            (fn x => fn (a, b) =>
              (Gen_Map2Set.map2set_insert
                 (Impl_Array_Hash_Map.ahm_update (HOL.eq A1_)
                   (HashCode.bounded_hashcode A2_))
                 x a,
                Impl_List_Map.list_map_update (HOL.eq A1_) x [] b))
            (Impl_Array_Hash_Map.ahm_empty
               (HashCode.def_hashmap_size A2_ HOL.Type),
              []);
      in
        (NONE, (a, b))
      end;
    val (a, (_, _)) =
      While_Combinator.whilea
        (fn (xb, (_, xd)) =>
          Autoref_Bindings_HOL.is_None xb andalso
            not (Impl_List_Map.list_map_isEmpty xd))
        (fn (_, (aa, ba)) =>
          let
            val ((ac, bc), bb) = Impl_List_Map.list_map_pick_remove ba;
          in
            (if p ac then (SOME (List.rev bc, ac), (aa, bb))
              else let
                     val (ad, bd) =
                       Foldi.foldli (List.rev (e ac)) (fn _ => true)
                         (fn xc => fn (ad, bd) =>
                           (if Gen_Map2Set.map2set_memb
                                 (Impl_Array_Hash_Map.ahm_lookup (HOL.eq A1_)
                                   (HashCode.bounded_hashcode A2_))
                                 xc ad
                             then (ad, bd)
                             else (Gen_Map2Set.map2set_insert
                                     (Impl_Array_Hash_Map.ahm_update
                                       (HOL.eq A1_)
                                       (HashCode.bounded_hashcode A2_))
                                     xc ad,
                                    (xc, ac :: bc) :: bd)))
                         (aa, bb);
                   in
                     (NONE, (ad, bd))
                   end)
          end)
        x;
  in
    a
  end;

fun find_path1_code (A1_, A2_) e u p =
  (case wset_find_path_code (A1_, A2_) e (e u) p of NONE => NONE
    | SOME (a, b) => SOME (u :: a, b));

end; (*struct Find_Path_Impl*)

structure Gabow_GBG : sig
  val un_set_drop_tr :
    'a -> ('a -> 'a -> 'a) ->
            Arith.nat -> 'a FArray.IsabelleMapping.ArrayType * Arith.nat -> 'a
end = struct

fun un_set_drop_tr es_impl un_impl i a =
  let
    val (_, b) =
      While_Combinator.whilea
        (fn (xc, _) => Arith.less_nat xc (Impl_Array_Stack.as_length a))
        (fn (aa, b) =>
          let
            val xa = un_impl (Impl_Array_Stack.as_get a aa) b;
            val xb = Arith.plus_nata aa Arith.one_nata;
          in
            (xb, xa)
          end)
        (i, es_impl);
  in
    b
  end;

end; (*struct Gabow_GBG*)

structure Gabow_GBG_Code : sig
  val go_is_no_brk_code :
    'a HashCode.hashable ->
      (('a -> bool) * ('a -> bool)) option *
        ('a, Arith.int) Impl_Array_Hash_Map.hashmap ->
        bool
  val go_is_done_code :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> (('a -> bool) * ('a -> bool)) option *
              ('a, Arith.int) Impl_Array_Hash_Map.hashmap ->
              bool
  val gto_outer_code :
    'a HashCode.hashable ->
      (('a -> bool) * ('a -> bool)) option ->
        (IntInf.int FArray.IsabelleMapping.ArrayType * Arith.nat) *
          (('a FArray.IsabelleMapping.ArrayType * Arith.nat) *
            ((Arith.nat FArray.IsabelleMapping.ArrayType * Arith.nat) *
              (('a, Arith.int) Impl_Array_Hash_Map.hashmap *
                ((Arith.nat * 'a list) FArray.IsabelleMapping.ArrayType *
                  Arith.nat)))) ->
          (('a -> bool) * ('a -> bool)) option *
            ('a, Arith.int) Impl_Array_Hash_Map.hashmap
  val goinitial_code :
    'a HashCode.hashable ->
      (('a -> bool) * ('a -> bool)) option *
        ('a, Arith.int) Impl_Array_Hash_Map.hashmap
  val goBrk_code :
    'a HashCode.hashable ->
      (('a -> bool) * ('a -> bool)) option *
        ('a, Arith.int) Impl_Array_Hash_Map.hashmap ->
        (('a -> bool) * ('a -> bool)) option
  val find_ce_tr :
    'a HOL.equal * 'a HashCode.hashable ->
      (('a -> bool), ('a -> 'a list), ('a list),
        (('a -> IntInf.int), 'b) Automata_Impl.gen_igbg_impl_ext)
        Digraph_Impl.gen_frg_impl_ext ->
        (('a -> bool) * ('a -> bool)) option
  val reconstruct_lasso_tr :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a -> bool) ->
        ('a -> bool) ->
          (('a -> bool), ('a -> 'a list), ('a list),
            (('a -> IntInf.int), 'b) Automata_Impl.gen_igbg_impl_ext)
            Digraph_Impl.gen_frg_impl_ext ->
            'a list * 'a list
  val find_lasso_tr :
    'a HOL.equal * 'a HashCode.hashable ->
      (('a -> bool), ('a -> 'a list), ('a list),
        (('a -> IntInf.int), 'b) Automata_Impl.gen_igbg_impl_ext)
        Digraph_Impl.gen_frg_impl_ext ->
        ('a list * 'a list) option
end = struct

fun go_is_no_brk_code A_ =
  (fn x => Autoref_Bindings_HOL.is_None (Product_Type.fst x));

fun go_is_done_code (A1_, A2_) =
  (fn x => fn xa =>
    (case Impl_Array_Hash_Map.ahm_lookup (HOL.eq A1_)
            (HashCode.bounded_hashcode A2_) x (Product_Type.snd xa)
      of NONE => false
      | SOME i =>
        (if Arith.less_eq_int Arith.zero_int i then false else true)));

fun gto_outer_code A_ = (fn x => fn (_, (_, (_, (xe, _)))) => (x, xe));

fun goinitial_code A_ =
  (NONE, Impl_Array_Hash_Map.ahm_empty (HashCode.def_hashmap_size A_ HOL.Type));

fun goBrk_code A_ = Product_Type.fst;

fun find_ce_tr (A1_, A2_) g_impl =
  let
    val _ = Gabow_Skeleton_Statistics.start ();
    val xa = goinitial_code A2_;
    val xb =
      Foldi.foldli (Fun.id (Digraph_Impl.frgi_V0 g_impl))
        (go_is_no_brk_code A2_)
        (fn xb => fn sigma =>
          (if not (go_is_done_code (A1_, A2_) xb sigma)
            then let
                   val xc =
                     (NONE,
                       (Impl_Array_Stack.as_singleton Arith.one_nat
                          (Automata_Impl.igbgi_acc g_impl xb),
                         (Impl_Array_Stack.as_singleton Arith.one_nat xb,
                           (Impl_Array_Stack.as_singleton Arith.one_nat
                              Arith.zero_nata,
                             (Impl_Array_Hash_Map.ahm_update (HOL.eq A1_)
                                (HashCode.bounded_hashcode A2_) xb
                                (Arith.int_of_nat Arith.zero_nata)
                                (Product_Type.snd sigma),
                               (if Autoref_Bindings_HOL.is_Nil
                                     (Digraph_Impl.frgi_E g_impl xb)
                                 then Impl_Array_Stack.as_empty Arith.zero_nat
()
                                 else Impl_Array_Stack.as_singleton
Arith.one_nat (Arith.zero_nata, Digraph_Impl.frgi_E g_impl xb)))))));
                   val (a, b) =
                     While_Combinator.whilea
                       (fn (xf, xg) =>
                         Autoref_Bindings_HOL.is_None xf andalso
                           not (Impl_Array_Stack.as_is_empty
                                 let
                                   val (xaa, (_, (_, _))) = Product_Type.snd xg;
                                 in
                                   xaa
                                 end))
                       (fn (_, b) =>
                         (case let
                                 val (aa, ba) = b;
                                 val (ab, bb) =
                                   Gabow_Skeleton_Code.select_edge_tr (A1_, A2_)
                                     ba;
                               in
                                 (ab, (aa, bb))
                               end
                           of (NONE, ba) =>
                             let
                               val a =
                                 let
                                   val (ab, bb) = ba;
                                   val xg =
                                     Gabow_Skeleton_Code.pop_tr (A1_, A2_) bb;
                                   val xh = Impl_Array_Stack.as_pop ab;
                                 in
                                   (xh, xg)
                                 end;
                             in
                               (NONE, a)
                             end
                           | (SOME xf, ba) =>
                             (if (case Impl_Array_Hash_Map.ahm_lookup
 (HOL.eq A1_) (HashCode.bounded_hashcode A2_) xf
 let
   val (_, (_, (xd, _))) = Product_Type.snd ba;
 in
   xd
 end
                                   of NONE => false
                                   | SOME i =>
                                     (if Arith.less_eq_int Arith.zero_int i
                                       then true else false))
                               then let
                                      val xg =
let
  val (ab, (ac, (ad, (ae, be)))) = ba;
  val xh = Gabow_Skeleton_Code.idx_of_tr (A1_, A2_) xf (ac, (ad, (ae, be)));
  val xi = Impl_Array_Stack.as_take (Arith.plus_nata xh Arith.one_nata) ad;
  val xj =
    Gabow_GBG.un_set_drop_tr (Collections_Patch1.bs_empty ())
      Collections_Patch1.bs_union xh ab;
  val xk = Impl_Array_Stack.as_push (Impl_Array_Stack.as_take xh ab) xj;
in
  (xk, (ac, (xi, (ae, be))))
end;
                                    in
                                      (case
let
  val (ab, _) = xg;
in
  List.all_interval_nat
    (fn xca => Collections_Patch1.bs_mem xca (Impl_Array_Stack.as_top ab))
    Arith.zero_nata (Automata_Impl.igbgi_num_acc g_impl)
end
of true =>
  let
    val (ab, (ac, (ad, (ae, be)))) = xg;
    val xj =
      (fn xfa =>
        (case Impl_Array_Hash_Map.ahm_lookup (HOL.eq A1_)
                (HashCode.bounded_hashcode A2_) xfa ae
          of NONE => false
          | SOME i =>
            (if Arith.less_eq_int Arith.zero_int i
              then Arith.less_nat (Arith.nat i) (Impl_Array_Stack.as_top ad)
              else false)));
    val xk =
      (fn xga =>
        (case Impl_Array_Hash_Map.ahm_lookup (HOL.eq A1_)
                (HashCode.bounded_hashcode A2_) xga ae
          of NONE => false
          | SOME i =>
            (if Arith.less_eq_int Arith.zero_int i
              then Arith.less_eq_nat (Impl_Array_Stack.as_top ad) (Arith.nat i)
              else false)));
  in
    (SOME (xj, xk), (ab, (ac, (ad, (ae, be)))))
  end
| false => (NONE, xg))
                                    end
                               else (if not
  (case Impl_Array_Hash_Map.ahm_lookup (HOL.eq A1_)
          (HashCode.bounded_hashcode A2_) xf
          let
            val (_, (_, (xd, _))) = Product_Type.snd ba;
          in
            xd
          end
    of NONE => false
    | SOME i => (if Arith.less_eq_int Arith.zero_int i then false else true))
                                      then (NONE,
     let
       val (xba, xca) = ba;
     in
       (Impl_Array_Stack.as_push xba (Automata_Impl.igbgi_acc g_impl xf),
         Gabow_Skeleton_Code.push_code (A1_, A2_) g_impl xf xca)
     end)
                                      else (NONE, ba)))))
                       xc;
                 in
                   gto_outer_code A2_ a b
                 end
            else sigma))
        xa;
    val _ = Gabow_Skeleton_Statistics.stop ();
  in
    goBrk_code A2_ xb
  end;

fun reconstruct_lasso_tr (A1_, A2_) vr vl g_impl =
  let
    val (a, b) =
      let
        val a =
          Find_Path_Impl.wset_find_path_code (A1_, A2_)
            (Digraph_Impl.graph_restrict_left_impl (fn x => fn f => f x) vr
              (Digraph_Impl.frgi_E g_impl))
            (Digraph_Impl.frgi_V0 g_impl) vl;
      in
        Option.the a
      end;
    val xa =
      Collections_Patch2.atLeastLessThan_tr (Collections_Patch1.bs_empty ())
        Collections_Patch1.bs_insert Arith.zero_nata
        (Automata_Impl.igbgi_num_acc g_impl);
    val xb =
      Digraph_Impl.graph_restrict_right_impl (fn x => fn f => f x) vl
        (Digraph_Impl.frgi_E g_impl);
    val (aa, (ab, _)) =
      While_Combinator.whilea
        (fn (_, (_, xi)) => not (Collections_Patch1.bs_eq xi xa))
        (fn (aa, (ab, bb)) =>
          let
            val xd =
              Find_Path_Impl.wset_find_path_code (A1_, A2_) xb [aa]
                (fn ac =>
                  not (Collections_Patch1.bs_subset_eq
                        (Automata_Impl.igbgi_acc g_impl ac) bb));
            val (ac, bc) = Option.the xd;
          in
            (bc, (ab @ ac,
                   Collections_Patch1.bs_union bb
                     (Automata_Impl.igbgi_acc g_impl bc)))
          end)
        (b, ([], Automata_Impl.igbgi_acc g_impl b));
    val xd =
      (if Autoref_Bindings_HOL.is_Nil ab
        then Find_Path_Impl.find_path1_code (A1_, A2_) xb aa (HOL.eq A1_ b)
        else Find_Path_Impl.wset_find_path_code (A1_, A2_) xb [aa]
               (HOL.eq A1_ b));
    val (ac, _) = Option.the xd;
  in
    (a, ab @ ac)
  end;

fun find_lasso_tr (A1_, A2_) g_impl =
  (case find_ce_tr (A1_, A2_) g_impl of NONE => NONE
    | SOME (a, b) =>
      let
        val aa = reconstruct_lasso_tr (A1_, A2_) a b g_impl;
      in
        SOME aa
      end);

end; (*struct Gabow_GBG_Code*)

structure CAVA_Abstract : sig
  val cfg_ce : 'a * ('b * 'c) -> 'c
  val cfg_l2b : 'a * ('b * 'c) -> 'a
end = struct

fun cfg_ce (c1, (c2, c3)) = c3;

fun cfg_l2b (c1, (c2, c3)) = c1;

end; (*struct CAVA_Abstract*)

structure LTL_Rewrite : sig
  val ltln_pure_universal_frmls_impl : 'a LTL.ltln -> bool
  val ltln_pure_eventual_frmls_impl : 'a LTL.ltln -> bool
  val ltln_rewrite_step_impl : 'a HOL.equal -> 'a LTL.ltln -> 'a LTL.ltln
  val ltln_rewrite_rec : 'a HOL.equal -> 'a LTL.ltln -> 'a LTL.ltln
  val ltln_rewrite : 'a HOL.equal -> 'a LTL.ltln -> 'a LTL.ltln
end = struct

fun ltln_pure_universal_frmls_impl (LTL.LTLnRelease (LTL.LTLnFalse, phi)) = true
  | ltln_pure_universal_frmls_impl (LTL.LTLnAnd (nu, mu)) =
    ltln_pure_universal_frmls_impl nu andalso ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl (LTL.LTLnOr (nu, mu)) =
    ltln_pure_universal_frmls_impl nu andalso ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl (LTL.LTLnUntil (nu, mu)) =
    ltln_pure_universal_frmls_impl nu andalso ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl (LTL.LTLnRelease (LTL.LTLnTrue, mu)) =
    ltln_pure_universal_frmls_impl LTL.LTLnTrue andalso
      ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl (LTL.LTLnRelease (LTL.LTLnProp v, mu)) =
    ltln_pure_universal_frmls_impl (LTL.LTLnProp v) andalso
      ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl (LTL.LTLnRelease (LTL.LTLnNProp v, mu)) =
    ltln_pure_universal_frmls_impl (LTL.LTLnNProp v) andalso
      ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl (LTL.LTLnRelease (LTL.LTLnAnd (v, va), mu)) =
    ltln_pure_universal_frmls_impl (LTL.LTLnAnd (v, va)) andalso
      ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl (LTL.LTLnRelease (LTL.LTLnOr (v, va), mu)) =
    ltln_pure_universal_frmls_impl (LTL.LTLnOr (v, va)) andalso
      ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl (LTL.LTLnRelease (LTL.LTLnNext v, mu)) =
    ltln_pure_universal_frmls_impl (LTL.LTLnNext v) andalso
      ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl (LTL.LTLnRelease (LTL.LTLnUntil (v, va), mu))
    = ltln_pure_universal_frmls_impl (LTL.LTLnUntil (v, va)) andalso
        ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl
    (LTL.LTLnRelease (LTL.LTLnRelease (v, va), mu)) =
    ltln_pure_universal_frmls_impl (LTL.LTLnRelease (v, va)) andalso
      ltln_pure_universal_frmls_impl mu
  | ltln_pure_universal_frmls_impl LTL.LTLnTrue = false
  | ltln_pure_universal_frmls_impl LTL.LTLnFalse = false
  | ltln_pure_universal_frmls_impl (LTL.LTLnProp v) = false
  | ltln_pure_universal_frmls_impl (LTL.LTLnNProp v) = false
  | ltln_pure_universal_frmls_impl (LTL.LTLnNext v) = false;

fun ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (LTL.LTLnTrue, phi)) = true
  | ltln_pure_eventual_frmls_impl (LTL.LTLnAnd (nu, mu)) =
    ltln_pure_eventual_frmls_impl nu andalso ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnOr (nu, mu)) =
    ltln_pure_eventual_frmls_impl nu andalso ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (LTL.LTLnFalse, mu)) =
    ltln_pure_eventual_frmls_impl LTL.LTLnFalse andalso
      ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (LTL.LTLnProp v, mu)) =
    ltln_pure_eventual_frmls_impl (LTL.LTLnProp v) andalso
      ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (LTL.LTLnNProp v, mu)) =
    ltln_pure_eventual_frmls_impl (LTL.LTLnNProp v) andalso
      ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (LTL.LTLnAnd (v, va), mu)) =
    ltln_pure_eventual_frmls_impl (LTL.LTLnAnd (v, va)) andalso
      ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (LTL.LTLnOr (v, va), mu)) =
    ltln_pure_eventual_frmls_impl (LTL.LTLnOr (v, va)) andalso
      ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (LTL.LTLnNext v, mu)) =
    ltln_pure_eventual_frmls_impl (LTL.LTLnNext v) andalso
      ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (LTL.LTLnUntil (v, va), mu)) =
    ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (v, va)) andalso
      ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnUntil (LTL.LTLnRelease (v, va), mu))
    = ltln_pure_eventual_frmls_impl (LTL.LTLnRelease (v, va)) andalso
        ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl (LTL.LTLnRelease (nu, mu)) =
    ltln_pure_eventual_frmls_impl nu andalso ltln_pure_eventual_frmls_impl mu
  | ltln_pure_eventual_frmls_impl LTL.LTLnTrue = false
  | ltln_pure_eventual_frmls_impl LTL.LTLnFalse = false
  | ltln_pure_eventual_frmls_impl (LTL.LTLnProp v) = false
  | ltln_pure_eventual_frmls_impl (LTL.LTLnNProp v) = false
  | ltln_pure_eventual_frmls_impl (LTL.LTLnNext v) = false;

fun ltln_rewrite_step_impl A_ psi =
  (case psi of LTL.LTLnTrue => psi | LTL.LTLnFalse => psi
    | LTL.LTLnProp _ => psi | LTL.LTLnNProp _ => psi
    | LTL.LTLnAnd (psi_1, psi_2) =>
      (case (psi_1, psi_2) of (LTL.LTLnTrue, b) => psi
        | (LTL.LTLnFalse, b) => psi | (LTL.LTLnProp _, b) => psi
        | (LTL.LTLnNProp _, b) => psi | (LTL.LTLnAnd (_, _), b) => psi
        | (LTL.LTLnOr (_, _), b) => psi | (LTL.LTLnNext _, b) => psi
        | (LTL.LTLnUntil (phi, mu), LTL.LTLnTrue) => psi
        | (LTL.LTLnUntil (phi, mu), LTL.LTLnFalse) => psi
        | (LTL.LTLnUntil (phi, mu), LTL.LTLnProp _) => psi
        | (LTL.LTLnUntil (phi, mu), LTL.LTLnNProp _) => psi
        | (LTL.LTLnUntil (phi, mu), LTL.LTLnAnd (_, _)) => psi
        | (LTL.LTLnUntil (phi, mu), LTL.LTLnOr (_, _)) => psi
        | (LTL.LTLnUntil (phi, mu), LTL.LTLnNext _) => psi
        | (LTL.LTLnUntil (phi, mu), LTL.LTLnUntil (nu, mua)) =>
          (if LTL.equal_ltlna A_ mu mua
            then LTL.LTLnUntil (LTL.LTLnAnd (phi, nu), mu) else psi)
        | (LTL.LTLnUntil (phi, mu), LTL.LTLnRelease (_, _)) => psi
        | (LTL.LTLnRelease (phi, nu), LTL.LTLnTrue) => psi
        | (LTL.LTLnRelease (phi, nu), LTL.LTLnFalse) => psi
        | (LTL.LTLnRelease (phi, nu), LTL.LTLnProp _) => psi
        | (LTL.LTLnRelease (phi, nu), LTL.LTLnNProp _) => psi
        | (LTL.LTLnRelease (phi, nu), LTL.LTLnAnd (_, _)) => psi
        | (LTL.LTLnRelease (phi, nu), LTL.LTLnOr (_, _)) => psi
        | (LTL.LTLnRelease (phi, nu), LTL.LTLnNext _) => psi
        | (LTL.LTLnRelease (phi, nu), LTL.LTLnUntil (_, _)) => psi
        | (LTL.LTLnRelease (phi, nu), LTL.LTLnRelease (phia, mu)) =>
          (if LTL.equal_ltlna A_ phi phia
            then LTL.LTLnRelease (phi, LTL.LTLnAnd (nu, mu)) else psi))
    | LTL.LTLnOr (psi_1, psi_2) =>
      (case (psi_1, psi_2) of (LTL.LTLnTrue, b) => psi
        | (LTL.LTLnFalse, b) => psi | (LTL.LTLnProp _, b) => psi
        | (LTL.LTLnNProp _, b) => psi | (LTL.LTLnAnd (_, _), b) => psi
        | (LTL.LTLnOr (_, _), b) => psi | (LTL.LTLnNext _, b) => psi
        | (LTL.LTLnUntil (phi, nu), LTL.LTLnTrue) => psi
        | (LTL.LTLnUntil (phi, nu), LTL.LTLnFalse) => psi
        | (LTL.LTLnUntil (phi, nu), LTL.LTLnProp _) => psi
        | (LTL.LTLnUntil (phi, nu), LTL.LTLnNProp _) => psi
        | (LTL.LTLnUntil (phi, nu), LTL.LTLnAnd (_, _)) => psi
        | (LTL.LTLnUntil (phi, nu), LTL.LTLnOr (_, _)) => psi
        | (LTL.LTLnUntil (phi, nu), LTL.LTLnNext _) => psi
        | (LTL.LTLnUntil (phi, nu), LTL.LTLnUntil (phia, mu)) =>
          (if LTL.equal_ltlna A_ phi phia
            then LTL.LTLnUntil (phi, LTL.LTLnOr (nu, mu)) else psi)
        | (LTL.LTLnUntil (phi, nu), LTL.LTLnRelease (_, _)) => psi
        | (LTL.LTLnRelease (phi, mu), LTL.LTLnTrue) => psi
        | (LTL.LTLnRelease (phi, mu), LTL.LTLnFalse) => psi
        | (LTL.LTLnRelease (phi, mu), LTL.LTLnProp _) => psi
        | (LTL.LTLnRelease (phi, mu), LTL.LTLnNProp _) => psi
        | (LTL.LTLnRelease (phi, mu), LTL.LTLnAnd (_, _)) => psi
        | (LTL.LTLnRelease (phi, mu), LTL.LTLnOr (_, _)) => psi
        | (LTL.LTLnRelease (phi, mu), LTL.LTLnNext _) => psi
        | (LTL.LTLnRelease (phi, mu), LTL.LTLnUntil (_, _)) => psi
        | (LTL.LTLnRelease (phi, mu), LTL.LTLnRelease (nu, mua)) =>
          (if LTL.equal_ltlna A_ mu mua
            then LTL.LTLnRelease (LTL.LTLnOr (phi, nu), mu) else psi))
    | LTL.LTLnNext _ => psi
    | LTL.LTLnUntil (nu, mu) =>
      (if LTL.equal_ltlna A_ mu LTL.LTLnTrue then LTL.LTLnTrue
        else (case (nu, mu)
               of (LTL.LTLnTrue, LTL.LTLnTrue) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnTrue, LTL.LTLnFalse) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnTrue, LTL.LTLnProp _) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnTrue, LTL.LTLnNProp _) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnTrue, LTL.LTLnAnd (_, _)) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnTrue, LTL.LTLnOr (_, _)) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnTrue, LTL.LTLnNext _) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnTrue, LTL.LTLnUntil (_, a)) =>
                 LTL.LTLnUntil (LTL.LTLnTrue, a)
               | (LTL.LTLnTrue, LTL.LTLnRelease (_, _)) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnProp _, b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnNProp _, b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnAnd (_, _), b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnOr (_, _), b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnNext _, b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnUntil (_, _), b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu else psi))
               | (LTL.LTLnRelease (_, _), b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_eventual_frmls_impl mu then mu
                          else psi))))
    | LTL.LTLnRelease (nu, mu) =>
      (if LTL.equal_ltlna A_ mu LTL.LTLnFalse then LTL.LTLnFalse
        else (case (nu, mu)
               of (LTL.LTLnTrue, b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, LTL.LTLnTrue) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, LTL.LTLnFalse) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, LTL.LTLnProp _) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, LTL.LTLnNProp _) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, LTL.LTLnAnd (_, _)) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, LTL.LTLnOr (_, _)) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, LTL.LTLnNext _) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, LTL.LTLnUntil (_, _)) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnFalse, LTL.LTLnRelease (_, a)) =>
                 LTL.LTLnRelease (LTL.LTLnFalse, a)
               | (LTL.LTLnProp _, b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnNProp _, b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnAnd (_, _), b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnOr (_, _), b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnNext _, b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnUntil (_, _), b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu else psi))
               | (LTL.LTLnRelease (_, _), b) =>
                 (if LTL.equal_ltlna A_ nu mu then nu
                   else (if ltln_pure_universal_frmls_impl mu then mu
                          else psi)))));

fun ltln_rewrite_rec A_ psi =
  (case ltln_rewrite_step_impl A_ psi of LTL.LTLnTrue => LTL.LTLnTrue
    | LTL.LTLnFalse => LTL.LTLnFalse | LTL.LTLnProp a => LTL.LTLnProp a
    | LTL.LTLnNProp a => LTL.LTLnNProp a
    | LTL.LTLnAnd (nu, mu) =>
      LTL.LTLnAnd (ltln_rewrite_rec A_ nu, ltln_rewrite_rec A_ mu)
    | LTL.LTLnOr (nu, mu) =>
      LTL.LTLnOr (ltln_rewrite_rec A_ nu, ltln_rewrite_rec A_ mu)
    | LTL.LTLnNext nu => LTL.LTLnNext (ltln_rewrite_rec A_ nu)
    | LTL.LTLnUntil (nu, mu) =>
      LTL.LTLnUntil (ltln_rewrite_rec A_ nu, ltln_rewrite_rec A_ mu)
    | LTL.LTLnRelease (nu, mu) =>
      LTL.LTLnRelease (ltln_rewrite_rec A_ nu, ltln_rewrite_rec A_ mu));

fun ltln_rewrite A_ psi =
  let
    val phi = ltln_rewrite_rec A_ psi;
  in
    (if not (LTL.equal_ltlna A_ phi psi) then ltln_rewrite A_ phi else psi)
  end;

end; (*struct LTL_Rewrite*)

structure PromelaLTL : sig
  datatype binOp = Eq | Le | LEq | Gr | GEq
  datatype ident = Ident of string * IntInf.int option
  datatype propc = CProp of ident | BProp of binOp * ident * ident |
    BExpProp of binOp * ident * IntInf.int
  val identConv : ident -> Promela.varRef
  val ident2expr : ident -> Promela.expr
  val binOpConv : binOp -> Promela.binOp
  val propConv : propc -> Promela.expr
  val ltlConv :
    (Promela.expr, Arith.nat) Assoc_List.assoc_list ->
      propc LTL.ltlc -> Arith.nat LTL.ltlc
  val lm_filter :
    ('a -> bool) -> ('a, Arith.nat) Assoc_List.assoc_list -> IntInf.int
  val validPropcs :
    unit Promela.gState_ext ->
      (Promela.expr, Arith.nat) Assoc_List.assoc_list -> IntInf.int
  val ltlPropcsa : propc LTL.ltlc -> propc list -> propc list
  val ltlPropcs :
    propc LTL.ltlc -> (Promela.expr, Arith.nat) Assoc_List.assoc_list
  val prepare :
    ((string -> string option) -> propc LTL.ltlc) ->
      PromelaAST.module list ->
        ((unit Promela.program_ext *
           (Promela.expr, Arith.nat) Assoc_List.assoc_list) *
          (IntInf.int * unit Promela.gState_ext)) *
          Arith.nat LTL.ltlc
  val nexts_code_aux :
    unit Promela.program_ext *
      (Promela.expr, Arith.nat) Assoc_List.assoc_list ->
      IntInf.int * unit Promela.gState_ext ->
        (IntInf.int * unit Promela.gState_ext) Dlist.dlist Refine_Det.dres
  val dSUCCEED_abort :
    string -> 'a Refine_Det.dres -> 'a Refine_Det.dres -> 'a Refine_Det.dres
  val nexts_code :
    unit Promela.program_ext *
      (Promela.expr, Arith.nat) Assoc_List.assoc_list ->
      IntInf.int * unit Promela.gState_ext ->
        (IntInf.int * unit Promela.gState_ext) Dlist.dlist
  val printConfig :
    (IntInf.int -> char list) ->
      unit Promela.program_ext *
        (Promela.expr, Arith.nat) Assoc_List.assoc_list ->
        (IntInf.int * unit Promela.gState_ext) option ->
          IntInf.int * unit Promela.gState_ext -> char list
end = struct

datatype binOp = Eq | Le | LEq | Gr | GEq;

datatype ident = Ident of string * IntInf.int option;

datatype propc = CProp of ident | BProp of binOp * ident * ident |
  BExpProp of binOp * ident * IntInf.int;

fun identConv (Ident (name, NONE)) = Promela.VarRef (true, name, NONE)
  | identConv (Ident (name, SOME i)) =
    Promela.VarRef (true, name, SOME (Promela.ExprConst i));

fun ident2expr x = (Promela.ExprVarRef o identConv) x;

fun binOpConv Eq = Promela.BinOpEq
  | binOpConv Le = Promela.BinOpLe
  | binOpConv LEq = Promela.BinOpLEq
  | binOpConv Gr = Promela.BinOpGr
  | binOpConv GEq = Promela.BinOpGEq;

fun propConv (CProp ident) =
  Promela.ExprBinOp
    (Promela.BinOpEq, ident2expr ident, Promela.ExprConst (1 : IntInf.int))
  | propConv (BProp (bop, il, ir)) =
    Promela.ExprBinOp (binOpConv bop, ident2expr il, ident2expr ir)
  | propConv (BExpProp (bop, il, ir)) =
    Promela.ExprBinOp (binOpConv bop, ident2expr il, Promela.ExprConst ir);

fun ltlConv p (LTL.LTLcRelease (x, y)) =
  LTL.LTLcRelease (ltlConv p x, ltlConv p y)
  | ltlConv p (LTL.LTLcUntil (x, y)) = LTL.LTLcUntil (ltlConv p x, ltlConv p y)
  | ltlConv p (LTL.LTLcIff (x, y)) = LTL.LTLcIff (ltlConv p x, ltlConv p y)
  | ltlConv p (LTL.LTLcImplies (x, y)) =
    LTL.LTLcImplies (ltlConv p x, ltlConv p y)
  | ltlConv p (LTL.LTLcOr (x, y)) = LTL.LTLcOr (ltlConv p x, ltlConv p y)
  | ltlConv p (LTL.LTLcAnd (x, y)) = LTL.LTLcAnd (ltlConv p x, ltlConv p y)
  | ltlConv p (LTL.LTLcGlobal x) = LTL.LTLcGlobal (ltlConv p x)
  | ltlConv p (LTL.LTLcFinal x) = LTL.LTLcFinal (ltlConv p x)
  | ltlConv p (LTL.LTLcNext x) = LTL.LTLcNext (ltlConv p x)
  | ltlConv p (LTL.LTLcNeg x) = LTL.LTLcNeg (ltlConv p x)
  | ltlConv pa (LTL.LTLcProp p) =
    LTL.LTLcProp
      (Option.the (Assoc_List.lookup Promela.equal_expr pa (propConv p)))
  | ltlConv uv LTL.LTLcFalse = LTL.LTLcFalse
  | ltlConv uu LTL.LTLcTrue = LTL.LTLcTrue;

fun lm_filter p m =
  ListMapImpl.iteratei_map_op_list_it_lm_ops m (fn _ => true)
    (fn (k, v) => fn sigma =>
      (if p k then Collections_Patch1.bs_insert v sigma else sigma))
    (Collections_Patch1.bs_empty ());

fun validPropcs g p =
  lm_filter
    (fn e => not (((Promela.exprArith g Promela.emptyProc e) : IntInf.int) = 0))
    p;

fun ltlPropcsa LTL.LTLcTrue l = l
  | ltlPropcsa LTL.LTLcFalse l = l
  | ltlPropcsa (LTL.LTLcProp p) l = p :: l
  | ltlPropcsa (LTL.LTLcNeg x) l = ltlPropcsa x l
  | ltlPropcsa (LTL.LTLcNext x) l = ltlPropcsa x l
  | ltlPropcsa (LTL.LTLcFinal x) l = ltlPropcsa x l
  | ltlPropcsa (LTL.LTLcGlobal x) l = ltlPropcsa x l
  | ltlPropcsa (LTL.LTLcAnd (x, y)) l = ltlPropcsa y (ltlPropcsa x l)
  | ltlPropcsa (LTL.LTLcOr (x, y)) l = ltlPropcsa y (ltlPropcsa x l)
  | ltlPropcsa (LTL.LTLcImplies (x, y)) l = ltlPropcsa y (ltlPropcsa x l)
  | ltlPropcsa (LTL.LTLcIff (x, y)) l = ltlPropcsa y (ltlPropcsa x l)
  | ltlPropcsa (LTL.LTLcUntil (x, y)) l = ltlPropcsa y (ltlPropcsa x l)
  | ltlPropcsa (LTL.LTLcRelease (x, y)) l = ltlPropcsa y (ltlPropcsa x l);

fun ltlPropcs p =
  let
    val ps =
      List.remdups Promela.equal_expr (List.map propConv (ltlPropcsa p []));
  in
    ListMapImpl.g_list_to_map_lm_basic_ops Promela.equal_expr
      (List.zip ps (List.upt Arith.zero_nata (List.size_list ps)))
  end;

fun prepare ltlChoose ast =
  let
    val _ = PromelaStatistics.start ();
    val eAst = Promela.preprocess ast;
    val (ltls, (g_0, prog)) = Promela.setUp eAst;
    val phi = ltlChoose (Assoc_List.lookup Stringa.equal_literal ltls);
    val p = ltlPropcs phi;
    val phi_c = ltlConv p phi;
    val ps_0 = validPropcs g_0 p;
    val _ = PromelaStatistics.stop_timer ();
  in
    (((prog, p), (ps_0, g_0)), phi_c)
  end;

fun nexts_code_aux prog g =
  let
    val (x, xa) = prog;
  in
    Promela.nexts_code
      (Product_Type.equal_prod Arith.equal_integer
        (Promela.equal_gState_ext Product_Type.equal_unit))
      x (fn ga => (validPropcs ga xa, ga)) (Product_Type.snd g)
  end;

fun dSUCCEED_abort msg dm m =
  (case m of Refine_Det.DSUCCEEDi => (raise Fail msg) (fn _ => dm)
    | Refine_Det.DFAILi => m | Refine_Det.DRETURN _ => m);

fun nexts_code prog g =
  Refine_Transfer.the_res
    (dSUCCEED_abort "The Universe is broken!"
      (Refine_Det.DRETURN
        (ListSetImpl.g_sng_ls_basic_ops
          (Product_Type.equal_prod Arith.equal_integer
            (Promela.equal_gState_ext Product_Type.equal_unit))
          g))
      (nexts_code_aux prog g));

fun printConfig f prom c_0 c_1 =
  Promela.printConfig f (Product_Type.fst prom)
    (Option.map Product_Type.snd c_0) (Product_Type.snd c_1);

end; (*struct PromelaLTL*)

structure CAVA_Impl : sig
  val bpc_to_sa_impl :
    BoolProgs.instr FArray.IsabelleMapping.ArrayType *
      (Arith.nat * IntInf.int) ->
      ((Arith.nat * IntInf.int -> bool),
        (Arith.nat * IntInf.int -> (Arith.nat * IntInf.int) list),
        ((Arith.nat * IntInf.int) list),
        ((Arith.nat * IntInf.int -> Arith.nat -> bool), unit)
          Automata_Impl.gen_sa_impl_ext)
        Digraph_Impl.gen_frg_impl_ext
  val gerth_ltl_to_gba_code :
    'a HOL.equal * 'a Orderings.linorder ->
      'a LTL.ltlc ->
        ((Arith.nat list), (Arith.nat -> Arith.nat list), (Arith.nat list),
          ((Arith.nat -> IntInf.int),
            ((Arith.nat -> ('a -> bool) -> bool), unit)
              Automata_Impl.gen_igba_impl_ext)
            Automata_Impl.gen_igbg_impl_ext)
          Digraph_Impl.gen_frg_impl_ext
  datatype config_l2b = CFG_L2B_GERTHS
  val ltl_to_gba_code :
    'a HOL.equal * 'a Orderings.linorder ->
      config_l2b ->
        'a LTL.ltlc ->
          ((Arith.nat list), (Arith.nat -> Arith.nat list), (Arith.nat list),
            ((Arith.nat -> IntInf.int),
              ((Arith.nat -> ('a -> bool) -> bool), unit)
                Automata_Impl.gen_igba_impl_ext)
              Automata_Impl.gen_igbg_impl_ext)
            Digraph_Impl.gen_frg_impl_ext
  val gbav_sys_prod_impl_cava_reorder :
    ('a -> 'a -> bool) ->
      (('a list), ('a -> 'a list), ('a list),
        (('a -> IntInf.int),
          (('a -> 'b -> bool), unit) Automata_Impl.gen_igba_impl_ext)
          Automata_Impl.gen_igbg_impl_ext)
        Digraph_Impl.gen_frg_impl_ext ->
        (('c -> bool), ('c -> 'c list), ('c list),
          (('c -> 'b), unit) Automata_Impl.gen_sa_impl_ext)
          Digraph_Impl.gen_frg_impl_ext ->
          (('a * 'c -> bool), ('a * 'c -> ('a * 'c) list), (('a * 'c) list),
            (('a * 'c -> IntInf.int), unit) Automata_Impl.gen_igbg_impl_ext)
            Digraph_Impl.gen_frg_impl_ext
  val dflt_inter_impl :
    ('a -> 'a -> bool) ->
      (('b -> bool), ('b -> 'b list), ('b list),
        (('b -> 'c), unit) Automata_Impl.gen_sa_impl_ext)
        Digraph_Impl.gen_frg_impl_ext ->
        (('a list), ('a -> 'a list), ('a list),
          (('a -> IntInf.int),
            (('a -> 'c -> bool), unit) Automata_Impl.gen_igba_impl_ext)
            Automata_Impl.gen_igbg_impl_ext)
          Digraph_Impl.gen_frg_impl_ext ->
          (('a * 'b -> bool), ('a * 'b -> ('a * 'b) list), (('a * 'b) list),
            (('a * 'b -> IntInf.int), unit) Automata_Impl.gen_igbg_impl_ext)
            Digraph_Impl.gen_frg_impl_ext *
            ('a * 'b -> 'b)
  val gabow_find_ce_code :
    'a HOL.equal * 'a HashCode.hashable ->
      (('a -> bool), ('a -> 'a list), ('a list),
        (('a -> IntInf.int), 'b) Automata_Impl.gen_igbg_impl_ext)
        Digraph_Impl.gen_frg_impl_ext ->
        (('a, unit) Lasso.lasso_ext option) option
  val ndfs_find_ce_code :
    'a HOL.equal * 'a HashCode.hashable ->
      (('a -> bool), ('a -> 'a list), ('a list),
        (('a -> IntInf.int), 'b) Automata_Impl.gen_igbg_impl_ext)
        Digraph_Impl.gen_frg_impl_ext ->
        (('a, unit) Lasso.lasso_ext option) option
  datatype config_ce = CFG_CE_SCC_GABOW | CFG_CE_NDFS
  val find_ce_code :
    'a HOL.equal * 'a HashCode.hashable ->
      config_ce ->
        (('a -> bool), ('a -> 'a list), ('a list),
          (('a -> IntInf.int), 'b) Automata_Impl.gen_igbg_impl_ext)
          Digraph_Impl.gen_frg_impl_ext ->
          (('a, unit) Lasso.lasso_ext option) option
  val impl_model_check_ltl_to_gba_code_uu_find_ce_code_map_lasso :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b Orderings.linorder ->
      config_l2b * (unit * config_ce) ->
        (('a -> bool), ('a -> 'a list), ('a list),
          (('a -> 'b -> bool), unit) Automata_Impl.gen_sa_impl_ext)
          Digraph_Impl.gen_frg_impl_ext ->
          'b LTL.ltlc -> (('a, unit) Lasso.lasso_ext option) option
  val cava_sys_agn :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b Orderings.linorder ->
      config_l2b * (unit * config_ce) ->
        (('a -> bool), ('a -> 'a list), ('a list),
          (('a -> 'b -> bool), unit) Automata_Impl.gen_sa_impl_ext)
          Digraph_Impl.gen_frg_impl_ext ->
          'b LTL.ltlc -> (('a, unit) Lasso.lasso_ext option) option
  val cava_bpc :
    config_l2b * (unit * config_ce) ->
      BoolProgs.instr FArray.IsabelleMapping.ArrayType *
        (Arith.nat * IntInf.int) ->
        Arith.nat LTL.ltlc ->
          (((Arith.nat * IntInf.int), unit) Lasso.lasso_ext option) option
  val dflt_cfg : config_l2b * (unit * config_ce)
  val promela_to_sa_impl :
    (unit Promela.program_ext *
      (Promela.expr, Arith.nat) Assoc_List.assoc_list) *
      (IntInf.int * unit Promela.gState_ext) ->
      ((IntInf.int * unit Promela.gState_ext -> bool),
        (IntInf.int * unit Promela.gState_ext ->
          (IntInf.int * unit Promela.gState_ext) list),
        ((IntInf.int * unit Promela.gState_ext) list),
        ((IntInf.int * unit Promela.gState_ext -> Arith.nat -> bool), unit)
          Automata_Impl.gen_sa_impl_ext)
        Digraph_Impl.gen_frg_impl_ext
  val cava_promela :
    config_l2b * (unit * config_ce) ->
      (unit Promela.program_ext *
        (Promela.expr, Arith.nat) Assoc_List.assoc_list) *
        (IntInf.int * unit Promela.gState_ext) ->
        Arith.nat LTL.ltlc ->
          (((IntInf.int * unit Promela.gState_ext), unit)
             Lasso.lasso_ext option) option
  val frv_edge_set_code :
    ('a -> 'a -> bool) ->
      (('a list), ('a -> 'a list), ('a list), 'b)
        Digraph_Impl.gen_frg_impl_ext ->
        ('a * 'a) list
  val frv_export_code :
    ('a -> 'a -> bool) ->
      (('a list), ('a -> 'a list), ('a list), 'b)
        Digraph_Impl.gen_frg_impl_ext ->
        'a list * ('a list * ('a * 'a) list)
end = struct

fun bpc_to_sa_impl bpc =
  let
    val (bp, c0) = bpc;
  in
    Digraph_Impl.Gen_frg_impl_ext
      ((fn _ => true),
        List.remdups
          (Product_Type.equal_prod Arith.equal_nat Arith.equal_integer) o
          BoolProgs.nexts bp,
        [c0],
        Automata_Impl.Gen_sa_impl_ext
          ((fn c => fn i => Collections_Patch1.bs_mem i (Product_Type.snd c)),
            ()))
  end;

fun gerth_ltl_to_gba_code (A1_, A2_) phi =
  LTL_to_GBA_impl.create_name_igba_code (A1_, A2_)
    (LTL_Rewrite.ltln_rewrite A1_
      (LTL.ltl_to_ltln (LTL.ltl_pushneg (LTL.ltlc_to_ltl phi))));

datatype config_l2b = CFG_L2B_GERTHS;

fun ltl_to_gba_code (A1_, A2_) cfg =
  let
    val CFG_L2B_GERTHS = cfg;
  in
    gerth_ltl_to_gba_code (A1_, A2_)
  end;

fun gbav_sys_prod_impl_cava_reorder eqq gi si =
  Digraph_Impl.Gen_frg_impl_ext
    ((fn (x, xa) =>
       Impl_List_Set.glist_member eqq x (Digraph_Impl.frgi_V gi) andalso
         Digraph_Impl.frgi_V si xa),
      (fn (x, xa) =>
        (if Automata_Impl.igbai_L gi x (Automata_Impl.sai_L si xa)
          then List.maps
                 (fn xaa =>
                   List.map (fn xb => (xb, xaa)) (Digraph_Impl.frgi_E gi x))
                 (List.rev (Digraph_Impl.frgi_E si xa))
          else [])),
      List.maps (fn x => List.map (fn a => (x, a)) (Digraph_Impl.frgi_V0 si))
        (Digraph_Impl.frgi_V0 gi),
      Automata_Impl.Gen_igbg_impl_ext
        (Automata_Impl.igbgi_num_acc gi,
          (fn (x, xa) =>
            (if Digraph_Impl.frgi_V si xa then Automata_Impl.igbgi_acc gi x
              else Collections_Patch1.bs_empty ())),
          ()));

fun dflt_inter_impl eqq si gi =
  (gbav_sys_prod_impl_cava_reorder eqq gi si, Product_Type.snd);

fun gabow_find_ce_code (A1_, A2_) =
  Option.map (SOME o Lasso.lasso_of_prpl) o
    Gabow_GBG_Code.find_lasso_tr (A1_, A2_);

fun ndfs_find_ce_code (A1_, A2_) g =
  let
    val x = Automata_Impl.degeneralize_ext_impl g (fn _ => ());
  in
    (case NDFS_SI.code_blue_dfs_ahs
            (Product_Type.equal_prod A1_ Arith.equal_nat,
              HashCode.hashable_prod A2_ HashCode.hashable_nat)
            x
      of NONE => NONE
      | SOME xb =>
        SOME (SOME (Lasso.map_lasso Product_Type.fst (Lasso.lasso_of_prpl xb))))
  end;

datatype config_ce = CFG_CE_SCC_GABOW | CFG_CE_NDFS;

fun find_ce_code (A1_, A2_) cfg =
  (case cfg of CFG_CE_SCC_GABOW => gabow_find_ce_code (A1_, A2_)
    | CFG_CE_NDFS => ndfs_find_ce_code (A1_, A2_));

fun impl_model_check_ltl_to_gba_code_uu_find_ce_code_map_lasso (A1_, A2_)
  (B1_, B2_) cfg sys phi =
  let
    val ba =
      ltl_to_gba_code (B1_, B2_) (CAVA_Abstract.cfg_l2b cfg) (LTL.LTLcNeg phi);
    val (g, map_q) = dflt_inter_impl Arith.equal_nata sys ba;
  in
    (case find_ce_code
            (Product_Type.equal_prod Arith.equal_nat A1_,
              HashCode.hashable_prod HashCode.hashable_nat A2_)
            (CAVA_Abstract.cfg_ce cfg) g
      of NONE => NONE | SOME NONE => SOME NONE
      | SOME (SOME ce) => SOME (SOME (Lasso.map_lasso map_q ce)))
  end;

fun cava_sys_agn (A1_, A2_) (B1_, B2_) =
  impl_model_check_ltl_to_gba_code_uu_find_ce_code_map_lasso (A1_, A2_)
    (B1_, B2_);

fun cava_bpc cfg bpc phi =
  cava_sys_agn
    (Product_Type.equal_prod Arith.equal_nat Arith.equal_integer,
      HashCode.hashable_prod HashCode.hashable_nat
        Collections_Patch1.hashable_integer)
    (Arith.equal_nat, Arith.linorder_nat) cfg (bpc_to_sa_impl bpc) phi;

val dflt_cfg : config_l2b * (unit * config_ce) =
  (CFG_L2B_GERTHS, ((), CFG_CE_SCC_GABOW));

fun promela_to_sa_impl promc =
  let
    val (prom, c_0) = promc;
  in
    Digraph_Impl.Gen_frg_impl_ext
      ((fn _ => true),
        ListSetImpl.g_to_list_ls_basic_ops o PromelaLTL.nexts_code prom, [c_0],
        Automata_Impl.Gen_sa_impl_ext
          ((fn c => fn i => Collections_Patch1.bs_mem i (Product_Type.fst c)),
            ()))
  end;

fun cava_promela cfg promc phi =
  cava_sys_agn
    (Product_Type.equal_prod Arith.equal_integer
       (Promela.equal_gState_ext Product_Type.equal_unit),
      HashCode.hashable_prod Collections_Patch1.hashable_integer
        (Promela.hashable_gState_ext Collections_Patch1.hashable_uint_unit))
    (Arith.equal_nat, Arith.linorder_nat) cfg (promela_to_sa_impl promc) phi;

fun frv_edge_set_code eq g =
  Foldi.foldli (Digraph_Impl.frgi_V g) (fn _ => true)
    (fn x => fn sigma =>
      let
        val xa = List.map (fn a => (x, a)) (Digraph_Impl.frgi_E g x);
      in
        Gen_Set.gen_union Foldi.foldli
          (Impl_List_Set.glist_insert (Autoref_Bindings_HOL.prod_eq eq eq)) xa
          sigma
      end)
    [];

fun frv_export_code eq g =
  let
    val x = Fun.id (Digraph_Impl.frgi_V g);
    val xa = Fun.id (Digraph_Impl.frgi_V0 g);
    val xb = Fun.id (frv_edge_set_code eq g);
  in
    (x, (xa, xb))
  end;

end; (*struct CAVA_Impl*)

structure BoolProgs_Extras : sig
  val counter_eq : Arith.nat -> Arith.nat -> Arith.nat -> BoolProgs.bexp
  val array_check :
    (Arith.nat -> BoolProgs.bexp) ->
      (Arith.nat -> BoolProgs.bexp) -> Arith.nat -> BoolProgs.bexp
  val dec_counter_toggle :
    Arith.nat list -> BoolProgs.bexp list -> bool -> Arith.nat -> BoolProgs.com
  val dec_countera :
    Arith.nat list ->
      BoolProgs.bexp list -> bool -> Arith.nat -> Arith.nat -> BoolProgs.com
  val dec_counter :
    Arith.nat list ->
      BoolProgs.bexp list -> Arith.nat -> Arith.nat -> BoolProgs.com
  val inc_counter :
    Arith.nat list ->
      BoolProgs.bexp list -> Arith.nat -> Arith.nat -> BoolProgs.com
  val set_counter :
    Arith.nat list ->
      BoolProgs.bexp list ->
        Arith.nat -> Arith.nat -> Arith.nat -> BoolProgs.com
  val array_access :
    (Arith.nat -> BoolProgs.bexp) ->
      (Arith.nat -> BoolProgs.com) -> Arith.nat -> BoolProgs.com
  val mapping_from_list :
    'a HOL.equal -> ('a * 'b) list -> ('a, 'b) Mapping.mapping
end = struct

fun counter_eq pos m n =
  (if Arith.less_nat m n then BoolProgs.Ff
    else let
           val posT = List.upt Arith.zero_nata n;
           val posF = List.upt n m;
           val a =
             List.map (fn x => BoolProgs.V (Arith.plus_nata pos x)) posT @
               List.map
                 (fn x => BoolProgs.Not (BoolProgs.V (Arith.plus_nata pos x)))
                 posF;
         in
           List.foldl (fn aa => fn b => BoolProgs.And (aa, b)) BoolProgs.Tt a
         end);

fun array_check ctr chk m =
  List.foldl
    (fn bexp => fn c =>
      BoolProgs.And
        (BoolProgs.Or (BoolProgs.Not (ctr c), chk c),
          BoolProgs.Or (ctr c, bexp)))
    BoolProgs.Ff (List.upt Arith.zero_nata m);

fun dec_counter_toggle vs bs false uu = BoolProgs.Assign (vs, bs)
  | dec_counter_toggle vs bs true pos =
    BoolProgs.Assign
      (Arith.minus_nat pos Arith.one_nata :: vs, BoolProgs.Ff :: bs);

fun dec_countera vs bs start pos n =
  (if Arith.equal_nata n Arith.zero_nata then dec_counter_toggle vs bs start pos
    else BoolProgs.IfTE
           (BoolProgs.Not (BoolProgs.V pos), dec_counter_toggle vs bs start pos,
             dec_countera vs bs true (Arith.suc pos)
               (Arith.minus_nat n Arith.one_nata)));

fun dec_counter vs bs = dec_countera vs bs false;

fun inc_counter vs bs pos n =
  (if Arith.equal_nata n Arith.zero_nata then BoolProgs.Assign (vs, bs)
    else BoolProgs.IfTE
           (BoolProgs.V pos,
             inc_counter vs bs (Arith.suc pos)
               (Arith.minus_nat n Arith.one_nata),
             BoolProgs.Assign (pos :: vs, BoolProgs.Tt :: bs)));

fun set_counter vs bs uu l uv =
  (if Arith.equal_nata l Arith.zero_nata then BoolProgs.Assign (vs, bs)
    else (if Arith.equal_nata uv Arith.zero_nata
           then set_counter (uu :: vs) (BoolProgs.Ff :: bs) (Arith.suc uu)
                  (Arith.minus_nat l Arith.one_nata) Arith.zero_nata
           else set_counter (uu :: vs) (BoolProgs.Tt :: bs) (Arith.suc uu)
                  (Arith.minus_nat l Arith.one_nata)
                  (Arith.minus_nat uv Arith.one_nata)));

fun array_access ctr act m =
  List.foldl (fn bexp => fn c => BoolProgs.IfTE (ctr c, act c, bexp))
    BoolProgs.Skip (List.upt Arith.zero_nata m);

fun mapping_from_list A_ =
  List.foldl (fn m => fn (k, v) => Mapping.update A_ k v m) Mapping.empty;

end; (*struct BoolProgs_Extras*)

structure BoolProgs_Simple : sig
  val simple_prog :
    Arith.nat -> Arith.nat -> (BoolProgs.bexp * BoolProgs.com) list
  val simple :
    Arith.nat ->
      BoolProgs.instr FArray.IsabelleMapping.ArrayType *
        (Arith.nat * IntInf.int)
  val simple_fun :
    Arith.nat -> ((char list), (Arith.nat -> BoolProgs.bexp)) Mapping.mapping
  val simple_const : Arith.nat -> ((char list), BoolProgs.bexp) Mapping.mapping
end = struct

fun simple_prog uu n =
  (if Arith.equal_nata n Arith.zero_nata then []
    else (BoolProgs.V (Arith.minus_nat n Arith.one_nata),
           BoolProgs.Assign
             ([Arith.minus_nat n Arith.one_nata], [BoolProgs.Ff])) ::
           simple_prog uu (Arith.minus_nat n Arith.one_nata));

fun simple n =
  (BoolProgs.optcomp
     (BoolProgs.While (BoolProgs.Tt, BoolProgs.Gc (simple_prog n n))),
    (Arith.zero_nata,
      List.foldl (fn xs => fn i => Collections_Patch1.bs_insert i xs)
        (Collections_Patch1.bs_empty ()) (List.upt Arith.zero_nata n)));

fun simple_fun n =
  BoolProgs_Extras.mapping_from_list (List.equal_list Stringa.equal_char)
    [([#"v", #"a", #"r"], BoolProgs.V)];

fun simple_const n = Mapping.empty;

end; (*struct BoolProgs_Simple*)

structure BoolProgs_LTL_Conv : sig
  val b2l : BoolProgs.bexp -> Arith.nat LTL.ltlc
  datatype propc = CProp of char list | FProp of (char list * IntInf.int)
  val ltl_conv :
    ((char list), BoolProgs.bexp) Mapping.mapping ->
      ((char list), (Arith.nat -> BoolProgs.bexp)) Mapping.mapping ->
        propc LTL.ltlc -> (Arith.nat LTL.ltlc, (char list)) Sum_Type.sum
end = struct

fun b2l BoolProgs.Tt = LTL.LTLcTrue
  | b2l BoolProgs.Ff = LTL.LTLcFalse
  | b2l (BoolProgs.V v) = LTL.LTLcProp v
  | b2l (BoolProgs.Not e) = LTL.LTLcNeg (b2l e)
  | b2l (BoolProgs.And (e1, e2)) = LTL.LTLcAnd (b2l e1, b2l e2)
  | b2l (BoolProgs.Or (e1, e2)) = LTL.LTLcOr (b2l e1, b2l e2);

datatype propc = CProp of char list | FProp of (char list * IntInf.int);

fun ltl_conv uu uv LTL.LTLcTrue = Sum_Type.Inl LTL.LTLcTrue
  | ltl_conv uw ux LTL.LTLcFalse = Sum_Type.Inl LTL.LTLcFalse
  | ltl_conv c uy (LTL.LTLcProp (CProp s)) =
    (case Mapping.lookup (List.equal_list Stringa.equal_char) c s
      of NONE =>
        Sum_Type.Inr
          ([#"U", #"n", #"k", #"n", #"o", #"w", #"n", #" ", #"c", #"o", #"n",
             #"s", #"t", #"a", #"n", #"t", #":", #" "] @
            s)
      | SOME ca => Sum_Type.Inl (b2l ca))
  | ltl_conv uz m (LTL.LTLcProp (FProp (s, arg))) =
    (case Mapping.lookup (List.equal_list Stringa.equal_char) m s
      of NONE =>
        Sum_Type.Inr
          ([#"U", #"n", #"k", #"n", #"o", #"w", #"n", #" ", #"f", #"u", #"n",
             #"c", #"t", #"i", #"o", #"n", #":", #" "] @
            s)
      | SOME f => (Sum_Type.Inl o b2l o f o Arith.nat_of_integer) arg)
  | ltl_conv c m (LTL.LTLcNeg x) =
    (case ltl_conv c m x of Sum_Type.Inl l => Sum_Type.Inl (LTL.LTLcNeg l)
      | Sum_Type.Inr a => Sum_Type.Inr a)
  | ltl_conv c m (LTL.LTLcNext x) =
    (case ltl_conv c m x of Sum_Type.Inl l => Sum_Type.Inl (LTL.LTLcNext l)
      | Sum_Type.Inr a => Sum_Type.Inr a)
  | ltl_conv c m (LTL.LTLcFinal x) =
    (case ltl_conv c m x of Sum_Type.Inl l => Sum_Type.Inl (LTL.LTLcFinal l)
      | Sum_Type.Inr a => Sum_Type.Inr a)
  | ltl_conv c m (LTL.LTLcGlobal x) =
    (case ltl_conv c m x of Sum_Type.Inl l => Sum_Type.Inl (LTL.LTLcGlobal l)
      | Sum_Type.Inr a => Sum_Type.Inr a)
  | ltl_conv c m (LTL.LTLcAnd (x, y)) =
    (case ltl_conv c m x
      of Sum_Type.Inl l =>
        (case ltl_conv c m y
          of Sum_Type.Inl r => Sum_Type.Inl (LTL.LTLcAnd (l, r))
          | Sum_Type.Inr a => Sum_Type.Inr a)
      | Sum_Type.Inr a => Sum_Type.Inr a)
  | ltl_conv c m (LTL.LTLcOr (x, y)) =
    (case ltl_conv c m x
      of Sum_Type.Inl l =>
        (case ltl_conv c m y
          of Sum_Type.Inl r => Sum_Type.Inl (LTL.LTLcOr (l, r))
          | Sum_Type.Inr a => Sum_Type.Inr a)
      | Sum_Type.Inr a => Sum_Type.Inr a)
  | ltl_conv c m (LTL.LTLcImplies (x, y)) =
    (case ltl_conv c m x
      of Sum_Type.Inl l =>
        (case ltl_conv c m y
          of Sum_Type.Inl r => Sum_Type.Inl (LTL.LTLcImplies (l, r))
          | Sum_Type.Inr a => Sum_Type.Inr a)
      | Sum_Type.Inr a => Sum_Type.Inr a)
  | ltl_conv c m (LTL.LTLcIff (x, y)) =
    (case ltl_conv c m x
      of Sum_Type.Inl l =>
        (case ltl_conv c m y
          of Sum_Type.Inl r => Sum_Type.Inl (LTL.LTLcIff (l, r))
          | Sum_Type.Inr a => Sum_Type.Inr a)
      | Sum_Type.Inr a => Sum_Type.Inr a)
  | ltl_conv c m (LTL.LTLcUntil (x, y)) =
    (case ltl_conv c m x
      of Sum_Type.Inl l =>
        (case ltl_conv c m y
          of Sum_Type.Inl r => Sum_Type.Inl (LTL.LTLcUntil (l, r))
          | Sum_Type.Inr a => Sum_Type.Inr a)
      | Sum_Type.Inr a => Sum_Type.Inr a)
  | ltl_conv c m (LTL.LTLcRelease (x, y)) =
    (case ltl_conv c m x
      of Sum_Type.Inl l =>
        (case ltl_conv c m y
          of Sum_Type.Inl r => Sum_Type.Inl (LTL.LTLcRelease (l, r))
          | Sum_Type.Inr a => Sum_Type.Inr a)
      | Sum_Type.Inr a => Sum_Type.Inr a);

end; (*struct BoolProgs_LTL_Conv*)

structure BoolProgs_LeaderFilters : sig
  val error : Arith.nat
  val turn : Arith.nat -> Arith.nat -> Arith.nat
  val b : Arith.nat -> Arith.nat -> Arith.nat
  val c : Arith.nat -> Arith.nat -> Arith.nat
  val curr : Arith.nat -> Arith.nat -> Arith.nat
  val l_1 : Arith.nat -> Arith.nat -> Arith.nat
  val l_2 : Arith.nat -> Arith.nat -> Arith.nat
  val l_3 : Arith.nat -> Arith.nat -> Arith.nat
  val l_4 : Arith.nat -> Arith.nat -> Arith.nat
  val l_5 : Arith.nat -> Arith.nat -> Arith.nat
  val l_8 : Arith.nat -> Arith.nat -> Arith.nat
  val l_9 : Arith.nat -> Arith.nat -> Arith.nat
  val lf_fun :
    Arith.nat -> ((char list), (Arith.nat -> BoolProgs.bexp)) Mapping.mapping
  val curr_eq : Arith.nat -> Arith.nat -> Arith.nat -> BoolProgs.bexp
  val elected : Arith.nat
  val lf_init : Arith.nat -> IntInf.int
  val curr_access :
    Arith.nat -> Arith.nat -> (Arith.nat -> BoolProgs.com) -> BoolProgs.com
  val curr_check :
    Arith.nat -> Arith.nat -> (Arith.nat -> BoolProgs.bexp) -> BoolProgs.bexp
  val set_turn :
    Arith.nat ->
      Arith.nat ->
        Arith.nat -> Arith.nat list -> BoolProgs.bexp list -> BoolProgs.com
  val inc_curr :
    Arith.nat ->
      Arith.nat -> Arith.nat list -> BoolProgs.bexp list -> BoolProgs.com
  val turn_eq : Arith.nat -> Arith.nat -> Arith.nat -> BoolProgs.bexp
  val process : Arith.nat -> Arith.nat -> (BoolProgs.bexp * BoolProgs.com) list
  val lf_const : Arith.nat -> ((char list), BoolProgs.bexp) Mapping.mapping
  val processes : Arith.nat -> (BoolProgs.bexp * BoolProgs.com) list
  val leader_filters :
    Arith.nat ->
      BoolProgs.instr FArray.IsabelleMapping.ArrayType *
        (Arith.nat * IntInf.int)
end = struct

val error : Arith.nat = Arith.one_nata;

fun turn n i =
  Arith.plus_nata (Arith.plus_nata error Arith.one_nata) (Arith.times_nata n i);

fun b n i = Arith.plus_nata (turn n n) i;

fun c n i = Arith.plus_nata (b n n) i;

fun curr n i = Arith.plus_nata (c n n) (Arith.times_nata n i);

fun l_1 n i = Arith.plus_nata (curr n n) i;

fun l_2 n i = Arith.plus_nata (l_1 n n) i;

fun l_3 n i = Arith.plus_nata (l_2 n n) i;

fun l_4 n i = Arith.plus_nata (l_3 n n) i;

fun l_5 n i = Arith.plus_nata (l_4 n n) i;

fun l_8 n i = Arith.plus_nata (l_5 n n) i;

fun l_9 n i = Arith.plus_nata (l_8 n n) i;

fun lf_fun n =
  BoolProgs_Extras.mapping_from_list (List.equal_list Stringa.equal_char)
    [([#"b"], (fn i => BoolProgs.V (b n i))),
      ([#"c"], (fn i => BoolProgs.V (c n i)))];

fun curr_eq n i v = BoolProgs_Extras.counter_eq (curr n i) n v;

val elected : Arith.nat = Arith.zero_nata;

fun lf_init n =
  List.foldl (fn xs => fn c => Collections_Patch1.bs_insert c xs)
    (Collections_Patch1.bs_empty ())
    (List.upt (l_1 n Arith.zero_nata) (l_1 n n));

fun curr_access n i act =
  BoolProgs_Extras.array_access (curr_eq n i) act
    (Arith.plus_nata n Arith.one_nata);

fun curr_check n i chk =
  BoolProgs_Extras.array_check (curr_eq n i) chk
    (Arith.plus_nata n Arith.one_nata);

fun set_turn n i v vs bs = BoolProgs_Extras.set_counter vs bs (turn n i) n v;

fun inc_curr n i vs bs = BoolProgs_Extras.inc_counter vs bs (curr n i) n;

fun turn_eq n i v = BoolProgs_Extras.counter_eq (turn n i) n v;

fun process n i =
  [(BoolProgs.V (l_1 n i),
     curr_access n i
       (fn v =>
         set_turn n v (Arith.plus_nata i Arith.one_nata) [l_1 n i, l_2 n i]
           [BoolProgs.Ff, BoolProgs.Tt])),
    (BoolProgs.And
       (BoolProgs.V (l_2 n i),
         curr_check n i (fn v => BoolProgs.Not (BoolProgs.V (b n v)))),
      BoolProgs.Assign ([l_2 n i, l_3 n i], [BoolProgs.Ff, BoolProgs.Tt])),
    (BoolProgs.V (l_3 n i),
      curr_access n i
        (fn v =>
          BoolProgs.Assign
            ([b n v, l_3 n i, l_4 n i],
              [BoolProgs.Tt, BoolProgs.Ff, BoolProgs.Tt]))),
    (BoolProgs.V (l_4 n i),
      curr_access n i
        (fn v =>
          BoolProgs.IfTE
            (BoolProgs.Not (turn_eq n v (Arith.plus_nata i Arith.one_nata)),
              BoolProgs.Assign
                ([l_4 n i, l_5 n i], [BoolProgs.Ff, BoolProgs.Tt]),
              BoolProgs.Assign
                ([l_4 n i, l_8 n i], [BoolProgs.Ff, BoolProgs.Tt])))),
    (BoolProgs.V (l_5 n i),
      curr_access n i
        (fn v =>
          BoolProgs.Assign
            ([c n v, b n v, l_5 n i],
              [BoolProgs.Tt, BoolProgs.Ff, BoolProgs.Ff]))),
    (BoolProgs.V (l_8 n i),
      BoolProgs.IfTE
        (curr_eq n i Arith.zero_nata,
          inc_curr n i [l_8 n i, l_1 n i] [BoolProgs.Ff, BoolProgs.Tt],
          curr_access n i
            (fn v =>
              BoolProgs.IfTE
                (BoolProgs.Not (BoolProgs.V (c n v)),
                  BoolProgs.Assign
                    ([l_8 n i, l_9 n i], [BoolProgs.Ff, BoolProgs.Tt]),
                  inc_curr n i [l_8 n i, l_1 n i]
                    [BoolProgs.Ff, BoolProgs.Tt])))),
    (BoolProgs.And (BoolProgs.V (l_9 n i), BoolProgs.V elected),
      BoolProgs.Assign ([error, l_9 n i], [BoolProgs.Tt, BoolProgs.Ff])),
    (BoolProgs.V (l_9 n i),
      BoolProgs.Assign ([elected, l_9 n i], [BoolProgs.Tt, BoolProgs.Ff]))];

fun lf_const n =
  BoolProgs_Extras.mapping_from_list (List.equal_list Stringa.equal_char)
    [([#"e", #"l", #"e", #"c", #"t", #"e", #"d"], BoolProgs.V elected),
      ([#"e", #"r", #"r", #"o", #"r"], BoolProgs.V error)];

fun processes n = List.maps (process n) (List.upt Arith.zero_nata n);

fun leader_filters n =
  (BoolProgs.optcomp
     (BoolProgs.While (BoolProgs.Tt, BoolProgs.Gc (processes n))),
    (Arith.zero_nata, lf_init n));

end; (*struct BoolProgs_LeaderFilters*)

structure BoolProgs_ReaderWriter : sig
  val ready : Arith.nat
  val q_error : Arith.nat
  val reading : 'a -> 'b -> Arith.nat -> Arith.nat
  val writing : Arith.nat -> 'a -> Arith.nat -> Arith.nat
  val activeR : Arith.nat -> Arith.nat -> Arith.nat
  val activeR_eq : Arith.nat -> Arith.nat -> Arith.nat -> BoolProgs.bexp
  val rw_fun :
    Arith.nat -> ((char list), (Arith.nat -> BoolProgs.bexp)) Mapping.mapping
  val writers_active : Arith.nat
  val readers_active : Arith.nat
  val writer_control :
    Arith.nat -> 'a -> Arith.nat -> (BoolProgs.bexp * BoolProgs.com) list
  val inc_activeR :
    Arith.nat ->
      Arith.nat -> Arith.nat list -> BoolProgs.bexp list -> BoolProgs.com
  val dec_activeR :
    Arith.nat ->
      Arith.nat -> Arith.nat list -> BoolProgs.bexp list -> BoolProgs.com
  val reader_control :
    Arith.nat -> Arith.nat -> Arith.nat -> (BoolProgs.bexp * BoolProgs.com) list
  val rw_body :
    Arith.nat ->
      Arith.nat ->
        Arith.nat -> Arith.nat -> (BoolProgs.bexp * BoolProgs.com) list
  val rw_init : 'a -> 'b -> IntInf.int
  val rw_const : Arith.nat -> ((char list), BoolProgs.bexp) Mapping.mapping
  val reader_writer :
    Arith.nat ->
      Arith.nat ->
        BoolProgs.instr FArray.IsabelleMapping.ArrayType *
          (Arith.nat * IntInf.int)
end = struct

val ready : Arith.nat = Arith.zero_nata;

val q_error : Arith.nat = Arith.nat_of_integer (3 : IntInf.int);

fun reading r w i = Arith.plus_nata (Arith.plus_nata q_error Arith.one_nata) i;

fun writing r w i = Arith.plus_nata (reading r w r) i;

fun activeR r w = writing r w w;

fun activeR_eq r w v = BoolProgs_Extras.counter_eq (activeR r w) r v;

fun rw_fun n =
  BoolProgs_Extras.mapping_from_list (List.equal_list Stringa.equal_char)
    [([#"r", #"e", #"a", #"d", #"i", #"n", #"g"],
       (fn i => BoolProgs.V (reading n n i))),
      ([#"w", #"r", #"i", #"t", #"i", #"n", #"g"],
        (fn i => BoolProgs.V (writing n n i))),
      ([#"a", #"c", #"t", #"i", #"v", #"e", #"R", #"_", #"e", #"q"],
        activeR_eq n n)];

val writers_active : Arith.nat = Arith.nat_of_integer (2 : IntInf.int);

val readers_active : Arith.nat = Arith.one_nata;

fun writer_control r w i =
  [(BoolProgs.V ready,
     BoolProgs.Assign
       ([ready, writers_active, writing r w i],
         [BoolProgs.Ff, BoolProgs.Tt, BoolProgs.Tt])),
    (BoolProgs.And (BoolProgs.V readers_active, BoolProgs.V (writing r w i)),
      BoolProgs.Assign
        ([readers_active, q_error, writing r w i],
          [BoolProgs.Ff, BoolProgs.Tt, BoolProgs.Ff])),
    (BoolProgs.And (BoolProgs.V writers_active, BoolProgs.V (writing r w i)),
      BoolProgs.Assign
        ([writers_active, ready, writing r w i],
          [BoolProgs.Ff, BoolProgs.Tt, BoolProgs.Ff]))];

fun inc_activeR r w vs bs = BoolProgs_Extras.inc_counter vs bs (activeR r w) r;

fun dec_activeR r w vs bs = BoolProgs_Extras.dec_counter vs bs (activeR r w) r;

fun reader_control r w i =
  [(BoolProgs.V ready,
     BoolProgs.Assign ([ready, readers_active], [BoolProgs.Ff, BoolProgs.Tt])),
    (BoolProgs.And
       (BoolProgs.V readers_active,
         BoolProgs.Not (BoolProgs.V (reading r w i))),
      inc_activeR r w [reading r w i] [BoolProgs.Tt]),
    (BoolProgs.And (BoolProgs.V readers_active, BoolProgs.V (reading r w i)),
      dec_activeR r w [reading r w i] [BoolProgs.Ff]),
    (BoolProgs.And (BoolProgs.V readers_active, activeR_eq r w Arith.zero_nata),
      BoolProgs.Assign
        ([readers_active, ready], [BoolProgs.Ff, BoolProgs.Tt]))];

fun rw_body uu uv r w =
  (if Arith.equal_nata w Arith.zero_nata
    then (if Arith.equal_nata r Arith.zero_nata then []
           else reader_control uu uv (Arith.minus_nat r Arith.one_nata) @
                  rw_body uu uv (Arith.minus_nat r Arith.one_nata)
                    Arith.zero_nata)
    else writer_control uu uv (Arith.minus_nat w Arith.one_nata) @
           rw_body uu uv r (Arith.minus_nat w Arith.one_nata));

fun rw_init r w =
  Collections_Patch1.bs_insert ready (Collections_Patch1.bs_empty ());

fun rw_const n =
  BoolProgs_Extras.mapping_from_list (List.equal_list Stringa.equal_char)
    [([#"r", #"e", #"a", #"d", #"y"], BoolProgs.V ready),
      ([#"r", #"e", #"a", #"d", #"e", #"r", #"s", #"_", #"a", #"c", #"t", #"i",
         #"v", #"e"],
        BoolProgs.V readers_active),
      ([#"w", #"r", #"i", #"t", #"e", #"r", #"s", #"_", #"a", #"c", #"t", #"i",
         #"v", #"e"],
        BoolProgs.V writers_active),
      ([#"q", #"_", #"e", #"r", #"r", #"o", #"r"], BoolProgs.V q_error)];

fun reader_writer r w =
  (BoolProgs.optcomp
     (BoolProgs.While (BoolProgs.Tt, BoolProgs.Gc (rw_body r w r w))),
    (Arith.zero_nata, rw_init r w));

end; (*struct BoolProgs_ReaderWriter*)

structure BoolProgs_Philosophers : sig
  val eata : 'a -> 'b -> 'b
  val eat : 'a -> Arith.nat -> BoolProgs.bexp
  val one : 'a Arith.plus -> 'a -> 'a -> 'a
  val freea : 'a Arith.diva * 'a Arith.numeral -> 'a -> 'a -> 'a
  val free : Arith.nat -> Arith.nat -> BoolProgs.bexp
  val onea : Arith.nat -> Arith.nat -> BoolProgs.bexp
  val dining : Arith.nat -> Arith.nat -> (BoolProgs.bexp * BoolProgs.com) list
  val phil_fun :
    Arith.nat -> ((char list), (Arith.nat -> BoolProgs.bexp)) Mapping.mapping
  val phil_init : Arith.nat -> IntInf.int
  val phil_const : Arith.nat -> ((char list), BoolProgs.bexp) Mapping.mapping
  val philosophers :
    Arith.nat ->
      BoolProgs.instr FArray.IsabelleMapping.ArrayType *
        (Arith.nat * IntInf.int)
end = struct

fun eata m i = i;

fun eat m i = BoolProgs.V (eata m i);

fun one A_ m i = Arith.plus A_ m i;

fun freea (A1_, A2_) m i =
  Arith.plus ((Arith.plus_semigroup_add o Arith.semigroup_add_numeral) A2_)
    (Arith.times ((Arith.times_dvd o Arith.dvd_div) A1_)
      (Arith.numeral A2_ (Arith.Bit0 Arith.One)) m)
    (Arith.moda A1_ i m);

fun free m i = BoolProgs.V (freea (Arith.div_nat, Arith.numeral_nat) m i);

fun onea m i = BoolProgs.V (one Arith.plus_nat m i);

fun dining m i =
  (if Arith.equal_nata i Arith.zero_nata then []
    else [(BoolProgs.And
             (BoolProgs.Not (eat m (Arith.minus_nat i Arith.one_nata)),
               free m (Arith.minus_nat i Arith.one_nata)),
            BoolProgs.Assign
              ([one Arith.plus_nat m (Arith.minus_nat i Arith.one_nata),
                 freea (Arith.div_nat, Arith.numeral_nat) m
                   (Arith.minus_nat i Arith.one_nata)],
                [BoolProgs.Tt, BoolProgs.Ff])),
           (BoolProgs.And
              (onea m (Arith.minus_nat i Arith.one_nata),
                free m
                  (Arith.plus_nata (Arith.minus_nat i Arith.one_nata)
                    Arith.one_nata)),
             BoolProgs.Assign
               ([one Arith.plus_nat m (Arith.minus_nat i Arith.one_nata),
                  freea (Arith.div_nat, Arith.numeral_nat) m
                    (Arith.plus_nata (Arith.minus_nat i Arith.one_nata)
                      Arith.one_nata),
                  eata m (Arith.minus_nat i Arith.one_nata)],
                 [BoolProgs.Ff, BoolProgs.Ff, BoolProgs.Tt])),
           (eat m (Arith.minus_nat i Arith.one_nata),
             BoolProgs.Assign
               ([freea (Arith.div_nat, Arith.numeral_nat) m
                   (Arith.minus_nat i Arith.one_nata),
                  freea (Arith.div_nat, Arith.numeral_nat) m
                    (Arith.plus_nata (Arith.minus_nat i Arith.one_nata)
                      Arith.one_nata),
                  eata m (Arith.minus_nat i Arith.one_nata)],
                 [BoolProgs.Tt, BoolProgs.Tt, BoolProgs.Ff]))] @
           dining m (Arith.minus_nat i Arith.one_nata));

fun phil_fun n =
  BoolProgs_Extras.mapping_from_list (List.equal_list Stringa.equal_char)
    [([#"e", #"a", #"t"], eat n), ([#"o", #"n", #"e"], onea n),
      ([#"f", #"r", #"e", #"e"], free n)];

fun phil_init n =
  List.foldl
    (fn xs => fn i =>
      Collections_Patch1.bs_insert
        (freea (Arith.div_nat, Arith.numeral_nat) n i) xs)
    (Collections_Patch1.bs_empty ()) (List.upt Arith.zero_nata n);

fun phil_const n = Mapping.empty;

fun philosophers n =
  (BoolProgs.optcomp
     (BoolProgs.While (BoolProgs.Tt, BoolProgs.Gc (dining n n))),
    (Arith.zero_nata, phil_init n));

end; (*struct BoolProgs_Philosophers*)

structure BoolProgs_Programs : sig
  val progs :
    ((char list),
      (char list *
        (char list *
          (Arith.nat ->
            (BoolProgs.instr FArray.IsabelleMapping.ArrayType *
              (Arith.nat * IntInf.int)) *
              (((char list), BoolProgs.bexp) Mapping.mapping *
                ((char list), (Arith.nat -> BoolProgs.bexp))
                  Mapping.mapping)))))
      Mapping.mapping
  val default_prog : char list
  val chose_prog :
    char list ->
      Arith.nat ->
        char list *
          (char list *
            ((BoolProgs.instr FArray.IsabelleMapping.ArrayType *
               (Arith.nat * IntInf.int)) *
              (((char list), BoolProgs.bexp) Mapping.mapping *
                ((char list), (Arith.nat -> BoolProgs.bexp)) Mapping.mapping)))
  val keys_of_map : ((char list), 'a) Mapping.mapping -> (char list) list
  val list_progs : (char list * (char list * char list)) list
end = struct

val progs :
  ((char list),
    (char list *
      (char list *
        (Arith.nat ->
          (BoolProgs.instr FArray.IsabelleMapping.ArrayType *
            (Arith.nat * IntInf.int)) *
            (((char list), BoolProgs.bexp) Mapping.mapping *
              ((char list), (Arith.nat -> BoolProgs.bexp)) Mapping.mapping)))))
    Mapping.mapping
  = BoolProgs_Extras.mapping_from_list (List.equal_list Stringa.equal_char)
      [([#"R", #"W"],
         ([#"R", #"e", #"a", #"d", #"e", #"r", #"/", #"W", #"r", #"i", #"t",
            #"e", #"r"],
           ([#"#", #" ", #"R", #"e", #"a", #"d", #"e", #"r", #"s", #" ", #"a",
              #"n", #"d", #" ", #"#", #" ", #"W", #"r", #"i", #"t", #"e", #"r",
              #"s"],
             (fn n =>
               (BoolProgs_ReaderWriter.reader_writer n n,
                 (BoolProgs_ReaderWriter.rw_const n,
                   BoolProgs_ReaderWriter.rw_fun n)))))),
        ([#"S"],
          ([#"S", #"i", #"m", #"p", #"l", #"e", #" ", #"V", #"a", #"r", #"i",
             #"a", #"b", #"l", #"e", #" ", #"S", #"e", #"t", #"t", #"i", #"n",
             #"g"],
            ([#"#", #" ", #"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #"s"],
              (fn n =>
                (BoolProgs_Simple.simple n,
                  (BoolProgs_Simple.simple_const n,
                    BoolProgs_Simple.simple_fun n)))))),
        ([#"P"],
          ([#"D", #"i", #"n", #"i", #"n", #"g", #" ", #"P", #"h", #"i", #"l",
             #"o", #"s", #"o", #"p", #"h", #"e", #"r", #"s"],
            ([#"#", #" ", #"P", #"h", #"i", #"l", #"o", #"s", #"o", #"p", #"h",
               #"e", #"r", #"s"],
              (fn n =>
                (BoolProgs_Philosophers.philosophers n,
                  (BoolProgs_Philosophers.phil_const n,
                    BoolProgs_Philosophers.phil_fun n)))))),
        ([#"L", #"F"],
          ([#"L", #"e", #"a", #"d", #"e", #"r", #" ", #"F", #"i", #"l", #"t",
             #"e", #"r", #"s"],
            ([#"#", #" ", #"P", #"r", #"o", #"c", #"e", #"s", #"s", #"e", #"s"],
              (fn n =>
                (BoolProgs_LeaderFilters.leader_filters n,
                  (BoolProgs_LeaderFilters.lf_const n,
                    BoolProgs_LeaderFilters.lf_fun n))))))];

val default_prog : char list = [#"S"];

fun chose_prog p n =
  (case Mapping.lookup (List.equal_list Stringa.equal_char) progs p
    of NONE =>
      let
        val (descr, (ndescr, pa)) =
          Option.the
            (Mapping.lookup (List.equal_list Stringa.equal_char) progs
              default_prog);
      in
        (descr @
           [#" ", #"(", #"f", #"a", #"l", #"l", #"b", #"a", #"c", #"k", #")"],
          (ndescr, pa n))
      end
    | SOME (descr, (ndescr, pa)) => (descr, (ndescr, pa n)));

fun keys_of_map x =
  Mapping.ordered_keys
    (List.equal_list Stringa.equal_char,
      List_lexord.linorder_list (Stringa.equal_char, Char_ord.linorder_char))
    x;

val list_progs : (char list * (char list * char list)) list =
  let
    val a = keys_of_map progs;
  in
    List.map
      (fn k =>
        let
          val (descr, (ndescr, _)) =
            Option.the
              (Mapping.lookup (List.equal_list Stringa.equal_char) progs k);
        in
          (k, (descr, ndescr))
        end)
      a
  end;

end; (*struct BoolProgs_Programs*)
