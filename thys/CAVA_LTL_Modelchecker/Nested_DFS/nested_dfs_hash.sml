
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


structure HPY_new_hash : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  type ('a, 'b) gen_bg_impl_ext
  type ('a, 'b, 'c, 'd) gen_frg_impl_ext
  val code_blue_dfs_nat :
    ((nat -> bool), (nat -> nat list), (nat list),
      ((nat -> bool), 'a) gen_bg_impl_ext)
      gen_frg_impl_ext ->
      (nat list * nat list) option
  val code_blue_dfs_ahs_nat :
    ((nat -> bool), (nat -> nat list), (nat list),
      ((nat -> bool), 'a) gen_bg_impl_ext)
      gen_frg_impl_ext ->
      (nat list * nat list) option
  val succ_of_list_impl_int : (IntInf.int * IntInf.int) list -> nat -> nat list
  val code_blue_dfs_hash_nat :
    ((nat -> bool), (nat -> nat list), (nat list),
      ((nat -> bool), 'a) gen_bg_impl_ext)
      gen_frg_impl_ext ->
      (nat list * nat list) option
  val acc_of_list_impl_hash_int : IntInf.int list -> nat -> bool
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer 0 k);

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a itself = Type;

fun def_hashmap_size_nat x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

datatype int = Int_of_integer of IntInf.int;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun integer_of_int (Int_of_integer k) = k;

fun uint32_of_int i = Word32.fromInt (integer_of_int i);

fun hashcode_nat n = uint32_of_int (int_of_nat n);

val hashable_nat =
  {hashcode = hashcode_nat, def_hashmap_size = def_hashmap_size_nat} :
  nat hashable;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

val ord_uint32 =
  {less_eq = (fn a => fn b => Word32.<= (a, b)),
    less = (fn a => fn b => Word32.< (a, b))}
  : Word32.word ord;

val preorder_uint32 = {ord_preorder = ord_uint32} : Word32.word preorder;

val order_uint32 = {preorder_order = preorder_uint32} : Word32.word order;

val linorder_uint32 = {order_linorder = order_uint32} : Word32.word linorder;

datatype color = R | B;

datatype ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;

datatype ('b, 'a) rbt = RBT of ('b, 'a) rbta;

datatype ('b, 'a) assoc_list = Assoc_List of ('b * 'a) list;

datatype ('b, 'a) hashmap = RBT_HM of (Word32.word, ('b, 'a) assoc_list) rbt;

datatype 'a dres = DSUCCEEDi | DFAILi | DRETURN of 'a;

datatype ('a, 'b) hashmapb =
  HashMapa of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype ('b, 'a) hashmapa = HashMap of ('b, 'a) hashmapb;

datatype 'a blue_witness = NO_CYC | REACH of 'a * 'a list |
  CIRC of 'a list * 'a list;

datatype ('a, 'b) gen_bg_impl_ext = Gen_bg_impl_ext of 'a * 'b;

datatype ('a, 'b, 'c, 'd) gen_frg_impl_ext =
  Gen_frg_impl_ext of 'a * 'b * 'c * 'd;

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun empty A_ = RBT Empty;

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

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

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun balance_right a k x (Branch (R, b, s, y, c)) =
  Branch (R, a, k, x, Branch (B, b, s, y, c))
  | balance_right (Branch (B, a, k, x, b)) s y Empty =
    balance (Branch (R, a, k, x, b)) s y Empty
  | balance_right (Branch (B, a, k, x, b)) s y (Branch (B, va, vb, vc, vd)) =
    balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z Empty =
    Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, balance (paint R a) k x b, s, y,
        Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
  | balance_right Empty k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Empty)) k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh))) k x Empty
    = Empty
  | balance_right Empty k x (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Empty)) k x
    (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl))) k x
    (Branch (B, va, vb, vc, vd)) = Empty;

fun balance_left (Branch (R, a, k, x, b)) s y c =
  Branch (R, Branch (B, a, k, x, b), s, y, c)
  | balance_left Empty k x (Branch (B, a, s, y, b)) =
    balance Empty k x (Branch (R, a, s, y, b))
  | balance_left (Branch (B, va, vb, vc, vd)) k x (Branch (B, a, s, y, b)) =
    balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
  | balance_left Empty k x (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
        balance b t z (paint R c))
  | balance_left Empty k x Empty = Empty
  | balance_left Empty k x (Branch (R, Empty, vb, vc, vd)) = Empty
  | balance_left Empty k x (Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd))
    = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x Empty = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Empty, vf, vg, vh)) = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)) = Empty;

fun combine Empty x = x
  | combine (Branch (v, va, vb, vc, vd)) Empty = Branch (v, va, vb, vc, vd)
  | combine (Branch (R, a, k, x, b)) (Branch (R, c, s, y, d)) =
    (case combine b c
      of Empty => Branch (R, a, k, x, Branch (R, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, a, k, x, b)) (Branch (B, c, s, y, d)) =
    (case combine b c
      of Empty => balance_left a k x (Branch (B, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, va, vb, vc, vd)) (Branch (R, b, k, x, c)) =
    Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
  | combine (Branch (R, a, k, x, b)) (Branch (B, va, vb, vc, vd)) =
    Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));

fun rbt_dela A_ x Empty = Empty
  | rbt_dela A_ x (Branch (c, a, y, s, b)) =
    (if less A_ x y then rbt_del_from_lefta A_ x a y s b
      else (if less A_ y x then rbt_del_from_righta A_ x a y s b
             else combine a b))
and rbt_del_from_lefta A_ x (Branch (B, lt, z, v, rt)) y s b =
  balance_left (rbt_dela A_ x (Branch (B, lt, z, v, rt))) y s b
  | rbt_del_from_lefta A_ x Empty y s b =
    Branch (R, rbt_dela A_ x Empty, y, s, b)
  | rbt_del_from_lefta A_ x (Branch (R, va, vb, vc, vd)) y s b =
    Branch (R, rbt_dela A_ x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_del_from_righta A_ x a y s (Branch (B, lt, z, v, rt)) =
  balance_right a y s (rbt_dela A_ x (Branch (B, lt, z, v, rt)))
  | rbt_del_from_righta A_ x a y s Empty =
    Branch (R, a, y, s, rbt_dela A_ x Empty)
  | rbt_del_from_righta A_ x a y s (Branch (R, va, vb, vc, vd)) =
    Branch (R, a, y, s, rbt_dela A_ x (Branch (R, va, vb, vc, vd)));

fun rbt_deletea A_ k t = paint B (rbt_dela A_ k t);

fun impl_of B_ (RBT x) = x;

fun delete A_ xb xc =
  RBT (rbt_deletea ((ord_preorder o preorder_order o order_linorder) A_) xb
        (impl_of A_ xc));

fun rbt_ins A_ f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_ins A_ f k v (Branch (B, l, x, y, r)) =
    (if less A_ k x then balance (rbt_ins A_ f k v l) x y r
      else (if less A_ x k then balance l x y (rbt_ins A_ f k v r)
             else Branch (B, l, x, f k y v, r)))
  | rbt_ins A_ f k v (Branch (R, l, x, y, r)) =
    (if less A_ k x then Branch (R, rbt_ins A_ f k v l, x, y, r)
      else (if less A_ x k then Branch (R, l, x, y, rbt_ins A_ f k v r)
             else Branch (R, l, x, f k y v, r)));

fun rbt_insert_with_key A_ f k v t = paint B (rbt_ins A_ f k v t);

fun rbt_insert A_ = rbt_insert_with_key A_ (fn _ => fn _ => fn nv => nv);

fun insert A_ xc xd xe =
  RBT (rbt_insert ((ord_preorder o preorder_order o order_linorder) A_) xc xd
        (impl_of A_ xe));

fun rbt_lookupa A_ Empty k = NONE
  | rbt_lookupa A_ (Branch (uu, l, x, y, r)) k =
    (if less A_ k x then rbt_lookupa A_ l k
      else (if less A_ x k then rbt_lookupa A_ r k else SOME y));

fun lookup A_ x =
  rbt_lookupa ((ord_preorder o preorder_order o order_linorder) A_)
    (impl_of A_ x);

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun deletea A_ k = filter (fn (ka, _) => not (eq A_ k ka));

fun fst (x1, x2) = x1;

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if eq A_ (fst p) k then (k, v) :: ps else p :: update A_ k v ps);

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun map fi [] = []
  | map fi (x21a :: x22) = fi x21a :: map fi x22;

fun is_none (SOME x) = false
  | is_none NONE = true;

fun gen_set emp ins l = fold ins l emp;

val emptya : ('a, 'b) assoc_list = Assoc_List [];

fun emptyb A_ = (fn _ => empty linorder_uint32);

fun hm_empty_const A_ = RBT_HM (emptyb A_ ());

fun hm_empty A_ = (fn _ => hm_empty_const A_);

fun dbind DFAILi f = DFAILi
  | dbind DSUCCEEDi f = DSUCCEEDi
  | dbind (DRETURN x) f = f x;

fun delete_aux A_ k [] = []
  | delete_aux A_ ka ((k, v) :: xs) =
    (if eq A_ ka k then xs else (k, v) :: delete_aux A_ ka xs);

fun impl_ofa (Assoc_List x) = x;

fun deleteb A_ k al = Assoc_List (delete_aux A_ k (impl_ofa al));

fun lookupa A_ al = map_of A_ (impl_ofa al);

fun snd (x1, x2) = x2;

fun update_with_aux B_ v k f [] = [(k, f v)]
  | update_with_aux B_ v k f (p :: ps) =
    (if eq B_ (fst p) k then (k, f (snd p)) :: ps
      else p :: update_with_aux B_ v k f ps);

fun update_with A_ v k f al =
  Assoc_List (update_with_aux A_ v k f (impl_ofa al));

fun updatea A_ k v = update_with A_ v k (fn _ => v);

fun impl_of_RBT_HM B_ (RBT_HM x) = x;

fun iteratei al c f = foldli (impl_ofa al) c f;

fun iteratei_bmap_op_list_it_lm_basic_ops s = iteratei s;

val zero_nat : nat = Nat 0;

fun g_size_abort_lm_basic_ops b m =
  iteratei_bmap_op_list_it_lm_basic_ops m (fn s => less_nat s b) (fn _ => suc)
    zero_nat;

fun g_isEmpty_lm_basic_ops m =
  equal_nata (g_size_abort_lm_basic_ops one_nat m) zero_nat;

fun rm_map_entry k f m =
  (case lookup linorder_uint32 m k
    of NONE =>
      (case f NONE of NONE => m | SOME v => insert linorder_uint32 k v m)
    | SOME v =>
      (case f (SOME v) of NONE => delete linorder_uint32 k m
        | SOME va => insert linorder_uint32 k va m));

fun deletec (A1_, A2_) k m =
  rm_map_entry (hashcode A2_ k)
    (fn a =>
      (case a of NONE => NONE
        | SOME lm =>
          let
            val lma = deleteb A1_ k lm;
          in
            (if g_isEmpty_lm_basic_ops lma then NONE else SOME lma)
          end))
    m;

fun hm_delete (A1_, A2_) k hm =
  RBT_HM (deletec (A1_, A2_) k (impl_of_RBT_HM A2_ hm));

fun lookupb (A1_, A2_) k m =
  (case lookup linorder_uint32 m (hashcode A2_ k) of NONE => NONE
    | SOME lm => lookupa A1_ lm k);

fun hm_lookup (A1_, A2_) k hm = lookupb (A1_, A2_) k (impl_of_RBT_HM A2_ hm);

fun updateb (A1_, A2_) k v m =
  let
    val hc = hashcode A2_ k;
  in
    (case lookup linorder_uint32 m hc
      of NONE => insert linorder_uint32 hc (updatea A1_ k v emptya) m
      | SOME bm => insert linorder_uint32 hc (updatea A1_ k v bm) m)
  end;

fun hm_update (A1_, A2_) k v hm =
  RBT_HM (updateb (A1_, A2_) k v (impl_of_RBT_HM A2_ hm));

fun apsnd f (x, y) = (x, f y);

fun extract_res cyc =
  (case cyc of NO_CYC => NONE | REACH (_, _) => NONE
    | CIRC (pr, pl) => SOME (pr, pl));

fun impl_ofb B_ (HashMap x) = x;

fun array_get a = FArray.IsabelleMapping.array_get a o integer_of_nat;

fun array_set a = FArray.IsabelleMapping.array_set a o integer_of_nat;

fun new_array v = FArray.IsabelleMapping.new_array v o integer_of_nat;

fun the_res (DRETURN x) = x;

fun is_None a = (case a of NONE => true | SOME _ => false);

fun map2set_insert i k s = i k () s;

fun red_init_witness u v = SOME ([u], v);

fun map2set_memb l k s = (case l k s of NONE => false | SOME _ => true);

fun rbt_lookup less (Branch (uu, l, x, y, r)) k =
  (if less k x then rbt_lookup less l k
    else (if less x k then rbt_lookup less r k else SOME y))
  | rbt_lookup less Empty k = NONE;

fun prep_wit_red v NONE = NONE
  | prep_wit_red v (SOME (p, u)) = SOME (v :: p, u);

fun code_red_dfs_0 A_ e onstack x =
  let
    val (a, b) = x;
    val xa =
      map2set_insert
        (rbt_insert ((ord_preorder o preorder_order o order_linorder) A_)) b a;
  in
    dbind (DRETURN (NDFS_SI_Statistics.vis_red ()))
      (fn _ =>
        dbind (foldli (e b)
                (fn aa =>
                  (case aa of DSUCCEEDi => false | DFAILi => false
                    | DRETURN ab => is_None ab))
                (fn xb => fn s =>
                  dbind s
                    (fn _ =>
                      (if map2set_memb
                            (fn k => fn t =>
                              rbt_lookup
                                (less ((ord_preorder o preorder_order o
 order_linorder)
A_))
                                t k)
                            xb onstack
                        then DRETURN (red_init_witness b xb)
                        else DRETURN NONE)))
                (DRETURN NONE))
          (fn xc =>
            (case xc
              of NONE =>
                foldli (e b)
                  (fn aa =>
                    (case aa of DSUCCEEDi => false | DFAILi => false
                      | DRETURN (_, ab) => is_None ab))
                  (fn xb => fn s =>
                    dbind s
                      (fn (aa, _) =>
                        (if not (map2set_memb
                                  (fn k => fn t =>
                                    rbt_lookup
                                      (less
((ord_preorder o preorder_order o order_linorder) A_))
                                      t k)
                                  xb aa)
                          then dbind (code_red_dfs_0 A_ e onstack (aa, xb))
                                 (fn (ab, bb) =>
                                   DRETURN (ab, prep_wit_red b bb))
                          else DRETURN (aa, NONE))))
                  (DRETURN (xa, NONE))
              | SOME _ => DRETURN (xa, xc))))
  end;

fun code_red_dfs A_ e onstack v u =
  the_res (code_red_dfs_0 A_ e onstack (v, u));

fun rbt_del less x (Branch (c, a, y, s, b)) =
  (if less x y then rbt_del_from_left less x a y s b
    else (if less y x then rbt_del_from_right less x a y s b else combine a b))
  | rbt_del less x Empty = Empty
and rbt_del_from_left less x (Branch (R, va, vb, vc, vd)) y s b =
  Branch (R, rbt_del less x (Branch (R, va, vb, vc, vd)), y, s, b)
  | rbt_del_from_left less x Empty y s b =
    Branch (R, rbt_del less x Empty, y, s, b)
  | rbt_del_from_left less x (Branch (B, lt, z, v, rt)) y s b =
    balance_left (rbt_del less x (Branch (B, lt, z, v, rt))) y s b
and rbt_del_from_right less x a y s (Branch (R, va, vb, vc, vd)) =
  Branch (R, a, y, s, rbt_del less x (Branch (R, va, vb, vc, vd)))
  | rbt_del_from_right less x a y s Empty =
    Branch (R, a, y, s, rbt_del less x Empty)
  | rbt_del_from_right less x a y s (Branch (B, lt, z, v, rt)) =
    balance_right a y s (rbt_del less x (Branch (B, lt, z, v, rt)));

fun nat_of_uint32 x = nat_of_integer (Word32.toInt x : IntInf.int);

fun array_grow a = FArray.IsabelleMapping.array_grow a o integer_of_nat;

fun equal_list A_ [] (x21 :: x22) = false
  | equal_list A_ (x21 :: x22) [] = false
  | equal_list A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_list A_ x22 y22
  | equal_list A_ [] [] = true;

fun equal_blue_witness A_ (REACH (v, lista)) (CIRC (list1, list2)) = false
  | equal_blue_witness A_ (CIRC (list1, list2)) (REACH (v, lista)) = false
  | equal_blue_witness A_ NO_CYC (CIRC (list1, list2)) = false
  | equal_blue_witness A_ (CIRC (list1, list2)) NO_CYC = false
  | equal_blue_witness A_ NO_CYC (REACH (v, lista)) = false
  | equal_blue_witness A_ (REACH (v, lista)) NO_CYC = false
  | equal_blue_witness A_ (CIRC (list1a, list2a)) (CIRC (list1, list2)) =
    equal_list A_ list1a list1 andalso equal_list A_ list2a list2
  | equal_blue_witness A_ (REACH (va, listaa)) (REACH (v, lista)) =
    eq A_ va v andalso equal_list A_ listaa lista
  | equal_blue_witness A_ NO_CYC NO_CYC = true;

fun frgi_V0 (Gen_frg_impl_ext (frgi_V, frgi_E, frgi_V0, more)) = frgi_V0;

fun frgi_E (Gen_frg_impl_ext (frgi_V, frgi_E, frgi_V0, more)) = frgi_E;

fun bgi_F
  (Gen_frg_impl_ext (frgi_V, frgi_E, frgi_V0, Gen_bg_impl_ext (bgi_F, more))) =
  bgi_F;

fun init_wit_blue_early A_ s t =
  (if eq A_ s t then CIRC ([], [s]) else REACH (t, [s]));

fun rbt_delete less k t = paint B (rbt_del less k t);

fun prep_wit_blue A_ u0 NO_CYC = NO_CYC
  | prep_wit_blue A_ u0 (REACH (u, p)) =
    (if eq A_ u0 u then CIRC ([], u0 :: p) else REACH (u, u0 :: p))
  | prep_wit_blue A_ u0 (CIRC (pr, pl)) = CIRC (u0 :: pr, pl);

fun init_wit_blue A_ u0 NONE = NO_CYC
  | init_wit_blue A_ u0 (SOME (p, u)) =
    (if eq A_ u u0 then CIRC ([], p) else REACH (u, p));

fun code_blue_dfs_0 (A1_, A2_) g x =
  let
    val (ab, (ac, (ad, bd))) = x;
    val xc =
      map2set_insert
        (rbt_insert ((ord_preorder o preorder_order o order_linorder) A2_)) bd
        ab;
    val xd =
      map2set_insert
        (rbt_insert ((ord_preorder o preorder_order o order_linorder) A2_)) bd
        ad;
    val xe = bgi_F g bd;
  in
    dbind (DRETURN (NDFS_SI_Statistics.vis_blue ()))
      (fn _ =>
        dbind (foldli (frgi_E g bd)
                (fn a =>
                  (case a of DSUCCEEDi => false | DFAILi => false
                    | DRETURN (_, (_, (_, xr))) =>
                      equal_blue_witness A1_ xr NO_CYC))
                (fn xa => fn s =>
                  dbind s
                    (fn (ae, (af, (ag, bg))) =>
                      (if map2set_memb
                            (fn k => fn t =>
                              rbt_lookup
                                (less ((ord_preorder o preorder_order o
 order_linorder)
A2_))
                                t k)
                            xa ag andalso
                            (xe orelse bgi_F g xa)
                        then DRETURN
                               (ae, (af, (ag, init_wit_blue_early A1_ bd xa)))
                        else (if not (map2set_memb
                                       (fn k => fn t =>
 rbt_lookup (less ((ord_preorder o preorder_order o order_linorder) A2_)) t k)
                                       xa ae)
                               then dbind (code_blue_dfs_0 (A1_, A2_) g
    (ae, (af, (ag, xa))))
                                      (fn (ah, (ai, (aj, bj))) =>
DRETURN (ah, (ai, (aj, prep_wit_blue A1_ bd bj))))
                               else dbind (DRETURN
    (NDFS_SI_Statistics.match_blue ()))
                                      (fn _ => DRETURN (ae, (af, (ag, bg))))))))
                (DRETURN (xc, (ac, (xd, NO_CYC)))))
          (fn (ae, (af, (ag, bg))) =>
            dbind (if equal_blue_witness A1_ bg NO_CYC andalso xe
                    then dbind (DRETURN (code_red_dfs A2_ (frgi_E g) ag af bd))
                           (fn (ah, bh) =>
                             DRETURN (ah, init_wit_blue A1_ bd bh))
                    else DRETURN (af, bg))
              (fn (ah, bh) =>
                let
                  val xi =
                    rbt_delete
                      (less ((ord_preorder o preorder_order o order_linorder)
                              A2_))
                      bd ag;
                in
                  DRETURN (ae, (ah, (xi, bh)))
                end)))
  end;

fun code_blue_dfs (A1_, A2_) g =
  the_res
    (dbind (DRETURN (NDFS_SI_Statistics.start ()))
      (fn _ =>
        dbind (foldli (frgi_V0 g)
                (fn a =>
                  (case a of DSUCCEEDi => false | DFAILi => false
                    | DRETURN (_, (_, xd)) => equal_blue_witness A1_ xd NO_CYC))
                (fn x => fn s =>
                  dbind s
                    (fn (a, (aa, _)) =>
                      (if not (map2set_memb
                                (fn k => fn t =>
                                  rbt_lookup
                                    (less ((ord_preorder o preorder_order o
     order_linorder)
    A2_))
                                    t k)
                                x a)
                        then dbind (code_blue_dfs_0 (A1_, A2_) g
                                     (a, (aa, (Empty, x))))
                               (fn (ab, (ac, (_, bd))) =>
                                 DRETURN (ab, (ac, bd)))
                        else DRETURN (a, (aa, NO_CYC)))))
                (DRETURN (Empty, (Empty, NO_CYC))))
          (fn (_, (_, ba)) =>
            dbind (DRETURN (NDFS_SI_Statistics.stop ()))
              (fn _ => DRETURN (extract_res ba)))));

fun new_hashmap_with A_ size = HashMapa (new_array [] size, zero_nat);

fun ahm_emptya A_ = (fn _ => new_hashmap_with A_ (def_hashmap_size A_ Type));

fun ahm_empty_const A_ = HashMap (ahm_emptya A_ ());

fun ahm_empty A_ = (fn _ => ahm_empty_const A_);

fun sgn_integer k =
  (if ((k : IntInf.int) = 0) then 0
    else (if IntInf.< (k, 0) then (~1 : IntInf.int) else (1 : IntInf.int)));

fun abs_integer k = (if IntInf.< (k, 0) then IntInf.~ k else k);

fun divmod_integer k l =
  (if ((k : IntInf.int) = 0) then (0, 0)
    else (if ((l : IntInf.int) = 0) then (0, k)
           else (apsnd o (fn a => fn b => IntInf.* (a, b)) o sgn_integer) l
                  (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = 0) then (IntInf.~ r, 0)
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (abs_integer l, s)))
                         end)));

fun mod_integer k l = snd (divmod_integer k l);

fun mod_nat m n = Nat (mod_integer (integer_of_nat m) (integer_of_nat n));

fun nat_of_hashcode x = nat_of_uint32 x;

fun bounded_hashcode_nat A_ n x = mod_nat (nat_of_hashcode (hashcode A_ x)) n;

fun minus_nat m n =
  Nat (max ord_integer 0 (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun array_length x = (nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun ahm_deletea (A1_, A2_) k (HashMapa (a, n)) =
  let
    val h = bounded_hashcode_nat A2_ (array_length a) k;
    val m = array_get a h;
    val deleted = not (is_none (map_of A1_ m k));
  in
    HashMapa
      (array_set a h (deletea A1_ k m),
        (if deleted then minus_nat n one_nat else n))
  end;

fun ahm_delete (A1_, A2_) k hm =
  HashMap (ahm_deletea (A1_, A2_) k (impl_ofb A2_ hm));

fun ahm_alpha_aux (A1_, A2_) a k =
  map_of A1_ (array_get a (bounded_hashcode_nat A2_ (array_length a) k)) k;

fun ahm_alpha (A1_, A2_) (HashMapa (a, uu)) = ahm_alpha_aux (A1_, A2_) a;

fun ahm_lookupa (A1_, A2_) k hm = ahm_alpha (A1_, A2_) hm k;

fun ahm_lookup (A1_, A2_) k hm = ahm_lookupa (A1_, A2_) k (impl_ofb A2_ hm);

fun ahm_update_aux (A1_, A2_) (HashMapa (a, n)) k v =
  let
    val h = bounded_hashcode_nat A2_ (array_length a) k;
    val m = array_get a h;
    val insert = is_none (map_of A1_ m k);
  in
    HashMapa
      (array_set a h (update A1_ k v m),
        (if insert then plus_nat n one_nat else n))
  end;

fun idx_iteratei_aux_array_get sz i l c f sigma =
  (if equal_nata i zero_nat orelse not (c sigma) then sigma
    else idx_iteratei_aux_array_get sz (minus_nat i one_nat) l c f
           (f (array_get l (minus_nat sz i)) sigma));

fun idx_iteratei_array_length_array_get l c f sigma =
  idx_iteratei_aux_array_get (array_length l) (array_length l) l c f sigma;

fun ahm_iteratei_aux A_ a c f sigma =
  idx_iteratei_array_length_array_get a c (fn x => foldli x c f) sigma;

fun ahm_rehash_auxa A_ n kv a =
  let
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

fun ahm_update (A1_, A2_) k v hm =
  HashMap (ahm_updatea (A1_, A2_) k v (impl_ofb A2_ hm));

fun array_get_oo x a = FArray.IsabelleMapping.array_get_oo x a o integer_of_nat;

fun array_set_oo f a = FArray.IsabelleMapping.array_set_oo f a o integer_of_nat;

fun ins_hm_basic_ops (A1_, A2_) x s = hm_update (A1_, A2_) x () s;

fun iam_empty x = (fn _ => FArray.IsabelleMapping.array_of_list []) x;

fun memb_ahm_basic_ops (A1_, A2_) x s =
  not (is_none (ahm_lookup (A1_, A2_) x s));

fun ins_ahm_basic_ops (A1_, A2_) x s = ahm_update (A1_, A2_) x () s;

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
                          | DRETURN (_, ab) => is_None ab))
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

fun memb_hm_basic_ops (A1_, A2_) x s = not (is_none (hm_lookup (A1_, A2_) x s));

fun iam_alpha a i = array_get_oo NONE a i;

fun iam_lookup k a = iam_alpha a k;

fun iam_increment l idx =
  max ord_nat (minus_nat (plus_nat idx one_nat) l)
    (plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) l)
      (nat_of_integer (3 : IntInf.int)));

fun iam_update k v a =
  array_set_oo
    (fn _ =>
      let
        val l = array_length a;
      in
        array_set (array_grow a (iam_increment l k) NONE) k (SOME v)
      end)
    a k (SOME v);

fun empty_ahm_basic_ops A_ = ahm_empty A_;

fun delete_ahm_basic_ops (A1_, A2_) x s = ahm_delete (A1_, A2_) x s;

fun code_blue_dfs_ahs_0 (A1_, A2_) g x =
  let
    val (ab, (ac, (ad, bd))) = x;
    val xc = ins_ahm_basic_ops (A1_, A2_) bd ab;
    val xd = ins_ahm_basic_ops (A1_, A2_) bd ad;
    val xe = bgi_F g bd;
  in
    dbind (DRETURN (NDFS_SI_Statistics.vis_blue ()))
      (fn _ =>
        dbind (dbind (DRETURN (id (frgi_E g bd)))
                (fn xs =>
                  foldli xs
                    (fn a =>
                      (case a of DSUCCEEDi => false | DFAILi => false
                        | DRETURN (_, (_, (_, xr))) =>
                          equal_blue_witness A1_ xr NO_CYC))
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
                                 (code_red_dfs_ahs (A1_, A2_) (frgi_E g) ag af
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

fun code_blue_dfs_ahs (A1_, A2_) g =
  the_res
    (dbind (DRETURN (NDFS_SI_Statistics.start ()))
      (fn _ =>
        dbind (dbind (DRETURN (id (frgi_V0 g)))
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

fun code_blue_dfs_nat x = code_blue_dfs (equal_nat, linorder_nat) x;

fun code_red_dfs_hash_0 (A1_, A2_) e onstack x =
  let
    val (a, b) = x;
    val xa = ins_hm_basic_ops (A1_, A2_) b a;
  in
    dbind (DRETURN (NDFS_SI_Statistics.vis_red ()))
      (fn _ =>
        dbind (foldli (e b)
                (fn aa =>
                  (case aa of DSUCCEEDi => false | DFAILi => false
                    | DRETURN ab => is_None ab))
                (fn xb => fn s =>
                  dbind s
                    (fn _ =>
                      (if memb_hm_basic_ops (A1_, A2_) xb onstack
                        then DRETURN (red_init_witness b xb)
                        else DRETURN NONE)))
                (DRETURN NONE))
          (fn xc =>
            (case xc
              of NONE =>
                foldli (e b)
                  (fn aa =>
                    (case aa of DSUCCEEDi => false | DFAILi => false
                      | DRETURN (_, ab) => is_None ab))
                  (fn xb => fn s =>
                    dbind s
                      (fn (aa, _) =>
                        (if not (memb_hm_basic_ops (A1_, A2_) xb aa)
                          then dbind (code_red_dfs_hash_0 (A1_, A2_) e onstack
                                       (aa, xb))
                                 (fn (ab, bb) =>
                                   DRETURN (ab, prep_wit_red b bb))
                          else DRETURN (aa, NONE))))
                  (DRETURN (xa, NONE))
              | SOME _ => DRETURN (xa, xc))))
  end;

fun code_red_dfs_hash (A1_, A2_) e onstack v u =
  the_res (code_red_dfs_hash_0 (A1_, A2_) e onstack (v, u));

fun empty_hm_basic_ops A_ = hm_empty A_;

fun glist_member eq x [] = false
  | glist_member eq x (y :: ys) = eq x y orelse glist_member eq x ys;

fun glist_insert eq x xs = (if glist_member eq x xs then xs else x :: xs);

fun delete_hm_basic_ops (A1_, A2_) x s = hm_delete (A1_, A2_) x s;

fun code_blue_dfs_hash_0 (A1_, A2_) g x =
  let
    val (ab, (ac, (ad, bd))) = x;
    val xc = ins_hm_basic_ops (A1_, A2_) bd ab;
    val xd = ins_hm_basic_ops (A1_, A2_) bd ad;
    val xe = bgi_F g bd;
  in
    dbind (DRETURN (NDFS_SI_Statistics.vis_blue ()))
      (fn _ =>
        dbind (dbind (DRETURN (id (frgi_E g bd)))
                (fn xs =>
                  foldli xs
                    (fn a =>
                      (case a of DSUCCEEDi => false | DFAILi => false
                        | DRETURN (_, (_, (_, xr))) =>
                          equal_blue_witness A1_ xr NO_CYC))
                    (fn xa => fn s =>
                      dbind s
                        (fn (ae, (af, (ag, bg))) =>
                          (if memb_hm_basic_ops (A1_, A2_) xa ag andalso
                                (xe orelse bgi_F g xa)
                            then DRETURN
                                   (ae, (af,
  (ag, init_wit_blue_early A1_ bd xa)))
                            else (if not (memb_hm_basic_ops (A1_, A2_) xa ae)
                                   then dbind
  (code_blue_dfs_hash_0 (A1_, A2_) g (ae, (af, (ag, xa))))
  (fn (ah, (ai, (aj, bj))) => DRETURN (ah, (ai, (aj, prep_wit_blue A1_ bd bj))))
                                   else dbind
  (DRETURN (NDFS_SI_Statistics.match_blue ()))
  (fn _ => DRETURN (ae, (af, (ag, bg))))))))
                    (DRETURN (xc, (ac, (xd, NO_CYC))))))
          (fn (ae, (af, (ag, bg))) =>
            dbind (if equal_blue_witness A1_ bg NO_CYC andalso xe
                    then dbind (DRETURN
                                 (code_red_dfs_hash (A1_, A2_) (frgi_E g) ag af
                                   bd))
                           (fn (ah, bh) =>
                             DRETURN (ah, init_wit_blue A1_ bd bh))
                    else DRETURN (af, bg))
              (fn (ah, bh) =>
                let
                  val xi = delete_hm_basic_ops (A1_, A2_) bd ag;
                in
                  DRETURN (ae, (ah, (xi, bh)))
                end)))
  end;

fun code_blue_dfs_hash (A1_, A2_) g =
  the_res
    (dbind (DRETURN (NDFS_SI_Statistics.start ()))
      (fn _ =>
        dbind (dbind (DRETURN (id (frgi_V0 g)))
                (fn xs =>
                  foldli xs
                    (fn a =>
                      (case a of DSUCCEEDi => false | DFAILi => false
                        | DRETURN (_, (_, xd)) =>
                          equal_blue_witness A1_ xd NO_CYC))
                    (fn x => fn s =>
                      dbind s
                        (fn (a, (aa, _)) =>
                          (if not (memb_hm_basic_ops (A1_, A2_) x a)
                            then dbind (code_blue_dfs_hash_0 (A1_, A2_) g
 (a, (aa, (empty_hm_basic_ops A2_ (), x))))
                                   (fn (ab, (ac, (_, bd))) =>
                                     DRETURN (ab, (ac, bd)))
                            else DRETURN (a, (aa, NO_CYC)))))
                    (DRETURN
                      (empty_hm_basic_ops A2_ (),
                        (empty_hm_basic_ops A2_ (), NO_CYC)))))
          (fn (_, (_, ba)) =>
            dbind (DRETURN (NDFS_SI_Statistics.stop ()))
              (fn _ => DRETURN (extract_res ba)))));

fun acc_of_list_impl_hash x =
  (fn xa =>
    let
      val xaa = gen_set (iam_empty ()) (map2set_insert iam_update) xa;
    in
      (fn xb => map2set_memb iam_lookup xb xaa)
    end)
    x;

fun code_blue_dfs_ahs_nat x = code_blue_dfs_ahs (equal_nat, hashable_nat) x;

fun succ_of_list_impl x =
  (fn xa =>
    let
      val xaa =
        fold (fn (xaa, xb) => fn xc =>
               (case iam_alpha xc xaa of NONE => iam_update xaa [xb] xc
                 | SOME xd =>
                   iam_update xaa (glist_insert equal_nata xb xd) xc))
          xa (iam_empty ());
    in
      (fn xb => (case iam_alpha xaa xb of NONE => [] | SOME xc => xc))
    end)
    x;

fun succ_of_list_impl_int x =
  (succ_of_list_impl o map (fn (u, v) => (nat_of_integer u, nat_of_integer v)))
    x;

fun code_blue_dfs_hash_nat x = code_blue_dfs_hash (equal_nat, hashable_nat) x;

fun acc_of_list_impl_hash_int x =
  (acc_of_list_impl_hash o map nat_of_integer) x;

end; (*struct HPY_new_hash*)
