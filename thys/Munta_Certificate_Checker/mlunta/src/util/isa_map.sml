
structure Uint : sig
  val set_bit : Word.word -> Int.int -> bool -> Word.word
  val shiftl : Word.word -> Int.int -> Word.word
  val shiftr : Word.word -> Int.int -> Word.word
  val shiftr_signed : Word.word -> Int.int -> Word.word
  val test_bit : Word.word -> Int.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word.<< (0wx1, Word.fromLargeInt (Int.toLarge n))
  in if b then Word.orb (x, mask)
     else Word.andb (x, Word.notb mask)
  end

fun shiftl x n =
  Word.<< (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr x n =
  Word.>> (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr_signed x n =
  Word.~>> (x, Word.fromLargeInt (Int.toLarge n))

fun test_bit x n =
  Word.andb (x, Word.<< (0wx1, Word.fromLargeInt (Int.toLarge n))) <> Word.fromInt 0

end; (* struct Uint *)


structure Timing : sig
  val start_timer: unit -> unit
  val save_time: string -> unit
  val get_timings: unit -> (string * Time.time) list
end = struct
  val t = Unsynchronized.ref Time.zeroTime;
  val timings = Unsynchronized.ref [];
  fun start_timer () = (t := Time.now ());
  fun get_elapsed () = Time.- (Time.now (), !t);
  fun save_time s = (timings := ((s, get_elapsed ()) :: !timings));
  fun get_timings () = !timings;
end


(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> Int.int -> bool -> Word32.word
  val shiftl : Word32.word -> Int.int -> Word32.word
  val shiftr : Word32.word -> Int.int -> Word32.word
  val shiftr_signed : Word32.word -> Int.int -> Word32.word
  val test_bit : Word32.word -> Int.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (Int.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (Int.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (Int.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


structure Integer: sig
  val div_mod: int -> int -> int * int
end = struct
  fun div_mod i j = (i div j, i mod j)
end



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

fun new_array (a:'a) (n:Int.int) = array (Int.toInt n, a);

fun array_length (a:'a ArrayType) = Int.fromInt (length a);

fun array_get (a:'a ArrayType) (i:Int.int) = sub (a, Int.toInt i);

fun array_set (a:'a ArrayType) (i:Int.int) (e:'a) = update (a, Int.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:Int.int) (x:'a) = grow (a, Int.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:Int.int) = shrink (a,Int.toInt sz);

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

fun new_array (a:'a) (n:Int.int) = array (Int.toInt n, a);

fun array_length (a:'a ArrayType) = Int.fromInt (length a);

fun array_get (a:'a ArrayType) (i:Int.int) = sub (a, Int.toInt i);

fun array_set (a:'a ArrayType) (i:Int.int) (e:'a) = update (a, Int.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:Int.int) (x:'a) = grow (a, Int.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:Int.int) = shrink (a,Int.toInt sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:Int.int) =
  sub (a,Int.toInt i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:Int.int) (e:'a) =
  update (a, Int.toInt i, e) handle Subscript => d ()

end;
end;





structure Tracing : sig
  val count_up : unit -> unit
  val get_count : unit -> int
end = struct
  val counter = Unsynchronized.ref 0;
  fun count_up () = (counter := !counter + 1);
  fun get_count () = !counter;
end



   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = Int.toInt di,
        src = ArraySlice.slice (src,Int.toInt si,SOME (Int.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,Int.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,Int.toInt i,x); a) handle Subscript => f () | Overflow => f ()

    



structure Isa_Map : sig
  type 'a equal
  type nat
  type 'a itself
  type 'a hashable
  type ('a, 'b) hashmap
  val bounded_hashcode_nat : 'a hashable -> nat -> 'a -> nat
  val hm_lookup : 'a equal * 'a hashable -> 'a -> ('a, 'b) hashmap -> 'b option
  val hm_lookup1 :
    int list * int list -> ((int list * int list), 'a) hashmap -> 'a option
  val hashmap_of_list :
    'a equal * 'a hashable -> ('a * 'b) list -> ('a, 'b) hashmap
  val hashmap_of_list1 :
    ((int list * int list) * 'a) list -> ((int list * int list), 'a) hashmap
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype nat = Nat of int;

datatype 'a itself = Type;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

fun integer_of_nat (Nat x) = x;

fun times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => a <= b), less = (fn a => fn b => a < b)} :
  int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : Int.int) k);

datatype num = One | Bit0 of num | Bit1 of num;

fun def_hashmap_size_list A_ =
  (fn _ =>
    times_nat (nat_of_integer (2 : Int.int)) (def_hashmap_size A_ Type));

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun hashcode_list A_ =
  foldl (fn h => fn x =>
          Word32.+ (Word32.* (h, Word32.fromLargeInt (Int.toLarge (33 : Int.int))), hashcode
            A_ x))
    (Word32.fromLargeInt (Int.toLarge (5381 : Int.int)));

fun hashable_list A_ =
  {hashcode = hashcode_list A_, def_hashmap_size = def_hashmap_size_list A_} :
  ('a list) hashable;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

fun def_hashmap_size_prod A_ B_ =
  (fn _ => plus_nat (def_hashmap_size A_ Type) (def_hashmap_size B_ Type));

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun hashcode_prod A_ B_ x =
  Word32.+ (Word32.* (hashcode A_
                        (fst x), Word32.fromLargeInt (Int.toLarge (33 : Int.int))), hashcode
            B_ (snd x));

fun hashable_prod A_ B_ =
  {hashcode = hashcode_prod A_ B_,
    def_hashmap_size = def_hashmap_size_prod A_ B_}
  : ('a * 'b) hashable;

val equal_integer = {equal = (fn a => fn b => a = b)} : int equal;

fun def_hashmap_size_integer x = (fn _ => nat_of_integer (16 : Int.int)) x;

fun hashcode_integer i = Word32.fromLargeInt (Int.toLarge i);

val hashable_integer =
  {hashcode = hashcode_integer, def_hashmap_size = def_hashmap_size_integer} :
  int hashable;

datatype ('a, 'b) hashmap =
  HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun is_none (SOME x) = false
  | is_none NONE = true;

fun apsnd f (x, y) = (x, f y);

fun array_get a = FArray.IsabelleMapping.array_get a o integer_of_nat;

fun array_set a = FArray.IsabelleMapping.array_set a o integer_of_nat;

fun new_array v = FArray.IsabelleMapping.new_array v o integer_of_nat;

fun nat_of_uint32 x =
  nat_of_integer (Int.fromLarge (Word32.toLargeInt x) : Int.int);

fun array_length x = (nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun nat_of_hashcode x = nat_of_uint32 x;

val one_nat : nat = Nat (1 : Int.int);

fun sgn_integer k =
  (if k = (0 : Int.int) then (0 : Int.int)
    else (if k < (0 : Int.int) then (~1 : Int.int)
           else (1 : Int.int)));

fun divmod_integer k l =
  (if k = (0 : Int.int) then ((0 : Int.int), (0 : Int.int))
    else (if l = (0 : Int.int) then ((0 : Int.int), k)
           else (apsnd o (fn a => fn b => a * b) o sgn_integer) l
                  (if sgn_integer k = sgn_integer l
                    then Integer.div_mod (abs k) (abs l)
                    else let
                           val (r, s) = Integer.div_mod (abs k) (abs l);
                         in
                           (if s = (0 : Int.int) then (~ r, (0 : Int.int))
                             else (~ r - (1 : Int.int), abs l - s))
                         end)));

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun bounded_hashcode_nat A_ n x =
  modulo_nat (nat_of_hashcode (hashcode A_ x)) n;

fun list_map_lookup eq uu [] = NONE
  | list_map_lookup eq k (y :: ys) =
    (if eq (fst y) k then SOME (snd y) else list_map_lookup eq k ys);

fun ahm_lookup_aux eq bhc k a =
  list_map_lookup eq k (array_get a (bhc (array_length a) k));

fun ahm_lookup eq bhc k (HashMap (a, uu)) = ahm_lookup_aux eq bhc k a;

fun hm_lookup (A1_, A2_) = ahm_lookup (eq A1_) (bounded_hashcode_nat A2_);

fun minus_nat m n =
  Nat (max ord_integer (0 : Int.int) (integer_of_nat m - integer_of_nat n));

fun equal_nat m n = integer_of_nat m = integer_of_nat n;

val zero_nat : nat = Nat (0 : Int.int);

fun idx_iteratei_aux get sz i l c f sigma =
  (if equal_nat i zero_nat orelse not (c sigma) then sigma
    else idx_iteratei_aux get sz (minus_nat i one_nat) l c f
           (f (get l (minus_nat sz i)) sigma));

fun idx_iteratei get sz l c f sigma =
  idx_iteratei_aux get (sz l) (sz l) l c f sigma;

fun hm_lookup1 x =
  hm_lookup
    (equal_prod (equal_list equal_integer) (equal_list equal_integer),
      hashable_prod (hashable_list hashable_integer)
        (hashable_list hashable_integer))
    x;

fun hm_grow (HashMap (a, n)) =
  plus_nat (times_nat (nat_of_integer (2 : Int.int)) (array_length a))
    (nat_of_integer (3 : Int.int));

fun less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

fun new_hashmap_with size = HashMap (new_array [] size, zero_nat);

fun ahm_empty def_size = new_hashmap_with def_size;

fun list_map_update_aux eq k v [] accu = (k, v) :: accu
  | list_map_update_aux eq k v (x :: xs) accu =
    (if eq (fst x) k then (k, v) :: xs @ accu
      else list_map_update_aux eq k v xs (x :: accu));

fun list_map_update eq k v m = list_map_update_aux eq k v m [];

val load_factor : nat = nat_of_integer (75 : Int.int);

fun ahm_filled (HashMap (a, n)) =
  less_eq_nat (times_nat (array_length a) load_factor)
    (times_nat n (nat_of_integer (100 : Int.int)));

fun ahm_iteratei_aux a c f sigma =
  idx_iteratei array_get array_length a c (fn x => foldli x c f) sigma;

fun ahm_rehash_auxa bhc n kv a = let
                                   val h = bhc n (fst kv);
                                 in
                                   array_set a h (kv :: array_get a h)
                                 end;

fun ahm_rehash_aux bhc a sz =
  ahm_iteratei_aux a (fn _ => true) (ahm_rehash_auxa bhc sz) (new_array [] sz);

fun ahm_rehash bhc (HashMap (a, n)) sz = HashMap (ahm_rehash_aux bhc a sz, n);

fun ahm_update_aux eq bhc (HashMap (a, n)) k v =
  let
    val h = bhc (array_length a) k;
    val m = array_get a h;
    val insert = is_none (list_map_lookup eq k m);
  in
    HashMap
      (array_set a h (list_map_update eq k v m),
        (if insert then plus_nat n one_nat else n))
  end;

fun ahm_update eq bhc k v hm =
  let
    val hma = ahm_update_aux eq bhc hm k v;
  in
    (if ahm_filled hma then ahm_rehash bhc hma (hm_grow hma) else hma)
  end;

fun hashmap_of_list (A1_, A2_) m =
  fold (fn (a, b) => ahm_update (eq A1_) (bounded_hashcode_nat A2_) a b) m
    (ahm_empty (def_hashmap_size A2_ Type));

fun hashmap_of_list1 x =
  hashmap_of_list
    (equal_prod (equal_list equal_integer) (equal_list equal_integer),
      hashable_prod (hashable_list hashable_integer)
        (hashable_list hashable_integer))
    x;

end; (*struct Isa_Map*)
