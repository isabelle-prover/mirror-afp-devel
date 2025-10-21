signature BOUND = sig
  type bound
  type isabelle_int
  type isabelle_nat
  val isabelle_int: int -> isabelle_int
  val isabelle_nat: int -> isabelle_nat
  val magic_number: int
  val lt: int -> bound
  val lte: int -> bound
  val inf: bound
end

signature SERIALIZE_BOUND = sig
  type bound
  type isabelle_int
  val isabelle_int: int -> isabelle_int
  val from_isabelle_int: isabelle_int -> int
  val magic_number: int
  val lt: int -> bound
  val lte: int -> bound
  val inf: bound
  val is_lt: bound -> bool
  val is_lte: bound -> bool
  val get_integer: bound -> int option
end

functor Serializer64Bit(Bound: SERIALIZE_BOUND) = struct
fun serialize_int x = x |> Bound.from_isabelle_int |> SerInt.serialize


datatype direction = Left | Right
fun shift dir n w =
    case dir of
        Left => Word64.<< (w, Word.fromInt n) |
        Right => Word64.>> (w, Word.fromInt n)

val shiftl = shift Left
val shiftr = shift Right
val shiftl1 = shiftl 1
val shiftr1 = shiftr 1

val all_ff = shiftl (Word64.wordSize - 1) (Word64.fromInt 1) |> Word64.notb

fun set_lsb w = Word64.orb (w, Word64.fromInt 1)

fun lt b = b |> Word64.fromInt |> shiftl1
fun lte b = b |> lt |> set_lsb

fun serialize_bound x =
    case Bound.get_integer x of
        NONE => all_ff |
        (SOME b) => if Bound.is_lt x then lt b else lte b

fun serialize_dbm dbm =
    let
      val len = length dbm
    in
      dbm |> map (SerWord64.serialize o serialize_bound) |> cons (SerInt.serialize len) |> Word8Vector.concat
    end

fun serialize_int_list ls = map serialize_int ls |> Word8Vector.concat

fun serialize_loc (loc, vars) = Word8Vector.concat [serialize_int_list vars, serialize_int_list loc]
fun serialize_union (discrete, union) = Word8Vector.concat (serialize_loc discrete ::map serialize_dbm union)

fun serialize_state_space ls = map serialize_union ls |> Word8Vector.concat

fun serialize p clocks vars state_space =
    let
      val magic_number = SerInt.serialize 42
      (*val lengths = map serialize_int [p, clocks, vars] |> Word8Vector.concat *)
      val lengths = map SerInt.serialize [p, clocks, vars] |> Word8Vector.concat
      val vector_list =  [magic_number, lengths, serialize_state_space state_space]
    in
      vector_list |> Word8Vector.concat
    end
end


functor Deserializer64Bit(Bound : BOUND) = struct
exception Malformed
val bytesPerElem = 8
val maxWord = Word64.fromInt ~1
val elem' = (flip (curry BinIO.inputN) bytesPerElem)
fun elem deser strm =
    let
      val x = elem' strm
      val len = Word8Vector.length x
    in
      if len = bytesPerElem then (deser x) else raise Malformed
    end

val integer = elem SerInt.deserialize
val a_int = elem (Bound.isabelle_int o SerInt.deserialize)
val a_nat = elem (Bound.isabelle_nat o SerInt.deserialize)

(* Unfortunately using cons here results in a constant first value *)
fun block acc deser n strm =
    fold_range (K (fn acc => (deser strm) :: acc)) n acc
    |> rev

fun single_block deser = block [] deser

fun vars n =
    single_block a_int n

fun location n =
    single_block a_int n


fun bound' w =
    let
      val lsb = Word64.andb(w, Word64.fromInt 1)
      val integer_part = Word64.~>> (w, 0w1) |> Word64.toIntX
    in
      if lsb = Word64.fromInt 0 then Bound.lt integer_part
      else Bound.lte integer_part
    end

fun is_inf v =
    let
      val front = Word8Vector.sub (v, 0)
      val rest = Word8VectorSlice.slice (v, 1, NONE)
    in
      front = 0wx7f andalso Word8VectorSlice.all (fn x => x = 0wxff) rest
    end

(* Check for inf for lsb set *)
fun bound v =
    if is_inf v then Bound.inf
    else bound' (SerWord64.deserialize v)

val a_bound = elem bound

fun dbm_line clocks =
    single_block a_bound clocks

fun dbm clocks =
    single_block a_bound (clocks * clocks)

fun scan_next p strm =
    let
      val n = integer strm
    in
      single_block p n strm
    end

fun union clocks =
    scan_next (dbm clocks)

fun pair p1 p2 strm =
    (
      p1 strm,
      p2 strm
    )
  
fun union_buechi clocks =
    scan_next (pair (dbm clocks) a_nat)

fun discrete_state n_vars processes strm =
    (location processes strm, vars n_vars strm)

datatype result =
    Reachable_Set of (((Bound.isabelle_int list * Bound.isabelle_int list) * Bound.bound list list) list)
  | Buechi_Set of (((Bound.isabelle_int list * Bound.isabelle_int list) * (Bound.bound list * Bound.isabelle_nat) list) list)

fun deserialize (strm : BinIO.instream) is_buechi : result option =
    let
      val magic_number = integer strm
      val p =  integer strm
      val clocks = integer strm
      val vars = integer strm
      val state = discrete_state vars p
      val version = if is_buechi then 1 else 0
      val valid =
        magic_number = Bound.magic_number + version
      val scan_reach = pair state (union clocks)
      val scan_buechi = pair state (union_buechi clocks)
    in
      if valid then
      (
        if is_buechi then
          SOME (Buechi_Set (scan_next scan_buechi strm))
        else
          SOME (Reachable_Set (scan_next scan_reach strm))
      ) handle Malformed => NONE
      else NONE
    end
end
