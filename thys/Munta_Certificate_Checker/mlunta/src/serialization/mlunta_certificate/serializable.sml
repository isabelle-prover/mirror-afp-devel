signature SERIALIZABLE = sig
  type from
  type to
  val serialize: from -> to
end

signature BINARY = SERIALIZABLE where type to = Word8Vector.vector

signature SERDE = sig
  include SERIALIZABLE
  val deserialize: to -> from
end

signature BINARY_SERDE = SERDE where type to = Word8Vector.vector

structure SerWord8 : SERDE = struct
type from = Word8.word
type to = Word8Vector.vector
val bytesPerElem = 1
fun serialize x =
    Word8Vector.tabulate (1, K x)
fun deserialize v =
    Word8Vector.sub (v, 0)
end

structure SerWord32 : SERDE = struct
type from = Word32.word
type to = Word8Vector.vector

val bytesPerElem = PackWord32Big.bytesPerElem

fun serialize x =
    let val a = Word8Array.array (4, Word8.fromInt 0) in
      (
	PackWord32Big.update (a, 0, Word32.toLargeX x);
	Word8Array.vector a
      )
    end

fun deserialize v =
   Word32.fromLargeWord (PackWord32Big.subVec (v, 0))
end

structure SerWord64 : SERDE = struct
type from = Word64.word
type to = Word8Vector.vector

val bytesPerElem = 8
val rhs_mask = Word64.fromInt 0 |> Word64.notb |> flip (curry Word64.>>) 0w32

fun serialize x =
    let
      val a = Word8Array.array (8, Word8.fromInt 0)
      val lhs = Word64.>> (x, 0w32)
      val rhs = Word64.andb (x, rhs_mask)
    in
      (
	PackWord32Big.update (a, 0, Word64.toLarge lhs);
	PackWord32Big.update (a, 1, Word64.toLarge rhs);
	Word8Array.vector a
      )
    end

fun deserialize v =
    let
      val lhs = LargeWord.<< (PackWord32Big.subVec (v, 0), 0w32)
      val rhs = PackWord32Big.subVec (v, 1)
    in
      Word64.fromLargeWord (LargeWord.+ (lhs, rhs))
    end
end


structure SerInt : SERDE =
struct
type from = Int.int
type to = Word8Vector.vector

val serialize =  SerWord64.serialize o Word64.fromInt
val deserialize = Word64.toIntX o SerWord64.deserialize
end
