(* Iteration Combinators for DBM functions  *)
signature DBM_ITER = sig
  structure M : MATRIX

  val close: 'a M.matrix -> (int * int * int * 'a) Iter.t
  val copy_clock: int -> int -> 'a M.matrix -> (int * int * 'a * 'a) Iter.t
  val free: int -> 'a M.matrix -> (int * int * 'a) Iter.t
  val up: 'a M.matrix -> int Iter.t
  val reset: int -> 'a M.matrix -> (int * int * 'a * 'a) Iter.t
  val shift: int -> 'a M.matrix -> (int * int * 'a * 'a) Iter.t
  val And: 'a M.matrix -> (int * int) Iter.t
  val norm_k: 'a M.matrix -> (int * int  * 'a) Iter.t
end

functor DBMIter(M : MATRIX) : DBM_ITER = struct
structure M = M
structure MIter = MatrixIter(M)
structure SP = SPIter(M)
open Iter

fun close m = SP.close m
fun up dbm = 1 to M.dim dbm
fun reset x dbm = to_n (M.dim dbm) <$> (fn i => (x, i, M.sub 0 i dbm, M.sub i 0 dbm))
fun i_neq_x x dbm = to_n (M.dim dbm) when (fn i => i <> x)
fun copy_clock x y dbm =
    i_neq_x x dbm <$> (fn i => (x, i, M.sub y i dbm , M.sub i y dbm))
fun free x dbm = i_neq_x x dbm <$> (fn i => (x, i, M.sub i 0 dbm ))
fun shift x dbm = i_neq_x x dbm <$> (fn i => (x, i, M.sub x i dbm , M.sub i x dbm))
fun And dbm = let val n = M.dim dbm in to_n n <*> to_n n end
val norm_k = MIter.do_ij
end

structure DBMLnIter = DBMIter(LnLayoutMatrix)
