(* Iteration Combinator for Floyd-Warshall SP *)
signature SP_ITER = sig
  structure M : MATRIX

  val close: 'a M.matrix -> (int * int * int * 'a) Iter.t
end

functor SPIter(M : MATRIX) : SP_ITER = struct
structure M = M
structure MIter = MatrixIter(M)

open Iter
fun close m = to_n (M.dim m) ** MIter.do_ij m
                   <$> (fn k & (i, j, elem) => (k, i, j, elem))
end
