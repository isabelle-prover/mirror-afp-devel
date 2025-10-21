(* Iteration Signature for two dimensional Matrices *)
signature MATRIX_ITER = sig
  structure M : MATRIX

  val do_ij: 'a M.matrix -> (int * int * 'a) Iter.t
end

functor MatrixIter(M : MATRIX) : MATRIX_ITER = struct
structure M = M

fun do_ij x = flip M.appij x
end
