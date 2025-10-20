signature SLICE_MATRIX = sig
  structure M : MATRIX
  type region = {
    row : int,
    col : int,
    ncols : int option,
    nrows : int option
  }
  type 'a slice
  val slice: 'a M.matrix -> region -> ('a slice) option
  val modify: 'a slice -> (int * int * 'a -> 'a) -> unit
  val update: 'a slice -> ('a -> 'a) -> unit
end

functor SliceMatrix(M : MATRIX) = struct
structure M = M
type region = {
  row : int,
  col : int,
  ncols : int option,
  nrows : int option
}

type 'a slice = {
  base : 'a M.matrix,
  reg : region
}

fun slice (reg as {row, col, nrows, ncols} : region) mat =
    let
      val dim = M.dim mat
      fun continue x = Option.mapPartial (K x)
      fun check_single n =
          if n < 0 orelse n > dim then NONE
          else SOME n
      fun check_n start n =
          check_single start
          |> continue (check_single (start + n))
      fun check_opt_n start n =
          case n of
              NONE => check_single start |
              SOME n => check_n start n
    in
      check_opt_n row nrows
      |> continue (check_opt_n col ncols)
      |> continue (SOME {base = mat, reg = reg})
    end

fun indices {row, col, nrows, ncols} base =
    let
      val dim = M.dim base
      fun get_last start n =
          case n of
              NONE => dim |
              SOME n => start + n
      val last_row = get_last row nrows
      val last_col = get_last col ncols
      open Iter
    in
      (row to last_row) <*> (col to last_col)
      <$> (fn (i, j) => (i, j, M.sub i j base))
    end

fun modify ({base, reg} : 'a slice) f =
    let
      val ixs = indices reg base
      fun upd f (arg as (i, j, _)) =
          M.update i j (f arg) base
    in
      Iter.for ixs (upd f)
    end

fun update slice f =
    modify slice (fn (_, _, x) => f x)
end
