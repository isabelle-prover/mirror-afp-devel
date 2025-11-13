(*  Title:      Zippy/glist.ML
    Author:     Kevin Kappelmann

Generalised lists.
*)
signature \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close> =
sig
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>

  type 'a t
  val empty : 'a t
  val cons : 'a -> 'a t -> 'a t
  val from_list : 'a list -> 'a t

  val is_empty : 'a t -> bool
  val dest : 'a t -> (@{ParaT_args} 'a * 'a t) M.t
  val foldl : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val nth : 'a t -> int -> (@{ParaT_args} 'a) M.t
  val length : 'a t -> int
end

functor \<^eval>\<open>sfx_ParaT_nargs "GList"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    where type @{ParaT_args encl: "(" ")"} exn = unit
  ) : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close> where type 'a t = 'a list =
struct
  structure M = M
  type 'a t = 'a list
  val empty = []
  val is_empty = null
  val foldl = fold
  val cons = cons
  fun dest [] = M.throw ()
    | dest (x :: xs) = M.pure (x, xs)
  val from_list = I
  fun nth xs n = nth xs n handle Subscript => M.throw ()
  val length =length
end