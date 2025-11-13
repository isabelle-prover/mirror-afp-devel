(*  Title:  itypeclass_base.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses (in Atkey-style),
inspired by the Haskell Prelude and "Parameterised Notions of Computation" by Robert Atkey.
*)
signature \<^eval>\<open>sfx_ParaT_nargs "IFUNCTOR_BASE"\<close> =
sig
  type (@{ParaT_args} 'i, 'o, 'a) t
  (*TODO: should we also require contravariance in first and covariance in second parameter?
  cf. paper by Atkey*)
  val map : ('a -> 'b) -> (@{ParaT_args} 'i, 'o, 'a) t -> (@{ParaT_args} 'i, 'o, 'b) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "IFUNCTOR"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IFUNCTOR_BASE"\<close>
  val <&> : (@{ParaT_args} 'i, 'o, 'a) t * ('a -> 'b) -> (@{ParaT_args} 'i, 'o, 'b) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "IFunctor"\<close>(F : \<^eval>\<open>sfx_ParaT_nargs "IFUNCTOR_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "IFUNCTOR"\<close> =
struct
open F
fun x <&> f = map f x
end

signature \<^eval>\<open>sfx_ParaT_nargs "IFUNCTOR_TRANS"\<close> =
sig
  (*the base functor to transform*)
  structure F : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IFUNCTOR_BASE"\<close>
  val lift : (@{ParaT_args} 'a) F.t -> (@{ParaT_args} 'i, 'i, 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "IAPPLICATIVE_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IFUNCTOR_BASE"\<close>
  val pure : 'a -> (@{ParaT_args} 'i, 'i, 'a) t
  val <*> : (@{ParaT_args} 'i, 'j, 'a -> 'b) t * (@{ParaT_args} 'j, 'k, 'a) t ->
    (@{ParaT_args} 'i, 'k, 'b) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IAPPLICATIVE_BASE"\<close>
  val bind : (@{ParaT_args} 'i, 'j, 'a) t -> ('a -> (@{ParaT_args} 'j, 'k, 'b) t) ->
    (@{ParaT_args} 'i, 'k, 'b) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "IMONAD"\<close> =
sig
include \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>
  val >>= : (@{ParaT_args} 'i, 'j, 'a) t * ('a -> (@{ParaT_args} 'j, 'k, 'b) t) ->
    (@{ParaT_args} 'i, 'k, 'b) t
  val join : (@{ParaT_args} 'i, 'j, (@{ParaT_args} 'j, 'k, 'a) t) t -> (@{ParaT_args} 'i, 'k, 'a) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "IMonad"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "IMONAD"\<close> =
struct
open M
fun m >>= f = bind m f
fun join x = bind x I
end

signature \<^eval>\<open>sfx_ParaT_nargs "IMONAD_TRANS"\<close> =
sig
  (*the base monad to transform*)
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>

  val lift : (@{ParaT_args} 'a) M.t -> (@{ParaT_args} 'i, 'i, 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "IMONAD_ZERO_BASE"\<close> =
sig
include \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>
val zero : unit -> (@{ParaT_args} 'i, 'i, 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "IMONAD_PLUS_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IMONAD_ZERO_BASE"\<close>
  (*satisfies left distribution law: "plus x y >>= f = plus (x >>= f) (y >>= f)"*)
  val plus_lazy : (@{ParaT_args} 'i, 'j, 'a) t -> (unit -> (@{ParaT_args} 'i, 'j, 'a) t) ->
    (@{ParaT_args} 'i, 'j, 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "IMONAD_OR_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IMONAD_ZERO_BASE"\<close>
  (*satisfies left catch law: "or (pure x) y = pure x"*)
  val or_lazy : (@{ParaT_args} 'i, 'j, 'a) t -> (unit -> (@{ParaT_args} 'i, 'j, 'a) t) ->
    (@{ParaT_args} 'i, 'j, 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "IMONAD_EXCEPTION_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>
  type @{ParaT_args encl: "(" ")"} exn
  val throw : @{ParaT_args encl: "(" ")"} exn -> (@{ParaT_args} 'i, 'i, 'a) t
  val catch : (@{ParaT_args} 'i, 'j, 'a) t -> (@{ParaT_args encl: "(" ")"} exn ->
    (@{ParaT_args} 'i, 'j, 'a) t) -> (@{ParaT_args} 'i, 'j, 'a) t
end
