(*  Title:  typeclass_base.ML
    Author: Kevin Kappelmann

Basic typeclasses inspired by the Haskell Prelude, monad-transformers, and the mtl package.

For an explanation of the @{ParaT_args} arguments, see the paper
"Zippy - Generic White-Box Proof Search with Zippers".
*)
infix 1 <*>
infix 1 >>=
infix 1 <&>

signature \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close> =
sig
  type (@{ParaT_args} 'a) t
  val map : ('a -> 'b) -> (@{ParaT_args} 'a) t -> (@{ParaT_args} 'b) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>
  val <&> : (@{ParaT_args} 'a) t * ('a -> 'b) -> (@{ParaT_args} 'b) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Functor"\<close>(F : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR"\<close> =
struct

open F
fun x <&> f = map f x

end

signature \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_TRANS"\<close> =
sig
  (*the base functor to transform*)
  structure F : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>
  val lift : (@{ParaT_args} 'a) F.t -> (@{ParaT_args} 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>
  val pure : 'a -> (@{ParaT_args} 'a) t
  val <*> : (@{ParaT_args} 'a -> 'b) t * (@{ParaT_args} 'a) t -> (@{ParaT_args} 'b) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>
  val liftA2 : ('a -> 'b -> 'c) -> (@{ParaT_args} 'a) t -> (@{ParaT_args} 'b) t -> (@{ParaT_args} 'c) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Applicative"\<close>(A : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE"\<close> =
struct

open A
fun liftA2 f x = curry (op <*>) (A.map f x)

end

signature \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_TRANS"\<close> =
sig
  (*the base applicative to transform*)
  structure A : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>
  val lift : (@{ParaT_args} 'a) A.t -> (@{ParaT_args} 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>
  val bind : (@{ParaT_args} 'a) t -> ('a -> (@{ParaT_args} 'b) t) -> (@{ParaT_args} 'b) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  val >>= : (@{ParaT_args} 'a) t * ('a -> (@{ParaT_args} 'b) t) -> (@{ParaT_args} 'b) t
  val join : (@{ParaT_args} (@{ParaT_args} 'a) t) t -> (@{ParaT_args} 'a) t
  val flat1 : (@{ParaT_args} 'a -> (@{ParaT_args} 'b) t) t -> 'a -> (@{ParaT_args} 'b) t
  val flat2 : (@{ParaT_args} 'a -> 'b -> (@{ParaT_args} 'c) t) t -> 'a -> 'b -> (@{ParaT_args} 'c) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "MONAD"\<close> =
struct

open M
fun x >>= f = bind x f
fun join x = x >>= I
fun flat1 fm x = fm >>= (fn f => f x)
fun flat2 fm x = M.map (fn f => f x) fm |> flat1

end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_TRANS"\<close> =
sig
  (*the base monad to transform*)
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>

  val lift : (@{ParaT_args} 'a) M.t -> (@{ParaT_args} 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "ALTERNATIVE_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>
  (*laws: (empty, <|>) forms a monoid on (@{ParaT_args} 'a) t*)
  val empty : unit -> (@{ParaT_args} 'a) t
  val <|> : (@{ParaT_args} 'a) t -> (@{ParaT_args} 'a) t -> (@{ParaT_args} 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "ALTERNATIVE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ALTERNATIVE_BASE"\<close>
  val optional : (@{ParaT_args} 'a) t -> (@{ParaT_args} 'a option) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Alternative"\<close>(A : \<^eval>\<open>sfx_ParaT_nargs "ALTERNATIVE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "ALTERNATIVE"\<close> =
struct

open A
fun optional x = A.<|> (A.map SOME x) (A.pure NONE)

end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_ZERO_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  val zero : unit -> (@{ParaT_args} 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_PLUS_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_ZERO_BASE"\<close>
  (*satisfies left distribution law: "plus x y >>= f = plus (x >>= f) (y >>= f)"*)
  val plus_lazy : (@{ParaT_args} 'a) t -> (unit -> (@{ParaT_args} 'a) t) -> (@{ParaT_args} 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_PLUS"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_PLUS_BASE"\<close>
  val plus : (@{ParaT_args} 'a) t -> (@{ParaT_args} 'a) t -> (@{ParaT_args} 'a) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Monad_Plus"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_PLUS_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "MONAD_PLUS"\<close> =
struct
  open M
  fun plus x y = M.plus_lazy x (K y)
end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_OR_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_ZERO_BASE"\<close>
  (*satisfies left catch law: "or (pure x) y = pure x"*)
  val or_lazy : (@{ParaT_args} 'a) t -> (unit -> (@{ParaT_args} 'a) t) -> (@{ParaT_args} 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_OR"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_OR_BASE"\<close>
  val or : (@{ParaT_args} 'a) t -> (@{ParaT_args} 'a) t -> (@{ParaT_args} 'a) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Monad_Or"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_OR_BASE"\<close>) :
  \<^eval>\<open>sfx_ParaT_nargs "MONAD_OR"\<close> =
struct
  open M
  fun or x y = M.or_lazy x (K y)
end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  type @{ParaT_args encl: "(" ")"} exn
  val throw : @{ParaT_args encl: "(" ")"} exn -> (@{ParaT_args} 'a) t
  val catch : (@{ParaT_args} 'a) t -> (@{ParaT_args encl: "(" ")"} exn ->
    (@{ParaT_args} 'a) t) -> (@{ParaT_args} 'a) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close> =
sig
  type (@{ParaT_args} 'a) f
  val foldl : ('a -> 'b -> 'b) -> (@{ParaT_args} 'a) f -> 'b -> 'b
  val foldr : ('a -> 'b -> 'b) -> (@{ParaT_args} 'a) f -> 'b -> 'b
end

signature \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_MONAD"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close>
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>

  val foldlM : ('a -> 'b -> (@{ParaT_args} 'b) M.t) ->
    (@{ParaT_args} 'a) f -> 'b -> (@{ParaT_args} 'b) M.t
  val foldrM : ('a -> 'b -> (@{ParaT_args} 'b) M.t) ->
    (@{ParaT_args} 'a) f -> 'b -> (@{ParaT_args} 'b) M.t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Foldable_Monad"\<close>(
    structure F : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close>
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_MONAD"\<close> =
struct

open F
structure M = M

fun foldlM f xs acc = let fun c x k acc = M.bind (f x acc) k
  in foldr c xs M.pure acc end

fun foldrM f xs acc = let fun c x k acc = M.bind (f x acc) k
  in foldl c xs M.pure acc end

end

signature \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close>
  sharing type t = f

  structure A : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>

  val traverse : ('a -> (@{ParaT_args} 'b) A.t) -> (@{ParaT_args} 'a) t ->
    (@{ParaT_args} (@{ParaT_args} 'b) t) A.t
end

signature \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>
  val sequence : (@{ParaT_args} (@{ParaT_args} 'a) A.t) t -> (@{ParaT_args} (@{ParaT_args} 'a) t) A.t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Traversable"\<close>(T : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE"\<close> =
struct

open T
fun sequence x = traverse I x

end

signature \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_TRANS"\<close> =
sig
  (*the base traversable to transform*)
  structure T : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>
  val lift : (@{ParaT_args} 'a) T.t -> (@{ParaT_args} 'a) t
end

