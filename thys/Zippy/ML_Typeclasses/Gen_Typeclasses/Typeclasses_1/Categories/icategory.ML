(*  Title:  icategory.ML
    Author: Kevin Kappelmann

Basic indexed typeclasses related to category theory,
inspired by the Haskell Prelude and "Parameterised Notions of Computation" by Robert Atkey.
*)
signature \<^eval>\<open>sfx_ParaT_nargs "ISEMI_CATEGORY_BASE"\<close> =
sig
  type (@{ParaT_args} 'i, 'o, 'a, 'b) morph
  type (@{ParaT_args} 'i, 'o, 'a) emorph = (@{ParaT_args} 'i, 'o, 'a, 'a) morph
  val comp : (@{ParaT_args} 'j, 'k, 'b, 'c) morph -> (@{ParaT_args} 'i, 'j, 'a, 'b) morph ->
    (@{ParaT_args} 'i, 'k, 'a, 'c) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "ISEMI_CATEGORY"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ISEMI_CATEGORY_BASE"\<close>
  val >>> : (@{ParaT_args} 'i, 'j, 'a, 'b) morph * (@{ParaT_args} 'j, 'k, 'b, 'c) morph ->
    (@{ParaT_args} 'i, 'k, 'a, 'c) morph
end

functor \<^eval>\<open>sfx_ParaT_nargs "ISemi_Category"\<close>(
    C : \<^eval>\<open>sfx_ParaT_nargs "ISEMI_CATEGORY_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "ISEMI_CATEGORY"\<close> =
struct
open C
fun f >>> g = comp g f
end

signature \<^eval>\<open>sfx_ParaT_nargs "ICATEGORY_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ISEMI_CATEGORY_BASE"\<close>
  (*unit argument to fight ML's value restriction*)
  val id : unit -> (@{ParaT_args} 'i, 'i, 'a) emorph
end

signature \<^eval>\<open>sfx_ParaT_nargs "ICATEGORY"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ICATEGORY_BASE"\<close>
  val repeatn : int -> (@{ParaT_args} 'i, 'i, 'a) emorph -> (@{ParaT_args} 'i, 'i, 'a) emorph
end

functor \<^eval>\<open>sfx_ParaT_nargs "ICategory"\<close>(C : \<^eval>\<open>sfx_ParaT_nargs "ICATEGORY_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "ICATEGORY"\<close> =
struct
open C
fun repeatn n f = if n <= 0 then id () else comp (repeatn (n - 1) f) f
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ICATEGORY_BASE"\<close>
  val arr : ('a -> 'b) -> (@{ParaT_args} 'i, 'i, 'a, 'b) morph
  val *** : (@{ParaT_args} 'i, 'j, 'a, 'b) morph * (@{ParaT_args} 'j, 'k, 'c, 'd) morph ->
    (@{ParaT_args} 'i, 'k, ('a * 'c), ('b * 'd)) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW"\<close> =
sig
include \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close>

val first : (@{ParaT_args} 'i, 'o, 'a, 'b) morph -> (@{ParaT_args} 'i, 'o, ('a * 'c), ('b * 'c)) morph
val second : (@{ParaT_args} 'i, 'o, 'a, 'b) morph -> (@{ParaT_args} 'i, 'o, ('c * 'a), ('c * 'b)) morph

val &&& : (@{ParaT_args} 'i, 'j, 'a, 'b) morph * (@{ParaT_args} 'j, 'k, 'a, 'c) morph ->
  (@{ParaT_args} 'i, 'k, 'a, 'b * 'c) morph

val K : 'a -> (@{ParaT_args} 'i, 'i, 'b, 'a) morph
val curry : (@{ParaT_args} 'i, 'o, 'a * 'b, 'c) morph -> 'a -> (@{ParaT_args} 'i, 'o, 'b, 'c) morph
end

functor \<^eval>\<open>sfx_ParaT_nargs "IArrow"\<close>(A : \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "IARROW"\<close> =
struct

open A
fun first f = f *** id ()
fun second f = id () *** f

fun f &&& g = comp (f *** g) (arr (fn b => (b, b)))

fun K x = arr (fn _ => x)
fun curry m i = comp m (K i &&& id ())

end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_APPLY_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close>
  val app : (@{ParaT_args} 'i, 'j, (@{ParaT_args} 'i, 'j, 'a, 'b) morph * 'a, 'b) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_APPLY"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_APPLY_BASE"\<close>
  val uncurry : ('a -> (@{ParaT_args} 'i, 'j, 'b, 'c) morph) ->
    (@{ParaT_args} 'i, 'j, 'a * 'b, 'c) morph
  val app' : 'a -> (@{ParaT_args} 'i, 'j, (@{ParaT_args} 'i, 'j, 'a, 'b) morph, 'b) morph
end

functor \<^eval>\<open>sfx_ParaT_nargs "IArrow_Apply"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "IARROW_APPLY_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IARROW_APPLY"\<close> =
struct
open A
local structure SC = \<^eval>\<open>sfx_ParaT_nargs "ISemi_Category"\<close>(A) open SC
in
fun uncurry f = arr (apfst f) >>> app
fun app' x = arr (rpair x) >>> app
end
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_ZERO_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close>
  val zero : unit -> (@{ParaT_args} 'i, 'i, 'a, 'b) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_PLUS_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_ZERO_BASE"\<close>
  val plus : (@{ParaT_args} 'i, 'j, 'a, 'b) morph -> (@{ParaT_args} 'i, 'j, 'a, 'b) morph ->
    (@{ParaT_args} 'i, 'j, 'a, 'b) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_OR_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_ZERO_BASE"\<close>
  val or : (@{ParaT_args} 'i, 'j, 'a, 'b) morph -> (@{ParaT_args} 'i, 'j, 'a, 'b) morph ->
    (@{ParaT_args} 'i, 'j, 'a, 'b) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close>
  type @{ParaT_args encl: "(" ")"} exn

  val throw : (@{ParaT_args} 'i, 'i, @{ParaT_args encl: "(" ")"} exn, 'a) morph
  val catch : (@{ParaT_args} 'i, 'j, 'a, 'b) morph ->
    (@{ParaT_args} 'i, 'j, 'a * @{ParaT_args encl: "(" ")"} exn, 'b) morph ->
    (@{ParaT_args} 'i, 'j, 'a, 'b) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION_BASE"\<close>
  val throw' : @{ParaT_args encl: "(" ")"} exn -> (@{ParaT_args} 'i, 'i, 'a, 'b) morph
  val catch' : (@{ParaT_args} 'i, 'j, 'a, 'b) morph -> (@{ParaT_args} 'i, 'j, 'a, 'b) morph ->
    (@{ParaT_args} 'i, 'j, 'a, 'b) morph
  val try : (@{ParaT_args} 'i, 'i, 'a) emorph -> (@{ParaT_args} 'i, 'i, 'a) emorph
end

functor \<^eval>\<open>sfx_ParaT_nargs "IArrow_Exception"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION"\<close> =
struct
open A

fun throw' x = comp throw (arr (K x))
fun catch' f g = catch f (comp g (arr fst))
fun try f = catch' f (id ())
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_CHOICE_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close>
  val cases : (@{ParaT_args} 'i, 'j, 'a, 'c) morph -> (@{ParaT_args} 'i, 'j, 'b, 'd) morph ->
    (@{ParaT_args} 'i, 'j, ('a, 'b) Either.either, ('c, 'd) Either.either) morph
  val merge : (@{ParaT_args} 'i, 'j, 'a, 'c) morph -> (@{ParaT_args} 'i, 'j, 'b, 'c) morph ->
    (@{ParaT_args} 'i, 'j, ('a, 'b) Either.either, 'c) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_CHOICE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_CHOICE_BASE"\<close>
  val opt : (@{ParaT_args} 'i, 'j, unit, 'b) morph -> (@{ParaT_args} 'i, 'j, 'a, 'b) morph ->
    (@{ParaT_args} 'i, 'j, 'a option, 'b) morph
end

functor \<^eval>\<open>sfx_ParaT_nargs "IArrow_Choice"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "IARROW_CHOICE_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IARROW_CHOICE"\<close> =
struct
open A
fun opt fnone fsome = comp (merge fnone fsome) (arr Either.of_opt)
end
