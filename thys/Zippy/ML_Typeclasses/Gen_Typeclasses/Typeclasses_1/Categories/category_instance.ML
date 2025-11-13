(*  Title:  category_instance.ML
    Author: Kevin Kappelmann

Instances of categories.
*)
(*standard function space*)
structure \<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply"\<close>
  : \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY_BASE"\<close> =
struct

type (@{ParaT_args} 'a, 'b) morph = 'a -> 'b
type (@{ParaT_args} 'a) emorph = (@{ParaT_args} 'a, 'a) morph
fun id _ = I
fun comp f g x = f (g x)
val arr = I
fun (f *** g) (x, y) = (f x, g y)
fun app (f, x) = f x

end

structure \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply"\<close>
  : \<^eval>\<open>sfx_ParaT_nargs "ARROW_ARROW_APPLY"\<close> =
struct
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(\<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply"\<close>)
  structure AA = \<^eval>\<open>sfx_ParaT_nargs "Arrow_Apply"\<close>(\<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply"\<close>)
end

(*Kleisli category*)
signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close> =
sig
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  type (@{ParaT_args} 'a, 'b) kleisli = 'a -> (@{ParaT_args} 'b) M.t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close> =
struct
structure M = M
type (@{ParaT_args} 'a, 'b) kleisli = 'a -> (@{ParaT_args} 'b) M.t
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY_BASE"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY_BASE"\<close> =
struct

open M
structure K = \<^eval>\<open>sfx_ParaT_nargs "Kleisli"\<close>(M)
open K

type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) kleisli
type (@{ParaT_args} 'a) emorph = (@{ParaT_args} 'a, 'a) morph
fun id _ = pure
local structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M) open M
in
fun comp k1 k2 x = k2 x >>= k1
fun arr f = pure o f
fun k1 *** k2 = (fn (x, y) => k1 x
  >>= (fn x' => k2 y
  >>= (fn y' => pure (x', y'))))
fun app (f, x) = f x
end

end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close> =
struct

structure K = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(M)
open K

fun first f (x, y) = M.bind (f x) (rpair y #> M.pure)
fun second f (x, y) = M.bind (f y) (pair x #> M.pure)
fun (f &&& g) x = M.bind (f x) (fn y1 => M.bind (g x) (fn y2 => M.pure (y1, y2)))
fun K x _ = M.pure x
fun curry f x y = f (x, y)

end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY"\<close> =
struct

structure K = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(M)
open K
fun app' x f = f x
fun uncurry f (x, y) = f x y

end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_ARROW_APPLY"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_ARROW_APPLY"\<close>
  where type (@{ParaT_args} 'a, 'b) A.morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_ARROW_APPLY"\<close> =
struct
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M)
  structure K = A.K
  structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(M)
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_ZERO_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_ZERO_BASE"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Zero"\<close>(
    MZ : \<^eval>\<open>sfx_ParaT_nargs "MONAD_ZERO_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_ZERO_BASE"\<close> =
struct
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(MZ)
open AA
fun zero _ _ = MZ.zero ()
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_PLUS_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_PLUS_BASE"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Plus_Base"\<close>(
    MP : \<^eval>\<open>sfx_ParaT_nargs "MONAD_PLUS_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_PLUS_BASE"\<close> =
struct
structure AZ = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Zero"\<close>(MP)
open AZ
fun plus f g x = MP.plus_lazy (f x) (fn _ => g x)
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_OR_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_OR_BASE"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Or_Base"\<close>(
    MO : \<^eval>\<open>sfx_ParaT_nargs "MONAD_OR_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_OR_BASE"\<close> =
struct
structure AZ = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Zero"\<close>(MO)
open AZ
fun or f g x = MO.or_lazy (f x) (fn _ => g x)
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION_BASE"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Base"\<close>(
    ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_BASE"\<close> =
struct
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(ME)
open AA
type @{ParaT_args encl: "(" ")"} exn = @{ParaT_args encl: "(" ")"} ME.exn
val throw = ME.throw
fun catch f g x = ME.catch (f x) (g o pair x)
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception"\<close>(
    ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close> =
struct
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Base"\<close>(ME)
open AE
fun throw' exn _ = ME.throw exn
fun catch' f g x = ME.catch (f x) (fn _ => g x)
fun try f = catch' f (id ())
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_CHOICE_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_CHOICE_BASE"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Choice_Base"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_CHOICE_BASE"\<close> =
struct
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(M)
open AA
fun cases f _ (Either.Left x) = M.map Either.Left (f x)
  | cases _ g (Either.Right y) = M.map Either.Right (g y)
fun merge f _ (Either.Left x) = f x
  | merge _ g (Either.Right y) = g y
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_CHOICE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_CHOICE"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Choice"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_CHOICE"\<close> =
struct
structure AC = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Choice_Base"\<close>(M)
open AC
fun opt f _ NONE = f ()
  | opt _ g (SOME x) = g x
end

functor \<^eval>\<open>sfx_ParaT_nargs "Applicative_Arrow"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close> =
struct
open A
type (@{ParaT_args} 'a) t = (@{ParaT_args} unit, 'a) morph
fun map f = comp (arr f)
fun pure x = arr (Library.K x)
fun f <*> x = comp (arr (uncurry I)) (comp (f *** x) (arr (fn b => (b, b))))
end

functor \<^eval>\<open>sfx_ParaT_nargs "Monad_Arrow_Apply"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close> =
struct
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Applicative_Arrow"\<close>(A)
open A AA
fun bind m f = comp app (comp (arr (fn x => (f x, ()))) m)
end
