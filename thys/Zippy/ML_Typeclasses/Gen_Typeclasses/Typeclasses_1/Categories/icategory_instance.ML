(*  Title:  icategory_instance.ML
    Author: Kevin Kappelmann

Instances of indexed categories.
*)

(*Indexed Kleisli category*)
signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close> =
sig
  structure M : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>
  type (@{ParaT_args} 'i, 'o, 'a, 'b) kleisli = 'a -> (@{ParaT_args} 'i, 'o, 'b) M.t
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close> =
struct
structure M = M
type (@{ParaT_args} 'i, 'o, 'a, 'b) kleisli = 'a -> (@{ParaT_args} 'i, 'o, 'b) M.t
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_APPLY_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_APPLY_BASE"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Apply_Base"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_APPLY_BASE"\<close> =
struct

open M
structure K = \<^eval>\<open>sfx_ParaT_nargs "IKleisli"\<close>(M)
open K

type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) kleisli
type (@{ParaT_args} 'i, 'o, 'a) emorph = (@{ParaT_args} 'i, 'o, 'a, 'a) morph
fun id _ = pure
local structure M = \<^eval>\<open>sfx_ParaT_nargs "IMonad"\<close>(M) open M
in
fun comp k1 k2 x = k2 x >>= k1
fun arr f = pure o f
fun k1 *** k2 = (fn (x, y) => k1 x
  >>= (fn x' => k2 y
  >>= (fn y' => pure (x', y'))))
fun app (f, x) = f x
end

end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW"\<close> =
struct

structure K = \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Apply_Base"\<close>(M)
open K

fun first f (x, y) = M.bind (f x) (rpair y #> M.pure)
fun second f (x, y) = M.bind (f y) (pair x #> M.pure)
fun (f &&& g) x = M.bind (f x) (fn y1 => M.bind (g x) (fn y2 => M.pure (y1, y2)))
fun K x _ = M.pure x
fun curry f x y = f (x, y)

end


signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_ZERO_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_ZERO_BASE"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Zero"\<close>(
    MZ : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_ZERO_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_ZERO_BASE"\<close> =
struct
structure AA = \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Apply_Base"\<close>(MZ)
open AA
fun zero _ _ = MZ.zero ()
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_PLUS_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_PLUS_BASE"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Plus_Base"\<close>(
    MP : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_PLUS_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_PLUS_BASE"\<close> =
struct
structure AZ = \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Zero"\<close>(MP)
open AZ
fun plus f g x = MP.plus_lazy (f x) (fn _ => g x)
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_OR_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_OR_BASE"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Or_Base"\<close>(
    MO : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_OR_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_OR_BASE"\<close> =
struct
structure AZ = \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Zero"\<close>(MO)
open AZ
fun or f g x = MO.or_lazy (f x) (fn _ => g x)
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION_BASE"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Exception_Base"\<close>(
    ME : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_EXCEPTION_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION_BASE"\<close> =
struct
structure AA = \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Apply_Base"\<close>(ME)
open AA
type @{ParaT_args encl: "(" ")"} exn = @{ParaT_args encl: "(" ")"} ME.exn
val throw = ME.throw
fun catch f g x = ME.catch (f x) (g o pair x)
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_CHOICE_BASE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_CHOICE_BASE"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Choice_Base"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_CHOICE_BASE"\<close> =
struct
structure AA = \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Apply_Base"\<close>(M)
open AA
fun cases f _ (Either.Left x) = M.map Either.Left (f x)
  | cases _ g (Either.Right y) = M.map Either.Right (g y)
fun merge f _ (Either.Left x) = f x
  | merge _ g (Either.Right y) = g y
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_CHOICE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_CHOICE"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Choice"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_CHOICE"\<close> =
struct
structure AC = \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Choice_Base"\<close>(M)
open AC
fun opt f _ NONE = f ()
  | opt _ g (SOME x) = g x
end

functor \<^eval>\<open>sfx_ParaT_nargs "IApplicative_Arrow"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IAPPLICATIVE_BASE"\<close> =
struct
open A
type (@{ParaT_args} 'i, 'j, 'a) t = (@{ParaT_args} 'i, 'j, unit, 'a) morph
fun map f = comp (arr f)
fun pure x = arr (Library.K x)
fun f <*> x = comp (arr (uncurry I)) (comp (f *** x) (arr (fn b => (b, b))))
end

functor \<^eval>\<open>sfx_ParaT_nargs "IMonad_Arrow_Apply"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "IARROW_APPLY_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_BASE"\<close> =
struct
structure AA = \<^eval>\<open>sfx_ParaT_nargs "IApplicative_Arrow"\<close>(A)
open A AA
fun bind m f = comp app (comp (arr (fn x => (f x, ()))) m)
end

