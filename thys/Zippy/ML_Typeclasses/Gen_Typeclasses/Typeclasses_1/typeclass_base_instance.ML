(*  Title:  typeclass_base_instance.ML
    Author: Kevin Kappelmann

Instances of basic typeclasses.
*)
structure \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close> : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close> =
struct

type (@{ParaT_args} 'a) t = 'a
fun map f x = f x
fun pure x = x
fun f <*> x = f x
fun bind x f = f x

end

structure \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close> : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close> =
struct

type (@{ParaT_args} 'a) f = 'a
fun foldl f x acc = f x acc
fun foldr f x acc = f x acc

end

functor \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close> =
struct

open \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>
open \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>

structure A = A
fun traverse f x = f x
end

functor \<^eval>\<open>sfx_ParaT_nargs "List_Functor_Trans"\<close>(F : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_TRANS"\<close> =
struct

structure F = F

type (@{ParaT_args} 'a) t = (@{ParaT_args} 'a list) F.t
fun lift x = F.map single x
fun map f = F.map (List.map f)

end

functor \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(F : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close> =
struct

type (@{ParaT_args} 'a) f = (@{ParaT_args} 'a list) F.f

fun fold_base _ [] = I
  | fold_base step (x :: xs) = step (fold_base step xs) x

fun foldl f = F.foldl (fold_base (fn frec => frec oo f))
fun foldr f = F.foldr (fold_base (fn frec => fn x => f x o frec))

end

functor \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
    T : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_TRANS"\<close> =
struct

structure T = T
structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Functor_Trans"\<close>(T)
open F
structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(T)
open F
structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)

structure A = \<^eval>\<open>sfx_ParaT_nargs "Applicative"\<close>(T.A)
fun traverse f = T.traverse (fn xs => F.foldr (A.liftA2 cons o f) xs (A.pure []))
end

functor \<^eval>\<open>sfx_ParaT_nargs "List_Applicative_Trans"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_TRANS"\<close> =
struct

structure A = A
structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Functor_Trans"\<close>(A)
open F

structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Functor_Trans"\<close>(\<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>)

fun pure x = A.pure (single x)

local structure A = \<^eval>\<open>sfx_ParaT_nargs "Applicative"\<close>(A); open A
in
fun f <*> x = A.<*> (A.map (fn f => fn x => maps (fn f => List.map f x) f) f, x)
end
end

(*Note: only forms a monad if the underlying monad is commutative;
cf. https://wiki.haskell.org/ListT_done_right*)
functor \<^eval>\<open>sfx_ParaT_nargs "List_Monad_Trans"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "MONAD_TRANS"\<close> =
struct

structure M = M
structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Functor_Trans"\<close>(M)
open F

structure T = \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(M))

fun pure x = M.pure (single x)

local structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M) open M
in
fun f <*> x = x >>= (fn x => f >>= (maps (fn f => List.map f x) #> M.pure))

fun bind x f = x >>= (fn x => T.traverse f x >>= (flat #> M.pure))
end
end

(*Note: all caveats for lists transformers also apply to seq transformers*)
functor \<^eval>\<open>sfx_ParaT_nargs "Seq_Functor_Trans"\<close>(F : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_TRANS"\<close> =
struct

structure F = F

type (@{ParaT_args} 'a) t = (@{ParaT_args} 'a Seq.seq) F.t
fun lift x = F.map Seq.single x
fun map f = F.map (Seq.map f)

end

functor \<^eval>\<open>sfx_ParaT_nargs "Seq_Applicative_Trans"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "APPLICATIVE_TRANS"\<close> =
struct

structure A = A
structure F = \<^eval>\<open>sfx_ParaT_nargs "Seq_Functor_Trans"\<close>(A)
open F

structure F = \<^eval>\<open>sfx_ParaT_nargs "Seq_Functor_Trans"\<close>(\<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>)

fun pure x = A.pure (Seq.single x)

local structure A = \<^eval>\<open>sfx_ParaT_nargs "Applicative"\<close>(A); open A
in
fun f <*> x = A.<*> (A.map (fn f => fn x => Seq.maps (fn f => Seq.map f x) f) f, x)
end
end

functor \<^eval>\<open>sfx_ParaT_nargs "Seq_Foldable_Trans"\<close>(F : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close> =
struct

type (@{ParaT_args} 'a) f = (@{ParaT_args} 'a Seq.seq) F.f

fun fold_base step sq acc = case Seq.pull sq of
    SOME (x, sq) => step (fold_base step sq) x acc
  | NONE => acc

fun foldl f = F.foldl (fold_base (fn frec => frec oo f))
fun foldr f = F.foldr (fold_base (fn frec => fn x => f x o frec))
end

functor \<^eval>\<open>sfx_ParaT_nargs "Seq_Traversable_Trans"\<close>(
    T : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_TRANS"\<close> =
struct

structure T = T
structure F = \<^eval>\<open>sfx_ParaT_nargs "Seq_Functor_Trans"\<close>(T)
open F
structure F = \<^eval>\<open>sfx_ParaT_nargs "Seq_Foldable_Trans"\<close>(T)
open F
structure F = \<^eval>\<open>sfx_ParaT_nargs "Seq_Foldable_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)

structure A = \<^eval>\<open>sfx_ParaT_nargs "Applicative"\<close>(T.A)
(*WARNING: traverse is not lazy*)
fun traverse f = T.traverse (fn sq => F.foldr (A.liftA2 Seq.cons o f) sq (A.pure Seq.empty))
end

(*note: monad transformer for seq cannot lazily be implemented (it requires traverse) and hence only
the standard monad instance is given.*)
structure \<^eval>\<open>sfx_ParaT_nargs "Seq_Monad"\<close> : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close> =
struct

structure F = \<^eval>\<open>sfx_ParaT_nargs "Seq_Functor_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>)
open F

val pure = Seq.single

fun f <*> x = Seq.maps (fn f => map f x) f
fun bind x f = Seq.maps f x
end

functor \<^eval>\<open>sfx_ParaT_nargs "Option_Functor_Trans"\<close>(F : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_TRANS"\<close> =
struct

structure F = F

type (@{ParaT_args} 'a) t = (@{ParaT_args} 'a option) F.t
fun lift x = F.map SOME x
fun map f = F.map (Option.map f)

end

functor \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Trans"\<close>(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "MONAD_TRANS"\<close> =
struct

structure M = M
structure F = \<^eval>\<open>sfx_ParaT_nargs "Option_Functor_Trans"\<close>(M)
open F

fun pure x = M.pure (SOME x)
fun f <*> x = M.bind f (fn NONE => M.pure NONE | SOME f => map f x)
fun bind x f = M.bind x (fn NONE => M.pure NONE | SOME x => f x)

end

functor \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Or_Trans"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "MONAD_OR_BASE"\<close> =
struct

structure OM = \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Trans"\<close>(M)
open OM

fun zero _ = M.pure NONE
fun or_lazy x fy = OM.M.bind x (fn NONE => fy () | _ => x)

end

functor \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Exception_Trans_Exception"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
  )
  : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    where type @{ParaT_args encl: "(" ")"} exn = @{ParaT_args encl: "(" ")"} M.exn =
struct

structure OM = \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Trans"\<close>(M)
type @{ParaT_args encl: "(" ")"} exn = @{ParaT_args encl: "(" ")"} M.exn

fun throw e = e |> OM.lift o M.throw
fun catch m f = M.catch m f
open OM

end

functor \<^eval>\<open>sfx_ParaT_nargs "Option_Foldable_Trans"\<close>(
    F : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_BASE"\<close> =
struct

type (@{ParaT_args} 'a) f = (@{ParaT_args} 'a option) F.f

fun fold_base _ NONE = I
  | fold_base f (SOME x) = f x
fun foldl f = F.foldl (fold_base f)
fun foldr f = F.foldr (fold_base f)

end

functor \<^eval>\<open>sfx_ParaT_nargs "Option_Traversable_Trans"\<close>(
    T : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_TRANS"\<close> =
struct

structure T = T
structure F = \<^eval>\<open>sfx_ParaT_nargs "Option_Functor_Trans"\<close>(T)
open F
structure F = \<^eval>\<open>sfx_ParaT_nargs "Option_Foldable_Trans"\<close>(T)
open F

structure A = \<^eval>\<open>sfx_ParaT_nargs "Applicative"\<close>(T.A)
fun traverse f = T.traverse (fn NONE => A.pure NONE | SOME x => A.map SOME (f x))

end

functor \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_Monad_Or"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_OR_BASE"\<close>
  ) :
    \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    where type @{ParaT_args encl: "(" ")"} exn = unit =
struct

open M
type @{ParaT_args encl: "(" ")"} exn = unit

val throw = zero
val catch = or_lazy

end

(* adapted from Haskell's free package https://hackage.haskell.org/package/free *)
functor \<^eval>\<open>sfx_ParaT_nargs "Free_Monad_Trans"\<close>(
    structure F : \<^eval>\<open>sfx_ParaT_nargs "FUNCTOR_BASE"\<close>
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "MONAD_TRANS"\<close> =
struct

structure M = M

datatype (@{ParaT_args} 'a, 'b) freef = Pure of 'a | Free of (@{ParaT_args} 'b) F.t
datatype (@{ParaT_args} 'a) freet = FreeT of (@{ParaT_args} (@{ParaT_args} 'a, (@{ParaT_args} 'a) freet) freef) M.t

fun runFreeT (FreeT m) = m

type (@{ParaT_args} 'a) t = (@{ParaT_args} 'a) freet

fun lift x = FreeT (M.map Pure x)

fun map f (FreeT m) =
  let fun f' (Pure x) = Pure (f x)
        | f' (Free xs) = Free (F.map (map f) xs)
  in FreeT (M.map f' m) end

fun pure a = FreeT (M.pure (Pure a))

fun bind (FreeT m) f = FreeT (M.bind m (fn Pure a => runFreeT (f a)
  | Free ms => M.pure (Free (F.map (fn m => bind m f) ms))))
fun m1 <*> m2 = bind m1 (fn f => bind m2 (fn x => pure (f x)))

end

