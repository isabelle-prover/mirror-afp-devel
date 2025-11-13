(*  Title:  state.ML
    Author: Kevin Kappelmann

State monads adapted from Haskells mtl package.
*)
signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE_BASE"\<close> =
sig
  structure SR : STATE_RESULT_BASE
  type s
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  val state : (s -> (s, 'a) SR.result) -> (@{ParaT_args} 'a) t
  val get : unit -> (@{ParaT_args} s) t
  val put : s -> (@{ParaT_args} unit) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE_BASE"\<close>
  val map_state : (s -> s) -> (@{ParaT_args} 'a) t -> (@{ParaT_args} 'a) t
  val map_result : ('a -> s -> (s, 'b) SR.result) -> (@{ParaT_args} 'a) t -> (@{ParaT_args} 'b) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Monad_State"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE"\<close> =
struct
open M
structure SR = State_Result(SR)
fun map_base f st = M.bind st (M.state o f)
fun map_state f = map_base (fn x => fn s => SR.result (f s) x)
fun map_result f = map_base f
end

signature \<^eval>\<open>sfx_ParaT_nargs "STATE_TRANS"\<close> =
sig
  structure SR : STATE_RESULT_BASE

  type (@{ParaT_args} 'a) mt
  type s
  type (@{ParaT_args} 'a) state = s -> (@{ParaT_args} (s, 'a) SR.result) mt

  include \<^eval>\<open>sfx_ParaT_nargs "MONAD_TRANS"\<close>
  where type (@{ParaT_args} 'a) t = (@{ParaT_args} 'a) state
  sharing type M.t = mt

  (*MONAD_STATE_BASE*)
  val state : (s -> (s, 'a) SR.result) -> (@{ParaT_args} 'a) state
  val get : unit -> (@{ParaT_args} s) state
  val put : s -> (@{ParaT_args} unit) state

  val run : s -> (@{ParaT_args} 'a) state -> (@{ParaT_args} (s, 'a) SR.result) M.t
  val eval : s -> (@{ParaT_args} 'a) state -> (@{ParaT_args} 'a) M.t
  val exec : s -> (@{ParaT_args} 'a) state -> (@{ParaT_args} s) M.t
end

functor \<^eval>\<open>sfx_ParaT_nargs "State_Trans"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
    structure SR : STATE_RESULT_BASE
    type s
  ) : \<^eval>\<open>sfx_ParaT_nargs "STATE_TRANS"\<close> =
struct

type (@{ParaT_args} 'a) mt = (@{ParaT_args} 'a) M.t
type (@{ParaT_args} 'a) state = s -> (@{ParaT_args} (s, 'a) SR.result) mt

structure MT : \<^eval>\<open>sfx_ParaT_nargs "MONAD_TRANS"\<close> =
struct
structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M) open M
type (@{ParaT_args} 'a) t = (@{ParaT_args} 'a) state

fun lift x s = x >>= (SR.result s #> M.pure)

structure SR = State_Result(SR)
fun map f st = M.map (SR.map_value f) o st
fun pure x = M.pure o (fn s => SR.result s x)
fun stf <*> stx = (fn s => stf s
  >>= (fn r => stx (SR.state r)
  >>= (fn r' => SR.result (SR.state r') (SR.value r (SR.value r')) |> M.pure)))
fun bind st f_st = (fn s => st s >>= (fn r => (f_st (SR.value r)) (SR.state r)))
end
open MT

structure MS : \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE_BASE"\<close> =
struct
open MT
structure SR = SR
type s = s
fun state fs = M.pure o fs
fun get () = state (fn s => SR.result s s)
fun put s = state (fn _ => SR.result s ())
end
open MS

fun run s st = st s
fun eval s = run s #> M.map SR.value
fun exec s = run s #> M.map SR.state

end

functor \<^eval>\<open>sfx_ParaT_nargs "Monad_Zero_State_Trans"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_ZERO_BASE"\<close>
    structure S : \<^eval>\<open>sfx_ParaT_nargs "STATE_TRANS"\<close>
    sharing type S.M.t = M.t
  ) :
    \<^eval>\<open>sfx_ParaT_nargs "MONAD_ZERO_BASE"\<close>
    where type (@{ParaT_args} 'a) t = (@{ParaT_args} 'a) S.t
  =
struct
fun zero _ = S.lift (M.zero ())
open S
end

functor \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_State_Trans"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    structure S : \<^eval>\<open>sfx_ParaT_nargs "STATE_TRANS"\<close>
    sharing type S.M.t = M.t
  ) :
    \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    where type (@{ParaT_args} 'a) t = (@{ParaT_args} 'a) S.t
  =
struct
open M
fun throw e = S.lift (M.throw e)
fun catch m f s = M.catch (m s) (fn e => f e s)
open S
end

functor \<^eval>\<open>sfx_ParaT_nargs "Monad_State_State_Trans"\<close>(A :
  sig
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE_BASE"\<close>
    structure S : \<^eval>\<open>sfx_ParaT_nargs "STATE_TRANS"\<close>
    sharing type S.M.t = M.t
  end
  ) :
    \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE_BASE"\<close>
    where type (@{ParaT_args} 'a) t = (@{ParaT_args} 'a) A.S.t
  =
struct
open A A.M
open S
structure SR = A.M.SR
type s = A.M.s
fun state fs = S.lift (A.M.state fs)
fun get _ = S.lift (A.M.get ())
fun put s = S.lift (A.M.put s)
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_STATE_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close>
  type s
  val get : unit -> (@{ParaT_args} 'a, s) morph
  val put : unit -> (@{ParaT_args} s, unit) morph
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_STATE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_STATE_BASE"\<close>
  val change : (@{ParaT_args} 'a * s, s) morph -> (@{ParaT_args} 'a) emorph
  val access : (@{ParaT_args} 'a * s, 'b) morph -> (@{ParaT_args} 'a, 'b) morph
end

functor \<^eval>\<open>sfx_ParaT_nargs "Arrow_State"\<close>(
    structure AS : \<^eval>\<open>sfx_ParaT_nargs "ARROW_STATE_BASE"\<close>
    structure A : \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close>
    sharing type A.morph = AS.morph
  ) : \<^eval>\<open>sfx_ParaT_nargs "ARROW_STATE"\<close> =
struct
open AS
open A

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A) open SC
in
fun get_state _ = id () &&& get ()
fun access f = get_state () >>> f
fun change f = access f &&& id ()
  >>> first (put ())
  >>> arr snd
end
end

signature \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_STATE"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_STATE"\<close>
  where type (@{ParaT_args} 'a, 'b) morph = (@{ParaT_args} 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_State"\<close>(
    MS : \<^eval>\<open>sfx_ParaT_nargs "MONAD_STATE_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_STATE"\<close> =
struct
structure KA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply_Base"\<close>(MS)
open KA
type s = MS.s
local structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(MS) open M
in
fun get _ _ = MS.get ()
fun put _ x = MS.put x
fun access f x = get () x >>= (pair x #> f)
fun change f x = access f x >>= put () >>= arr (fn _ => x)
end
end

