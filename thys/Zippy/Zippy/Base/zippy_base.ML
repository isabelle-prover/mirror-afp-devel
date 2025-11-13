(*  Title:      Zippy/zippy_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_BASE =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_BASE_BASE

  (* misc *)
  structure LT : \<^eval>\<open>sfx_ParaT_nargs "TRAVERSABLE_BASE"\<close>
  where type (@{ParaT_args} 'a) t = 'a list
  sharing type LT.A.t = M.t
  structure LF : \<^eval>\<open>sfx_ParaT_nargs "FOLDABLE_MONAD"\<close>
  where type (@{ParaT_args} 'a) f = 'a list
  sharing type LF.M.t = M.t

  (* updates *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val update_zipper{i}: ((@{ParaT_args} @{AllT_args} Z{i}.zipper) emorph) list ->
    (@{ParaT_args} @{AllT_args} Z{i}.zipper) emorph\<close>\<close>
end

functor Zippy_Base(
    structure Z : ZIPPY_BASE_BASE
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Z.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Show{i} : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show{i}.t = Z.Z{i}.zipper\<close>\<close>
  ) : ZIPPY_BASE =
struct
open Log Z
structure MU = Zippy_Monad_Util(M); open MU
structure AZU = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Util"\<close>(
  structure Z = Z; structure AE = Exn.AE); open AZU

(* misc *)
structure LT = \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(M))
structure LF = \<^eval>\<open>sfx_ParaT_nargs "Foldable_Monad"\<close>(
  structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)
  structure M = M)

(* updates *)
local open SC Mo A
in
\<^imap>\<open>\<open>{i}\<close> => \<open>
fun update_zipper{i} updates z = Ctxt.get_ctxt () >>= (fn ctxt => if null updates
  then (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Skipping empty updates for zipper{i}",
      Show{i}.pretty ctxt z
    ] |> Pretty.block |> Pretty.string_of);
    pure z)
  else (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Updating zipper{i}",
      Show{i}.pretty ctxt z
    ] |> Pretty.block |> Pretty.string_of);
    LF.foldlM I updates z))
\<close>\<close>
end
end
