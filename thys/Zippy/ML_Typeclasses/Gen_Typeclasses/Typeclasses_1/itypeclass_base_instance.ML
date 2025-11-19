(*  Title:  itypeclass_base_instance.ML
    Author: Kevin Kappelmann

Instances of basic indexed typeclasses.
*)
functor \<^eval>\<open>sfx_ParaT_nargs "IMonad_Exception_IMonad_Or"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "IMONAD_OR_BASE"\<close>
  ) :
    \<^eval>\<open>sfx_ParaT_nargs "IMONAD_EXCEPTION_BASE"\<close>
    where type @{ParaT_args encl: "(" ")"} exn = unit =
struct
open M
type @{ParaT_args encl: "(" ")"} exn = unit

val throw = zero
val catch = or_lazy
end
