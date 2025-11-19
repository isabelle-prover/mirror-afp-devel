(*  Title:      Zippy/morph.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} dep
  type @{AllT_args} from
  type @{AllT_args} to
  val morph : @{AllT_args} dep -> (@{ParaT_args} @{AllT_args} from, @{AllT_args} to) morph
end

(*endo morphism*)
signature \<^eval>\<open>sfx_T_nargs "DEP_EMORPH"\<close> =
sig
  include \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
  sharing type from = to
end

functor \<^eval>\<open>sfx_T_nargs "Dep_EMorph"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} dep
    type @{AllT_args} data
    val morph : @{AllT_args} dep -> (@{ParaT_args} @{AllT_args} data) M.emorph
  ) : \<^eval>\<open>sfx_T_nargs "DEP_EMORPH"\<close> =
struct
open M
type @{AllT_args} dep = @{AllT_args} dep
type @{AllT_args} from = @{AllT_args} data
type @{AllT_args} to = @{AllT_args} data
val morph = morph
end

signature \<^eval>\<open>sfx_T_nargs "MORPH"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} from
  type @{AllT_args} to
  val morph : (@{ParaT_args} @{AllT_args} from, @{AllT_args} to) morph
end

(*endomorphism*)
signature \<^eval>\<open>sfx_T_nargs "EMORPH"\<close> =
sig
  include \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type from = to
end

functor \<^eval>\<open>sfx_T_nargs "EMorph"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} data
    val morph : (@{ParaT_args} @{AllT_args} data) M.emorph
  ) : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close> =
struct
open M
type @{AllT_args} from = @{AllT_args} data
type @{AllT_args} to = @{AllT_args} data
val morph = morph
end

functor \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
    structure M : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    type @{AllT_args} dep
  ) :
    \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
    where type @{AllT_args} dep = @{AllT_args} dep =
struct
structure MIn = M; open M
type @{AllT_args} dep = @{AllT_args} dep
fun morph _ = MIn.morph
end

functor \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(
    M : \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
    where type @{AllT_args} dep = unit
  ) : \<^eval>\<open>sfx_T_nargs "MORPH"\<close> =
struct
structure MIn = M; open M
fun morph x = MIn.morph () x
end
