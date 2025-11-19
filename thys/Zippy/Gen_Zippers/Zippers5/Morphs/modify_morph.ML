(*  Title:      Zippy/modify_morph.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Morph_From"\<close>(
    structure M : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    type @{AllT_args} nfrom
    val dest_nfrom : (@{ParaT_args} @{AllT_args} nfrom, @{AllT_args} M.from) M.morph
  ) :
    \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    where type @{AllT_args} from = @{AllT_args} nfrom
    where type @{AllT_args} to = @{AllT_args} M.to
  =
struct
structure Min = M
open M
type @{AllT_args} from = @{AllT_args} nfrom
fun morph x = x |> Min.K.comp Min.morph dest_nfrom
end

functor \<^eval>\<open>sfx_T_nargs "Modify_Morph_To"\<close>(
    structure M : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    type @{AllT_args} nto
    val nto : (@{ParaT_args} @{AllT_args} M.to, @{AllT_args} nto) M.morph
  ) :
    \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    where type @{AllT_args} from = @{AllT_args} M.from
    where type @{AllT_args} to = @{AllT_args} nto
  =
struct
structure Min = M
open M
type @{AllT_args} to = @{AllT_args} nto
fun morph x = x |> Min.K.comp nto Min.morph
end

functor \<^eval>\<open>sfx_T_nargs "Modify_Morph_From_To"\<close>(
    structure M : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    type @{AllT_args} nfrom
    val dest_nfrom : (@{ParaT_args} @{AllT_args} nfrom, @{AllT_args} M.from) M.morph
    type @{AllT_args} nto
    val nto : (@{ParaT_args} @{AllT_args} M.to, @{AllT_args} nto) M.morph
  ) :
    \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    where type @{AllT_args} from = @{AllT_args} nfrom
    where type @{AllT_args} to = @{AllT_args} nto
  =
\<^eval>\<open>sfx_T_nargs "Modify_Morph_To"\<close>(
  type @{AllT_args} nto = @{AllT_args} nto
  val nto = nto
  structure M = \<^eval>\<open>sfx_T_nargs "Modify_Morph_From"\<close>(
    type @{AllT_args} nfrom = @{AllT_args} nfrom
    val dest_nfrom = dest_nfrom
    structure M = M
))
