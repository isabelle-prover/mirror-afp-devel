(*  Title:      Zippy/modify_structured_lens.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Container"\<close>(
    structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    type @{AllT_args} ncontainer
    val ncontainer : (@{ParaT_args} @{AllT_args} L.container, @{AllT_args} ncontainer) L.C.morph
    val dest_ncontainer : (@{ParaT_args} @{AllT_args} ncontainer, @{AllT_args} L.container) L.C.morph
  )
  : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ncontainer
    where type @{AllT_args} data = @{AllT_args} L.data
  =
struct
open L
type @{AllT_args} container = @{AllT_args} ncontainer

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(C)
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(K.M)
  open SC A
in
fun getter x = x |> (dest_ncontainer >>> L.getter)
fun modifier x = x |> (second dest_ncontainer >>> L.modifier >>> ncontainer)
fun lens _ = L.mk_lens getter modifier
end

end

functor \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Data"\<close>(
    structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    type @{AllT_args} ndata
    val ndata : (@{ParaT_args} @{AllT_args} L.data, @{AllT_args} ndata) L.C.morph
    val dest_ndata : (@{ParaT_args} @{AllT_args} ndata, @{AllT_args} L.data) L.C.morph
  )
  : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} L.container
    where type @{AllT_args} data = @{AllT_args} ndata
  =
struct
open L
type @{AllT_args} data = @{AllT_args} ndata

fun lens _ = L.comp (L.lens_get_mk ndata dest_ndata) (L.lens ())
fun getter x = L.get (lens ()) x
fun modifier x = L.modify (lens ()) x
end

functor \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Container_Data"\<close>(
    structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    type @{AllT_args} ncontainer
    val ncontainer : (@{ParaT_args} @{AllT_args} L.container, @{AllT_args} ncontainer) L.C.morph
    val dest_ncontainer : (@{ParaT_args} @{AllT_args} ncontainer, @{AllT_args} L.container) L.C.morph
    type @{AllT_args} ndata
    val ndata : (@{ParaT_args} @{AllT_args} L.data, @{AllT_args} ndata) L.C.morph
    val dest_ndata : (@{ParaT_args} @{AllT_args} ndata, @{AllT_args} L.data) L.C.morph
  )
  : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} ncontainer
    where type @{AllT_args} data = @{AllT_args} ndata
  =
\<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Data"\<close>(
  type @{AllT_args} ndata = @{AllT_args} ndata
  val ndata = ndata
  val dest_ndata = dest_ndata
  structure L = \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Container"\<close>(
    type @{AllT_args} ncontainer = @{AllT_args} ncontainer
    val ncontainer = ncontainer
    val dest_ncontainer = dest_ncontainer
    structure L = L
))
